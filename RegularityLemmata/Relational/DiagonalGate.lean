/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrongCounting
import RegularityLemmata.Partition.Equitable

/-!
# Phase 10 unit 8: the diagonal gate

The strong-counting summit (`Relational/BinaryStrongCounting.lean`) compares the **transversal**
induced count — copies whose three vertices land in three *distinct* coarse cells — against the
coarse step estimate. This file closes the remaining gap to the **global** induced count, which
also counts copies with two vertices in the same cell.

The global count is the sum of the box counts over *all* ordered cell-triples; it decomposes
exactly into the transversal part and a nontransversal part (`Function.Injective` vs not). For a
`Fin 3` index, non-injectivity is exactly one of the three coordinate collisions
`T 0 = T 1`, `T 0 = T 2`, `T 1 = T 2`, and each collision event contributes at most `m·|s|²`
box volume when every coarse cell has cardinality at most `m` — hence a `3·m·|s|²` nontransversal
bound, with the factor `3` counting the collision events.

Part-size bounds are inherited under refinement (a finer cell sits inside a coarse cell), so an
initial equipartition supplies `m = |s| / #parts + 1` for the witness's coarse partition. The
global strong-counting corollary adds the `3·m·|s|²` diagonal charge to the summit bound.

This file is independent of `AtMostBinary` until the final combination with the strong-counting
summit; the factor `3` is derived, not assumed.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-! ### All-cell and nontransversal cell triples -/

/-- Ordered triples of cells of `Q` with a repeated cell (the complement of the transversal
triples inside all ordered cell-triples). -/
def nontransversalCellTriples (Q : Finpartition s) : Finset (Fin 3 → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter (fun T => ¬ Function.Injective T)

/-- The total induced count: the number of induced pattern embeddings, summed over *all* ordered
cell-triples (each embedding's image meets a unique cell-triple, transversal or not). -/
def globalInducedCount (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℕ :=
  ∑ T ∈ Fintype.piFinset fun _ => Q.parts, inducedEmbeddingCountOn P M T

variable {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {Q : Finpartition s}

/-! ### Exact global-count decomposition -/

/-- **Global = transversal + nontransversal.** -/
theorem globalInducedCount_eq_transversal_add_nontransversal :
    globalInducedCount P M Q
      = transversalInducedCount P M Q
        + ∑ T ∈ nontransversalCellTriples Q, inducedEmbeddingCountOn P M T := by
  rw [globalInducedCount, transversalInducedCount, transversalCellTriples,
    nontransversalCellTriples]
  exact (Finset.sum_filter_add_sum_filter_not (Fintype.piFinset fun _ => Q.parts)
    Function.Injective _).symm

/-- **The full box is the disjoint union of the cell boxes.** Every vertex of `s` lies in a unique
cell, so a function into `s` lands in a unique cell-triple box. -/
theorem piFinset_const_eq_biUnion_cellTriples (Q : Finpartition s) :
    Fintype.piFinset (fun _ : Fin 3 => s)
      = (Fintype.piFinset fun _ : Fin 3 => Q.parts).biUnion Fintype.piFinset := by
  ext f
  rw [Fintype.mem_piFinset, Finset.mem_biUnion]
  constructor
  · intro hf
    choose C hC using fun i => (Q.existsUnique_mem (hf i)).exists
    exact ⟨C, Fintype.mem_piFinset.mpr fun i => (hC i).1,
      Fintype.mem_piFinset.mpr fun i => (hC i).2⟩
  · rintro ⟨T, hT, hfT⟩
    rw [Fintype.mem_piFinset] at hT hfT
    exact fun i => Finset.mem_of_subset (Q.le (hT i)) (hfT i)

/-- The cell boxes over distinct cell-triples are pairwise disjoint. -/
theorem piFinset_pairwiseDisjoint_cellTriples (Q : Finpartition s) :
    (↑(Fintype.piFinset fun _ : Fin 3 => Q.parts) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      Fintype.piFinset := by
  intro T hT T' hT' hTT'
  rw [Finset.mem_coe, Fintype.mem_piFinset] at hT hT'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro f hfT hfT'
  rw [Fintype.mem_piFinset] at hfT hfT'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hTT'
  exact Finset.disjoint_left.mp
    (Q.disjoint (Finset.mem_coe.mpr (hT i)) (Finset.mem_coe.mpr (hT' i)) hi) (hfT i) (hfT' i)

/-- **The global count is the library's actual induced-embedding count over the full box.** The
partition-cell sum equals `inducedEmbeddingCountOn` on `fun _ => s`. -/
theorem globalInducedCount_eq_inducedEmbeddingCountOn :
    globalInducedCount P M Q = inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) := by
  rw [inducedEmbeddingCountOn, piFinset_const_eq_biUnion_cellTriples Q, Finset.filter_biUnion,
    Finset.card_biUnion fun T hT T' hT' hTT' =>
      (piFinset_pairwiseDisjoint_cellTriples Q (Finset.mem_coe.mpr hT)
        (Finset.mem_coe.mpr hT') hTT').mono (Finset.filter_subset _ _) (Finset.filter_subset _ _),
    globalInducedCount]
  exact Finset.sum_congr rfl fun T _ => rfl

/-- **Partition-independence of the global count**: it does not depend on the cell partition (both
sides equal the actual count over the full box). -/
theorem globalInducedCount_eq_globalInducedCount (Q Q' : Finpartition s) :
    globalInducedCount P M Q = globalInducedCount P M Q' :=
  (globalInducedCount_eq_inducedEmbeddingCountOn (Q := Q)).trans
    (globalInducedCount_eq_inducedEmbeddingCountOn (Q := Q')).symm

/-- **Full-carrier bridge to the Phase 8 counting API.** On a finite carrier partitioned as
`Finpartition univ`, the global count is exactly the diagonal-sensitive `inducedEmbeddingCount`. -/
theorem globalInducedCount_eq_inducedEmbeddingCount [Fintype V]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (Q : Finpartition (Finset.univ : Finset V)) :
    globalInducedCount P M Q = inducedEmbeddingCount P M := by
  rw [globalInducedCount_eq_inducedEmbeddingCountOn, inducedEmbeddingCountOn, inducedEmbeddingCount,
    Fintype.piFinset_univ]

/-! ### `Fin 3` collision characterization -/

/-- A `Fin 3`-indexed triple fails to be injective exactly when two coordinates collide. -/
theorem not_injective_fin_three {α : Type*} {T : Fin 3 → α} :
    ¬ Function.Injective T ↔ T 0 = T 1 ∨ T 0 = T 2 ∨ T 1 = T 2 := by
  rw [Function.not_injective_iff]
  constructor
  · rintro ⟨a, b, hab, hne⟩
    fin_cases a <;> fin_cases b <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0, 1, h, by decide⟩
    · exact ⟨0, 2, h, by decide⟩
    · exact ⟨1, 2, h, by decide⟩

/-! ### The `3·m·|s|²` nontransversal bound -/

/-- The doubled-cell squared mass is at most `m·|s|²` when cells have size at most `m`. -/
private theorem sum_sq_mul_card_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ p ∈ Q.parts ×ˢ Q.parts, ((p.1.card : ℝ) * p.1.card * p.2.card) ≤ m * (s.card : ℝ) ^ 2 := by
  rw [Finset.sum_product]
  have hstep : ∑ C ∈ Q.parts, ∑ D ∈ Q.parts, ((C.card : ℝ) * C.card * D.card)
      = (∑ C ∈ Q.parts, (C.card : ℝ) * C.card) * s.card := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun C _ => by rw [← Finset.mul_sum, sum_card_parts_cast]
  rw [hstep]
  have hsq : ∑ C ∈ Q.parts, (C.card : ℝ) * C.card ≤ (m : ℝ) * s.card := by
    calc ∑ C ∈ Q.parts, (C.card : ℝ) * C.card
        ≤ ∑ C ∈ Q.parts, (m : ℝ) * C.card :=
          Finset.sum_le_sum fun C hC =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast hm C hC) (Nat.cast_nonneg _)
      _ = (m : ℝ) * s.card := by rw [← Finset.mul_sum, sum_card_parts_cast]
  calc (∑ C ∈ Q.parts, (C.card : ℝ) * C.card) * s.card
      ≤ ((m : ℝ) * s.card) * s.card := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)
    _ = m * (s.card : ℝ) ^ 2 := by ring

/-- The `(0,1)` collision event has box volume at most `m·|s|²`. -/
private theorem sum_collision_zero_one_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 1),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ m * (s.card : ℝ) ^ 2 := by
  have hre : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 1),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ p ∈ Q.parts ×ˢ Q.parts, ((p.1.card : ℝ) * p.1.card * p.2.card) := by
    refine Finset.sum_nbij' (fun T => (T 0, T 2)) (fun p => ![p.1, p.1, p.2])
      (fun T hT => ?_) (fun p hp => ?_) (fun T hT => ?_) (fun p _ => ?_) (fun T hT => ?_)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.1 0, hT.1 2⟩
    · rw [Finset.mem_product] at hp
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i => by fin_cases i <;> [exact hp.1; exact hp.1; exact hp.2], rfl⟩
    · funext i; fin_cases i <;> [rfl; exact (Finset.mem_filter.mp hT).2; rfl]
    · rfl
    · rw [(Finset.mem_filter.mp hT).2]
  rw [hre]; exact sum_sq_mul_card_le hm

/-- The `(0,2)` collision event has box volume at most `m·|s|²`. -/
private theorem sum_collision_zero_two_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 2),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ m * (s.card : ℝ) ^ 2 := by
  have hre : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 2),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ p ∈ Q.parts ×ˢ Q.parts, ((p.1.card : ℝ) * p.1.card * p.2.card) := by
    refine Finset.sum_nbij' (fun T => (T 0, T 1)) (fun p => ![p.1, p.2, p.1])
      (fun T hT => ?_) (fun p hp => ?_) (fun T hT => ?_) (fun p _ => ?_) (fun T hT => ?_)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.1 0, hT.1 1⟩
    · rw [Finset.mem_product] at hp
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i => by fin_cases i <;> [exact hp.1; exact hp.2; exact hp.1], rfl⟩
    · funext i; fin_cases i <;> [rfl; rfl; exact (Finset.mem_filter.mp hT).2]
    · rfl
    · rw [(Finset.mem_filter.mp hT).2]; ring
  rw [hre]; exact sum_sq_mul_card_le hm

/-- The `(1,2)` collision event has box volume at most `m·|s|²`. -/
private theorem sum_collision_one_two_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 1 = T 2),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ m * (s.card : ℝ) ^ 2 := by
  have hre : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 1 = T 2),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ p ∈ Q.parts ×ˢ Q.parts, ((p.1.card : ℝ) * p.1.card * p.2.card) := by
    refine Finset.sum_nbij' (fun T => (T 1, T 0)) (fun p => ![p.2, p.1, p.1])
      (fun T hT => ?_) (fun p hp => ?_) (fun T hT => ?_) (fun p _ => ?_) (fun T hT => ?_)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.1 1, hT.1 0⟩
    · rw [Finset.mem_product] at hp
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun i => by fin_cases i <;> [exact hp.2; exact hp.1; exact hp.1], rfl⟩
    · funext i; fin_cases i <;> [rfl; rfl; exact (Finset.mem_filter.mp hT).2]
    · rfl
    · rw [(Finset.mem_filter.mp hT).2]; ring
  rw [hre]; exact sum_sq_mul_card_le hm

/-- **Derived diagonal bound.** When every cell of `Q` has cardinality at most `m`, the
nontransversal induced count is at most `3·m·|s|²` — three collision events, each `≤ m·|s|²`. -/
theorem sum_nontransversal_inducedEmbeddingCountOn_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ((∑ T ∈ nontransversalCellTriples Q, inducedEmbeddingCountOn P M T : ℕ) : ℝ)
      ≤ 3 * m * (s.card : ℝ) ^ 2 := by
  rw [Nat.cast_sum]
  have hpt : ∀ T : Fin 3 → Finset V,
      (if ¬ Function.Injective T then cellTripleVolume T else 0)
      ≤ (if T 0 = T 1 then cellTripleVolume T else 0)
        + (if T 0 = T 2 then cellTripleVolume T else 0)
        + (if T 1 = T 2 then cellTripleVolume T else 0) := by
    intro T
    have hv : 0 ≤ cellTripleVolume T := cellTripleVolume_nonneg T
    have e01 : 0 ≤ (if T 0 = T 1 then cellTripleVolume T else 0) := by
      split_ifs <;> [exact hv; exact le_rfl]
    have e02 : 0 ≤ (if T 0 = T 2 then cellTripleVolume T else 0) := by
      split_ifs <;> [exact hv; exact le_rfl]
    have e12 : 0 ≤ (if T 1 = T 2 then cellTripleVolume T else 0) := by
      split_ifs <;> [exact hv; exact le_rfl]
    by_cases h : Function.Injective T
    · rw [if_neg (not_not.mpr h)]; linarith
    · rw [if_pos h, not_injective_fin_three] at *
      rcases h with h01 | h02 | h12
      · rw [if_pos h01]; linarith
      · rw [if_pos h02]; linarith
      · rw [if_pos h12]; linarith
  calc ∑ T ∈ nontransversalCellTriples Q, (inducedEmbeddingCountOn P M T : ℝ)
      ≤ ∑ T ∈ nontransversalCellTriples Q, cellTripleVolume T :=
        Finset.sum_le_sum fun T _ => inducedEmbeddingCountOn_le_cellTripleVolume P M T
    _ = ∑ T ∈ Fintype.piFinset fun _ : Fin 3 => Q.parts,
          (if ¬ Function.Injective T then cellTripleVolume T else 0) := by
        rw [nontransversalCellTriples, Finset.sum_filter]
    _ ≤ ∑ T ∈ Fintype.piFinset fun _ : Fin 3 => Q.parts,
          ((if T 0 = T 1 then cellTripleVolume T else 0)
            + (if T 0 = T 2 then cellTripleVolume T else 0)
            + (if T 1 = T 2 then cellTripleVolume T else 0)) :=
        Finset.sum_le_sum fun T _ => hpt T
    _ = (∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 1),
            cellTripleVolume T)
          + (∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 0 = T 2),
              cellTripleVolume T)
          + (∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => T 1 = T 2),
              cellTripleVolume T) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
          Finset.sum_filter]
    _ ≤ m * (s.card : ℝ) ^ 2 + m * (s.card : ℝ) ^ 2 + m * (s.card : ℝ) ^ 2 := by
        simp only [cellTripleVolume]
        exact add_le_add (add_le_add (sum_collision_zero_one_le hm) (sum_collision_zero_two_le hm))
          (sum_collision_one_two_le hm)
    _ = 3 * m * (s.card : ℝ) ^ 2 := by ring

/-! ### The global strong-counting corollary -/

/-- **Global strong three-vertex counting.** Adding the diagonal charge to the summit: for a
binary-palette strong witness whose coarse cells all have cardinality at most `m`, the actual
number of induced pattern embeddings on the whole carrier (`inducedEmbeddingCountOn` over the full
box `fun _ => s`) is within `(10·τ + 3·η + 3·δ/η²)·|s|³ + 3·m·|s|²` of the coarse step estimate. -/
theorem BinaryPaletteStrongWitness.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η)
    {m : ℕ} (hm : ∀ C ∈ w.coarse.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
        + 3 * m * (s.card : ℝ) ^ 2 := by
  rw [← globalInducedCount_eq_inducedEmbeddingCountOn (Q := w.coarse)]
  have hsummit := w.abs_transversalInducedCount_sub_coarseInducedEstimate_le P hnull hτ1 hη
  have hdiag : |(globalInducedCount P M w.coarse : ℝ) - (transversalInducedCount P M w.coarse : ℝ)|
      ≤ 3 * m * (s.card : ℝ) ^ 2 := by
    have hcast : (globalInducedCount P M w.coarse : ℝ) - (transversalInducedCount P M w.coarse : ℝ)
        = ((∑ T ∈ nontransversalCellTriples w.coarse, inducedEmbeddingCountOn P M T : ℕ) : ℝ) := by
      rw [globalInducedCount_eq_transversal_add_nontransversal]; push_cast; ring
    rw [hcast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact sum_nontransversal_inducedEmbeddingCountOn_le hm
  calc |(globalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ |(globalInducedCount P M w.coarse : ℝ) - (transversalInducedCount P M w.coarse : ℝ)|
          + |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse| :=
        abs_sub_le _ _ _
    _ ≤ 3 * m * (s.card : ℝ) ^ 2
          + (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 :=
        add_le_add hdiag hsummit
    _ = (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
          + 3 * m * (s.card : ℝ) ^ 2 := by ring

/-- **Equipartition specialization.** When the witness's starting partition `P₀` is an
equipartition, its `|s| / #parts + 1` part-size bound is inherited by the coarse partition
(`part_card_le_of_refines`), supplying the diagonal charge without a separate cell-size
hypothesis. -/
theorem BinaryPaletteStrongWitness.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le_of_equipartition
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (hP₀ : P₀.IsEquipartition)
    (P : FiniteRelModel L (Fin 3)) (hnull : NullaryCompatible P M)
    (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
        + 3 * ((s.card / P₀.parts.card + 1 : ℕ) : ℝ) * (s.card : ℝ) ^ 2 :=
  w.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le P hnull hτ1 hη
    (part_card_le_of_refines w.coarse_le (forall_card_le_of_isEquipartition hP₀))

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

/-- The unique model of the empty language (no relations to interpret). -/
private def emptyModel (W : Type*) : FiniteRelModel FirstOrder.Language.empty W :=
  ⟨fun {_} R _ => R.elim⟩

-- **The gate controls actual embeddings: `3! = 6` on the empty language.** With the indiscrete
-- partition `⊤` (one cell) no ordered triple is transversal, yet the global count sees all `6`
-- injective self-maps of `Fin 3` — the whole count is diagonal (nontransversal).
example : globalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊤ : Finpartition (Finset.univ : Finset (Fin 3))) = 6 := by decide

example : transversalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊤ : Finpartition (Finset.univ : Finset (Fin 3))) = 0 := by decide

-- **Discrete partition `⊥`**: every vertex is its own cell, so all `6` injective maps land in
-- three distinct cells — global and transversal agree, with zero nontransversal contribution.
example : globalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) = 6 := by decide

example : transversalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) = 6 := by decide

example : (∑ T ∈ nontransversalCellTriples (⊥ : Finpartition (Finset.univ : Finset (Fin 3))),
    inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3)) T) = 0 := by decide

-- **Full-carrier bridge to the Phase 8 counting API.**
example : globalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))
    = inducedEmbeddingCount (emptyModel (Fin 3)) (emptyModel (Fin 3)) :=
  globalInducedCount_eq_inducedEmbeddingCount _

-- **Partition-independence of the global count**, concretely: `⊤` and `⊥` agree.
example : globalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))
    = globalInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) :=
  globalInducedCount_eq_globalInducedCount _ _

-- **Collision characterization is exhaustive.** On `Fin 3` non-injectivity is precisely one of
-- the three coordinate collisions.
example {α : Type*} (T : Fin 3 → α) :
    ¬ Function.Injective T ↔ T 0 = T 1 ∨ T 0 = T 2 ∨ T 1 = T 2 :=
  not_injective_fin_three

-- **Empty-host bridge**: over the empty host there are no cell-triples to charge.
example : nontransversalCellTriples (⊥ : Finpartition (∅ : Finset (Fin 0))) = ∅ := by decide

-- **Part-size inheritance is a refinement fact**, needing neither the language nor the model.
example {m : ℕ} {P₁ P₂ : Finpartition s} (hle : P₁ ≤ P₂) (hm : ∀ B ∈ P₂.parts, B.card ≤ m) :
    ∀ A ∈ P₁.parts, A.card ≤ m :=
  part_card_le_of_refines hle hm

-- **Equipartition supplies the cell bound**, statement-level.
example {P₁ : Finpartition s} (hP : P₁.IsEquipartition) :
    ∀ B ∈ P₁.parts, B.card ≤ s.card / P₁.parts.card + 1 :=
  forall_card_le_of_isEquipartition hP

end Tests

end RegularityLemmata
