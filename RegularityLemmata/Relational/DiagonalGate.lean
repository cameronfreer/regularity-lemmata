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

/-! ### Part-size inheritance and equipartition specialization -/

/-- **Part-size inheritance under refinement.** If `Q` refines `P` and every cell of `P` has
cardinality at most `m`, then so does every cell of `Q` (a finer cell sits inside a coarse one). -/
theorem card_le_of_le_of_forall_card_le {m : ℕ} {P₁ P₂ : Finpartition s} (hle : P₁ ≤ P₂)
    (hm : ∀ B ∈ P₂.parts, B.card ≤ m) : ∀ A ∈ P₁.parts, A.card ≤ m := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := hle hA
  exact le_trans (Finset.card_le_card hAB) (hm B hB)

/-- **Equipartition part-size bound.** Every cell of an equipartition has cardinality at most
`|s| / #parts + 1`. -/
theorem forall_card_le_of_isEquipartition {P₁ : Finpartition s} (hP : P₁.IsEquipartition) :
    ∀ B ∈ P₁.parts, B.card ≤ s.card / P₁.parts.card + 1 :=
  fun _ hB => hP.card_part_le_average_add_one hB

/-! ### The global strong-counting corollary -/

/-- **Global strong three-vertex counting.** Adding the diagonal charge to the summit: for a
binary-palette strong witness whose coarse cells all have cardinality at most `m`, the *global*
induced count is within `(10·τ + 3·η + 3·δ/η²)·|s|³ + 3·m·|s|²` of the coarse step estimate. -/
theorem BinaryPaletteStrongWitness.abs_globalInducedCount_sub_coarseInducedEstimate_le
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η)
    {m : ℕ} (hm : ∀ C ∈ w.coarse.parts, C.card ≤ m) :
    |(globalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
        + 3 * m * (s.card : ℝ) ^ 2 := by
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
equipartition, its `|s| / #parts + 1` part-size bound is inherited by the coarse partition,
supplying the diagonal charge without a separate cell-size hypothesis. -/
theorem BinaryPaletteStrongWitness.abs_globalInducedCount_sub_coarseInducedEstimate_le_of_equipartition
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (hP₀ : P₀.IsEquipartition)
    (P : FiniteRelModel L (Fin 3)) (hnull : NullaryCompatible P M)
    (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(globalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
        + 3 * ((s.card / P₀.parts.card + 1 : ℕ) : ℝ) * (s.card : ℝ) ^ 2 :=
  w.abs_globalInducedCount_sub_coarseInducedEstimate_le P hnull hτ1 hη
    (card_le_of_le_of_forall_card_le w.coarse_le (forall_card_le_of_isEquipartition hP₀))

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- **Empty host partition.** Over the empty host there are no cells, so *every* cell-triple set is
-- empty — in particular there are no nontransversal (diagonal) triples to charge.
example : nontransversalCellTriples (⊥ : Finpartition (∅ : Finset (Fin 0))) = ∅ := by decide

-- **Collision characterization is exhaustive.** On `Fin 3` non-injectivity is precisely one of
-- the three coordinate collisions.
example {α : Type*} (T : Fin 3 → α) :
    ¬ Function.Injective T ↔ T 0 = T 1 ∨ T 0 = T 2 ∨ T 1 = T 2 :=
  not_injective_fin_three

-- **Singleton host, one cell.** With a single cell no ordered triple has three distinct cells, so
-- the transversal set is empty; every cell-triple is a diagonal one (here exactly `![{0},{0},{0}]`).
example : transversalCellTriples (⊤ : Finpartition ({0} : Finset (Fin 1))) = ∅ := by decide

example : (nontransversalCellTriples (⊤ : Finpartition ({0} : Finset (Fin 1)))).card = 1 := by
  decide

-- **Part-size inheritance is a refinement fact**, needing neither the language nor the model.
example {m : ℕ} {P₁ P₂ : Finpartition s} (hle : P₁ ≤ P₂) (hm : ∀ B ∈ P₂.parts, B.card ≤ m) :
    ∀ A ∈ P₁.parts, A.card ≤ m :=
  card_le_of_le_of_forall_card_le hle hm

-- **Equipartition supplies the cell bound**, statement-level.
example {P₁ : Finpartition s} (hP : P₁.IsEquipartition) :
    ∀ B ∈ P₁.parts, B.card ≤ s.card / P₁.parts.card + 1 :=
  forall_card_le_of_isEquipartition hP

end Tests

end RegularityLemmata
