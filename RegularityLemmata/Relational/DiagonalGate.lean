/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrongCounting
import RegularityLemmata.Relational.Indivisible
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

The collision decomposition is **arity-generic**. For `k`-tuples of cells
(`nontransversalCellTuples`, volume `cellTupleVolume`), non-injectivity has some strictly ordered
collision `i < j` (`not_injective_iff_exists_lt_eq`), each of the `k.choose 2` collision events
contributes at most `m·|s|^(k−1)`, and the total nontransversal charge is
`(k.choose 2)·m·|s|^(k−1)`
(`sum_nontransversalCellTuples_weight_le`), guard-free in `k`. The `Fin 3` results are its
`k = 3` instances, with `3.choose 2 = 3`.

The same `i < j` family drives the **positional lift of the bad-pair mass**
(`badCellTuples`, `sum_badCellTuples_weight_le_mass`, `sum_badCellTuples_weight_le`): a cell
tuple with some coordinate-pair position in a bad pair set `D` is charged to that position, each
of the `k.choose 2` positions carries at most the `D`-pair mass times `|s|^(k−2)`, and a single
aggregated mass bound `≤ β·|s|²` yields `(k.choose 2)·β·|s|^k`. `badTripleVolume_le` is
recovered at `k = 3` by restricting to transversal tuples. The hypothesis is the one aggregated
bound; the `k.choose 2` is the lift, not a union bound over per-pair hypotheses.

The gate also settles the **quotient counting theorem** of the approximation-to-counting
interface: for `N` indivisible for `Q`, the `s`-restricted induced count of a `k`-vertex pattern
equals the quotient-weighted count `quotientInducedCount` (`Relational/Indivisible.lean`) on the
transversal cell tuples exactly, and the repeated-cell tuples contribute at most the diagonal
charge (`IsIndivisibleFor.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le`; full carrier
at `s = univ`). The box decomposition behind it is index-generic
(`inducedEmbeddingCountOn_eq_sum_cellTuples`).

Part-size bounds are inherited under refinement (a finer cell sits inside a coarse cell), so an
initial equipartition supplies `m = |s| / #parts + 1` for the witness's coarse partition. The
global strong-counting corollary adds the `3·m·|s|²` diagonal charge to the summit bound.

This file is independent of `AtMostBinary` until the final combination with the strong-counting
summit; the factor `3` is derived, not assumed.

The diagonal charge is proved for **weights** (`sum_nontransversal_weight_le`): it constrains any
real weight dominated by the cell-triple volume, so it serves the actual and the predicted side
alike. The induced count is one specialization
(`sum_nontransversal_inducedEmbeddingCountOn_le`); "volume times a factor `≤ 1`", the shape of
every step estimate, is another (`sum_nontransversal_volume_mul_le`).
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

/-! ### The box decomposition, index-generic -/

section BoxDecomposition

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **The full box is the disjoint union of the cell boxes.** Every vertex of `s` lies in a unique
cell, so a function into `s` lands in a unique cell-tuple box. Index-generic. -/
theorem piFinset_const_eq_biUnion_cellTuples (Q : Finpartition s) :
    Fintype.piFinset (fun _ : W => s)
      = (Fintype.piFinset fun _ : W => Q.parts).biUnion Fintype.piFinset := by
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

/-- The cell boxes over distinct cell tuples are pairwise disjoint. Index-generic. -/
theorem piFinset_pairwiseDisjoint_cellTuples (Q : Finpartition s) :
    (↑(Fintype.piFinset fun _ : W => Q.parts) : Set (W → Finset V)).PairwiseDisjoint
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

/-- **The `s`-restricted induced count is the sum of the box counts over all cell tuples.**
Index-generic; `globalInducedCount_eq_inducedEmbeddingCountOn` is the `Fin 3` reading. -/
theorem inducedEmbeddingCountOn_eq_sum_cellTuples (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    (Q : Finpartition s) :
    inducedEmbeddingCountOn P M (fun _ : W => s)
      = ∑ T ∈ Fintype.piFinset fun _ : W => Q.parts, inducedEmbeddingCountOn P M T := by
  rw [inducedEmbeddingCountOn, piFinset_const_eq_biUnion_cellTuples Q, Finset.filter_biUnion,
    Finset.card_biUnion fun T hT T' hT' hTT' =>
      (piFinset_pairwiseDisjoint_cellTuples Q (Finset.mem_coe.mpr hT)
        (Finset.mem_coe.mpr hT') hTT').mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)]
  exact Finset.sum_congr rfl fun T _ => rfl

/-- On a finite carrier, the count over the full box `fun _ ↦ univ` is `inducedEmbeddingCount`. -/
theorem inducedEmbeddingCountOn_univ [Fintype V] (P : FiniteRelModel L W) (M : FiniteRelModel L V) :
    inducedEmbeddingCountOn P M (fun _ : W => Finset.univ) = inducedEmbeddingCount P M := by
  rw [inducedEmbeddingCountOn, inducedEmbeddingCount, Fintype.piFinset_univ]

end BoxDecomposition

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

/-- **The full box is the disjoint union of the cell boxes**, `Fin 3` reading of
`piFinset_const_eq_biUnion_cellTuples`. -/
theorem piFinset_const_eq_biUnion_cellTriples (Q : Finpartition s) :
    Fintype.piFinset (fun _ : Fin 3 => s)
      = (Fintype.piFinset fun _ : Fin 3 => Q.parts).biUnion Fintype.piFinset :=
  piFinset_const_eq_biUnion_cellTuples Q

/-- The cell boxes over distinct cell-triples are pairwise disjoint, `Fin 3` reading of
`piFinset_pairwiseDisjoint_cellTuples`. -/
theorem piFinset_pairwiseDisjoint_cellTriples (Q : Finpartition s) :
    (↑(Fintype.piFinset fun _ : Fin 3 => Q.parts) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      Fintype.piFinset :=
  piFinset_pairwiseDisjoint_cellTuples Q

/-- **The global count is the library's actual induced-embedding count over the full box.** The
partition-cell sum equals `inducedEmbeddingCountOn` on `fun _ => s`. -/
theorem globalInducedCount_eq_inducedEmbeddingCountOn :
    globalInducedCount P M Q = inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) :=
  (inducedEmbeddingCountOn_eq_sum_cellTuples P M Q).symm

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
  rw [globalInducedCount_eq_inducedEmbeddingCountOn, inducedEmbeddingCountOn_univ]

/-! ### Arity-generic cell tuples and the collision decomposition -/

/-- Ordered `k`-tuples of cells of `Q` with a repeated cell (the complement of the transversal
tuples inside all ordered cell-tuples). `nontransversalCellTriples` is the `k = 3` instance. -/
def nontransversalCellTuples {k : ℕ} (Q : Finpartition s) : Finset (Fin k → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter (fun T => ¬ Function.Injective T)

@[simp] theorem mem_nontransversalCellTuples {k : ℕ} {T : Fin k → Finset V} :
    T ∈ nontransversalCellTuples Q ↔ (∀ i, T i ∈ Q.parts) ∧ ¬ Function.Injective T := by
  simp [nontransversalCellTuples, Fintype.mem_piFinset]

theorem nontransversalCellTriples_eq_nontransversalCellTuples (Q : Finpartition s) :
    nontransversalCellTriples Q = nontransversalCellTuples Q := rfl

/-- Ordered `k`-tuples of **distinct** cells of `Q`. `transversalCellTriples` is the `k = 3`
instance. -/
def transversalCellTuples {k : ℕ} (Q : Finpartition s) : Finset (Fin k → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter Function.Injective

@[simp] theorem mem_transversalCellTuples {k : ℕ} {T : Fin k → Finset V} :
    T ∈ transversalCellTuples Q ↔ (∀ i, T i ∈ Q.parts) ∧ Function.Injective T := by
  simp [transversalCellTuples, Fintype.mem_piFinset]

theorem transversalCellTriples_eq_transversalCellTuples (Q : Finpartition s) :
    transversalCellTriples Q = transversalCellTuples Q := rfl

/-- **Transversal + nontransversal**, arity-generic: the `s`-restricted count splits exactly
along injectivity of the cell tuple. -/
theorem inducedEmbeddingCountOn_eq_transversal_add_nontransversal {k : ℕ}
    (P : FiniteRelModel L (Fin k)) (M : FiniteRelModel L V) (Q : Finpartition s) :
    inducedEmbeddingCountOn P M (fun _ : Fin k => s)
      = (∑ T ∈ transversalCellTuples Q, inducedEmbeddingCountOn P M T)
        + ∑ T ∈ nontransversalCellTuples Q, inducedEmbeddingCountOn P M T := by
  rw [inducedEmbeddingCountOn_eq_sum_cellTuples P M Q, transversalCellTuples,
    nontransversalCellTuples]
  exact (Finset.sum_filter_add_sum_filter_not _ Function.Injective _).symm

/-- The box volume of a `k`-tuple of cells: the product of the cell cardinalities.
`cellTripleVolume` is the `k = 3` instance. -/
def cellTupleVolume {k : ℕ} (T : Fin k → Finset V) : ℝ :=
  ∏ i, ((T i).card : ℝ)

omit [DecidableEq V] in
theorem cellTupleVolume_nonneg {k : ℕ} (T : Fin k → Finset V) : 0 ≤ cellTupleVolume T :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

omit [DecidableEq V] in
theorem cellTripleVolume_eq_cellTupleVolume (T : Fin 3 → Finset V) :
    cellTripleVolume T = cellTupleVolume T := by
  rw [cellTripleVolume, cellTupleVolume, Fin.prod_univ_three]

/-- Crude box bound, arity-generic: an induced count never exceeds the box volume. -/
theorem inducedEmbeddingCountOn_le_cellTupleVolume {k : ℕ} (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) (T : Fin k → Finset V) :
    (inducedEmbeddingCountOn P M T : ℝ) ≤ cellTupleVolume T := by
  rw [inducedEmbeddingCountOn, cellTupleVolume]
  have hle := (Finset.card_filter_le (Fintype.piFinset T)
    fun f => Function.Injective f ∧ PreservesAndReflects P M f).trans_eq (Fintype.card_piFinset T)
  exact_mod_cast hle

/-- **One collision event.** For `i ≠ j`, the cell tuples with `T i = T j` have total box volume
at most `m·|s|^(k−1)`: dropping coordinate `j` is injective on the event (coordinate `i` carries
the same cell), the dropped cell has cardinality at most `m`, and the remaining `k − 1`
coordinates range freely over the cells, with total volume `|s|^(k−1)`. -/
private theorem sum_collision_le {k m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) {i j : Fin k}
    (hij : i ≠ j) :
    ∑ T ∈ (Fintype.piFinset fun _ : Fin k => Q.parts).filter (fun T => T i = T j),
        cellTupleVolume T
      ≤ m * (s.card : ℝ) ^ (k - 1) := by
  classical
  set event := (Fintype.piFinset fun _ : Fin k => Q.parts).filter (fun T => T i = T j)
    with hevent
  set drop : (Fin k → Finset V) → ({l : Fin k // l ≠ j} → Finset V) := fun T l => T l.val
    with hdrop
  have hsplit : ∀ T : Fin k → Finset V,
      cellTupleVolume T = ((T j).card : ℝ) * ∏ l, ((drop T l).card : ℝ) := by
    intro T
    rw [cellTupleVolume, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    exact Finset.prod_subtype (Finset.univ.erase j) (fun l => by simp) fun l => ((T l).card : ℝ)
  have hinj : Set.InjOn drop event := by
    intro T hT T' hT' h
    rw [Finset.mem_coe, hevent, Finset.mem_filter] at hT hT'
    funext l
    by_cases hl : l = j
    · subst hl
      rw [← hT.2, ← hT'.2]
      exact congr_fun h ⟨i, hij⟩
    · exact congr_fun h ⟨l, hl⟩
  have hfree : ∑ T' ∈ Fintype.piFinset (fun _ : {l : Fin k // l ≠ j} => Q.parts),
      ∏ l, ((T' l).card : ℝ) = (s.card : ℝ) ^ (k - 1) := by
    refine (Finset.sum_prod_piFinset Q.parts fun _ C => ((C.card : ℕ) : ℝ)).trans ?_
    simp [sum_card_parts_cast, Fintype.card_subtype_compl]
  calc ∑ T ∈ event, cellTupleVolume T
      ≤ ∑ T ∈ event, (m : ℝ) * ∏ l, ((drop T l).card : ℝ) := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [hevent, Finset.mem_filter, Fintype.mem_piFinset] at hT
        rw [hsplit T]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm _ (hT.1 j))
          (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = (m : ℝ) * ∑ T' ∈ event.image drop, ∏ l, ((T' l).card : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (m : ℝ) * ∑ T' ∈ Fintype.piFinset (fun _ : {l : Fin k // l ≠ j} => Q.parts),
          ∏ l, ((T' l).card : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
          fun _ _ _ => Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
        intro T' hT'
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hT'
        rw [hevent, Finset.mem_filter, Fintype.mem_piFinset] at hT
        exact Fintype.mem_piFinset.mpr fun l => hT.1 l.val
    _ = m * (s.card : ℝ) ^ (k - 1) := by rw [hfree]

/-- **Generic diagonal bound, arity-parametric.** Any real weight dominated by the cell-tuple
volume on the nontransversal `k`-tuples has total mass at most `(k choose 2)·m·|s|^(k−1)`:
each nontransversal tuple has some strictly ordered collision `i < j`
(`not_injective_iff_exists_lt_eq`), each of the `k.choose 2` collision events contributes at most
`m·|s|^(k−1)`
(`sum_collision_le`), and the events are counted by `Fintype.card_product_filter_lt`.

Guard-free: no `2 ≤ k`, no nonempty carrier, no positive cell size, and no nonnegativity of the
weight — only the one-sided domination is used. At `k = 0` and `k = 1` every tuple is injective
and `k.choose 2 = 0`, so both sides vanish. -/
theorem sum_nontransversalCellTuples_weight_le {k m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m)
    (weight : (Fin k → Finset V) → ℝ)
    (hw : ∀ T ∈ nontransversalCellTuples Q, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ nontransversalCellTuples Q, weight T
      ≤ (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
  classical
  set pairs : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2) with hpairs
  have hpt : ∀ T : Fin k → Finset V,
      (if ¬ Function.Injective T then cellTupleVolume T else 0)
        ≤ ∑ p ∈ pairs, (if T p.1 = T p.2 then cellTupleVolume T else 0) := by
    intro T
    have hnn : ∀ p ∈ pairs, 0 ≤ (if T p.1 = T p.2 then cellTupleVolume T else 0) :=
      fun p _ => by split_ifs <;> [exact cellTupleVolume_nonneg T; exact le_rfl]
    by_cases h : Function.Injective T
    · rw [ite_eq_right (not_not.mpr h)]
      exact Finset.sum_nonneg hnn
    · rw [ite_eq_left h]
      obtain ⟨i, j, hij, hT⟩ := not_injective_iff_exists_lt_eq.mp h
      have hmem : (i, j) ∈ pairs := by
        rw [hpairs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hij⟩
      calc cellTupleVolume T
          = (if T (i, j).1 = T (i, j).2 then cellTupleVolume T else 0) := by rw [ite_eq_left hT]
        _ ≤ ∑ p ∈ pairs, (if T p.1 = T p.2 then cellTupleVolume T else 0) :=
          Finset.single_le_sum hnn hmem
  have hcard : pairs.card = k.choose 2 := by
    simpa [hpairs] using Fintype.card_product_filter_lt (α := Fin k)
  calc ∑ T ∈ nontransversalCellTuples Q, weight T
      ≤ ∑ T ∈ nontransversalCellTuples Q, cellTupleVolume T := Finset.sum_le_sum hw
    _ = ∑ T ∈ Fintype.piFinset fun _ : Fin k => Q.parts,
          (if ¬ Function.Injective T then cellTupleVolume T else 0) := by
        rw [nontransversalCellTuples, Finset.sum_filter]
    _ ≤ ∑ T ∈ Fintype.piFinset fun _ : Fin k => Q.parts,
          ∑ p ∈ pairs, (if T p.1 = T p.2 then cellTupleVolume T else 0) :=
        Finset.sum_le_sum fun T _ => hpt T
    _ = ∑ p ∈ pairs, ∑ T ∈ (Fintype.piFinset fun _ : Fin k => Q.parts).filter
          (fun T => T p.1 = T p.2), cellTupleVolume T := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _p ∈ pairs, (m : ℝ) * (s.card : ℝ) ^ (k - 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [hpairs, Finset.mem_filter] at hp
        exact sum_collision_le hm hp.2.ne
    _ = (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-! ### The positional lift of the bad-pair mass -/

/-- Cell `k`-tuples with **some coordinate-pair position** `i < j` landing in the bad pair set
`D` (over all ordered cell tuples; the transversal bad tuples are a subset). -/
def badCellTuples {k : ℕ} (Q : Finpartition s) (D : Finset (Finset V × Finset V)) :
    Finset (Fin k → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter fun T => ∃ i j, i < j ∧ (T i, T j) ∈ D

@[simp] theorem mem_badCellTuples {k : ℕ} {D : Finset (Finset V × Finset V)}
    {T : Fin k → Finset V} :
    T ∈ badCellTuples Q D ↔ (∀ i, T i ∈ Q.parts) ∧ ∃ i j, i < j ∧ (T i, T j) ∈ D := by
  simp [badCellTuples, Fintype.mem_piFinset]

/-- **One position.** For `i ≠ j`, the cell tuples whose `(i, j)` position lies in `D` have total
volume at most the `D`-pair mass times `|s|^(k−2)`: the pair `(T i, T j)` together with the
remaining coordinates determines `T`, the pair ranges over `D`, and the other `k − 2`
coordinates range freely over the cells with total volume `|s|^(k−2)`. No hypothesis
`D ⊆ Q.parts ×ˢ Q.parts` is needed: the map into `D ×ˢ (free box)` is merely injective. -/
private theorem sum_position_le {k : ℕ} {D : Finset (Finset V × Finset V)} {i j : Fin k}
    (hij : i ≠ j) :
    ∑ T ∈ (Fintype.piFinset fun _ : Fin k => Q.parts).filter (fun T => (T i, T j) ∈ D),
        cellTupleVolume T
      ≤ (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) := by
  classical
  set event := (Fintype.piFinset fun _ : Fin k => Q.parts).filter (fun T => (T i, T j) ∈ D)
    with hevent
  set free := Fintype.piFinset (fun _ : {l : Fin k // l ≠ i ∧ l ≠ j} => Q.parts) with hfree
  set emb : (Fin k → Finset V) →
      (Finset V × Finset V) × ({l : Fin k // l ≠ i ∧ l ≠ j} → Finset V) :=
    fun T => ((T i, T j), fun l => T l.val) with hemb
  set G : (Finset V × Finset V) × ({l : Fin k // l ≠ i ∧ l ≠ j} → Finset V) → ℝ :=
    fun q => (q.1.1.card : ℝ) * q.1.2.card * ∏ l, ((q.2 l).card : ℝ) with hG
  have hsplit : ∀ T : Fin k → Finset V, cellTupleVolume T = G (emb T) := by
    intro T
    simp only [hG, hemb, cellTupleVolume]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) _
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc]
    congr 1
    exact Finset.prod_subtype ((Finset.univ.erase i).erase j)
      (fun l => by simp [and_comm]) fun l => ((T l).card : ℝ)
  have hinj : Set.InjOn emb event := by
    intro T _ T' _ h
    simp only [hemb, Prod.mk.injEq] at h
    funext l
    by_cases hl : l = i
    · subst hl; exact h.1.1
    by_cases hl' : l = j
    · subst hl'; exact h.1.2
    exact congr_fun h.2 ⟨l, hl, hl'⟩
  have hcard : Fintype.card {l : Fin k // l ≠ i ∧ l ≠ j} = k - 2 := by
    rw [Fintype.card_subtype]
    have hfilt : (Finset.univ.filter fun l : Fin k => l ≠ i ∧ l ≠ j)
        = (Finset.univ.erase i).erase j := by
      ext l; simp [and_comm]
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hfreesum : ∑ T' ∈ free, ∏ l, ((T' l).card : ℝ) = (s.card : ℝ) ^ (k - 2) := by
    rw [hfree]
    refine (Finset.sum_prod_piFinset Q.parts fun _ C => ((C.card : ℕ) : ℝ)).trans ?_
    simp [sum_card_parts_cast, hcard]
  calc ∑ T ∈ event, cellTupleVolume T
      = ∑ T ∈ event, G (emb T) := Finset.sum_congr rfl fun T _ => hsplit T
    _ = ∑ q ∈ event.image emb, G q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ D ×ˢ free, G q := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => ?_
        · intro q hq
          obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hq
          rw [hevent, Finset.mem_filter, Fintype.mem_piFinset] at hT
          exact Finset.mem_product.mpr ⟨hT.2, Fintype.mem_piFinset.mpr fun l => hT.1 l.val⟩
        · simp only [hG]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) := by
        simp only [hG]
        rw [Finset.sum_product, ← hfreesum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by dsimp only; rw [← Finset.mul_sum]

/-- **The positional lift, raw form.** Any real weight dominated by the cell-tuple volume on
the bad tuples has total mass at most `(k.choose 2)` times the `D`-pair mass times `|s|^(k−2)`:
a bad tuple is charged to some strictly ordered position `i < j` with `(T i, T j) ∈ D`, and
each of the `k.choose 2` positions carries at most the pair mass times the free volume
(`sum_position_le`). `selectedPairTripleMass_any_le` is recovered at `k = 3` by restricting to
transversal tuples (coefficient `3.choose 2 = 3`, free volume `|s|`).

Guard-free: no `2 ≤ k` (at `k < 2` there are no positions, and `k.choose 2 = 0`), no
`D ⊆ Q.parts ×ˢ Q.parts`, no nonnegativity of the weight. -/
theorem sum_badCellTuples_weight_le_mass {k : ℕ} {D : Finset (Finset V × Finset V)}
    (weight : (Fin k → Finset V) → ℝ)
    (hw : ∀ T ∈ badCellTuples Q D, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ badCellTuples Q D, weight T
      ≤ (k.choose 2) * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) := by
  classical
  set pairs : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2) with hpairs
  have hpt : ∀ T : Fin k → Finset V,
      (if ∃ i j, i < j ∧ (T i, T j) ∈ D then cellTupleVolume T else 0)
        ≤ ∑ p ∈ pairs, (if (T p.1, T p.2) ∈ D then cellTupleVolume T else 0) := by
    intro T
    have hnn : ∀ p ∈ pairs, 0 ≤ (if (T p.1, T p.2) ∈ D then cellTupleVolume T else 0) :=
      fun p _ => by split_ifs <;> [exact cellTupleVolume_nonneg T; exact le_rfl]
    by_cases h : ∃ i j, i < j ∧ (T i, T j) ∈ D
    · rw [ite_eq_left h]
      obtain ⟨i, j, hij, hT⟩ := h
      have hmem : (i, j) ∈ pairs := by
        rw [hpairs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hij⟩
      calc cellTupleVolume T
          = (if (T (i, j).1, T (i, j).2) ∈ D then cellTupleVolume T else 0) := by
            rw [ite_eq_left hT]
        _ ≤ ∑ p ∈ pairs, (if (T p.1, T p.2) ∈ D then cellTupleVolume T else 0) :=
          Finset.single_le_sum hnn hmem
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg hnn
  have hcard : pairs.card = k.choose 2 := by
    simpa [hpairs] using Fintype.card_product_filter_lt (α := Fin k)
  calc ∑ T ∈ badCellTuples Q D, weight T
      ≤ ∑ T ∈ badCellTuples Q D, cellTupleVolume T := Finset.sum_le_sum hw
    _ = ∑ T ∈ Fintype.piFinset fun _ : Fin k => Q.parts,
          (if ∃ i j, i < j ∧ (T i, T j) ∈ D then cellTupleVolume T else 0) := by
        rw [badCellTuples, Finset.sum_filter]
    _ ≤ ∑ T ∈ Fintype.piFinset fun _ : Fin k => Q.parts,
          ∑ p ∈ pairs, (if (T p.1, T p.2) ∈ D then cellTupleVolume T else 0) :=
        Finset.sum_le_sum fun T _ => hpt T
    _ = ∑ p ∈ pairs, ∑ T ∈ (Fintype.piFinset fun _ : Fin k => Q.parts).filter
          (fun T => (T p.1, T p.2) ∈ D), cellTupleVolume T := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ _p ∈ pairs, (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [hpairs, Finset.mem_filter] at hp
        exact sum_position_le hp.2.ne
    _ = (k.choose 2) * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-- **The positional lift, normalized.** With the **single aggregated** bad-pair mass bound
`Σ_{(A,B) ∈ D} |A|·|B| ≤ β·|s|²` (the arity-3 `hmass`, verbatim), the bad cell tuples carry
weight at most `(k.choose 2)·β·|s|^k`. The `k.choose 2` is the positional lift of
`sum_badCellTuples_weight_le_mass`, never a union bound over per-pair hypotheses: a consumer
holding per-pair bounds sums them into this one hypothesis first. `badTripleVolume_le` is
recovered at `k = 3` by restricting to transversal tuples. Guard-free in `k`. -/
theorem sum_badCellTuples_weight_le {k : ℕ} {D : Finset (Finset V × Finset V)} {β : ℝ}
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (weight : (Fin k → Finset V) → ℝ)
    (hw : ∀ T ∈ badCellTuples Q D, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ badCellTuples Q D, weight T ≤ (k.choose 2) * β * (s.card : ℝ) ^ k := by
  refine (sum_badCellTuples_weight_le_mass weight hw).trans ?_
  rcases lt_or_ge k 2 with hk | hk
  · rw [Nat.choose_eq_zero_of_lt hk]
    simp
  · have hpow : (s.card : ℝ) ^ 2 * (s.card : ℝ) ^ (k - 2) = (s.card : ℝ) ^ k := by
      rw [← pow_add]
      congr 1
      omega
    calc (k.choose 2 : ℝ) * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2)
        ≤ (k.choose 2 : ℝ) * (β * (s.card : ℝ) ^ 2) * (s.card : ℝ) ^ (k - 2) := by
          gcongr
      _ = (k.choose 2 : ℝ) * β * ((s.card : ℝ) ^ 2 * (s.card : ℝ) ^ (k - 2)) := by ring
      _ = (k.choose 2) * β * (s.card : ℝ) ^ k := by rw [hpow]

/-! ### The quotient counting theorem -/

section QuotientCounting

variable {k : ℕ}

/-- **The transversal part of an indivisible model's count is the quotient-weighted count.**
Transversal cell tuples correspond to injective tuples of cells, and on each the box count is
all-or-nothing (`IsIndivisibleFor.inducedEmbeddingCountOn_cells`). -/
theorem sum_transversalCellTuples_eq_quotientInducedCount {N : FiniteRelModel L V}
    (h : N.IsIndivisibleFor Q) (P : FiniteRelModel L (Fin k)) :
    ∑ T ∈ transversalCellTuples Q, inducedEmbeddingCountOn P N T = quotientInducedCount P N Q := by
  rw [quotientInducedCount_eq_sum_ite h P]
  refine Finset.sum_bij (fun T hT i => ⟨T i, (mem_transversalCellTuples.mp hT).1 i⟩)
    (fun T hT => ?_) (fun T hT T' hT' heq => ?_) (fun C hC => ?_) (fun T hT => rfl)
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i j hij =>
      (mem_transversalCellTuples.mp hT).2 (congrArg Subtype.val hij)⟩
  · funext i
    exact congrArg Subtype.val (congr_fun heq i)
  · refine ⟨fun i => (C i : Finset V), mem_transversalCellTuples.mpr
      ⟨fun i => (C i).2, fun i j hij => (Finset.mem_filter.mp hC).2 (Subtype.ext hij)⟩, rfl⟩

/-- The quotient-weighted count never exceeds the `s`-restricted count of an indivisible
model: the nontransversal part is nonnegative. -/
theorem FiniteRelModel.IsIndivisibleFor.quotientInducedCount_le {N : FiniteRelModel L V}
    (h : N.IsIndivisibleFor Q) (P : FiniteRelModel L (Fin k)) :
    quotientInducedCount P N Q ≤ inducedEmbeddingCountOn P N (fun _ : Fin k => s) := by
  rw [inducedEmbeddingCountOn_eq_transversal_add_nontransversal P N Q,
    sum_transversalCellTuples_eq_quotientInducedCount h P]
  exact Nat.le_add_right _ _

/-- **Quotient counting.** For `N` indivisible for `Q` with cells of size at most `m`, the
`s`-restricted induced count of a `k`-vertex pattern is the quotient-weighted count up to the
diagonal charge `(k.choose 2)·m·|s|^(k−1)`: the transversal part is exact
(`sum_transversalCellTuples_eq_quotientInducedCount`), and the repeated-cell tuples — reachable
by injective host tuples, with no exact formula attempted — route entirely through the diagonal
gate `sum_nontransversalCellTuples_weight_le`. The only constant is the gate's. Stated in
`s`-restricted units; the full-carrier form is
`abs_inducedEmbeddingCount_sub_quotientInducedCount_le` at `s = univ`. -/
theorem FiniteRelModel.IsIndivisibleFor.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le
    {N : FiniteRelModel L V} (h : N.IsIndivisibleFor Q) (P : FiniteRelModel L (Fin k)) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P N (fun _ : Fin k => s) : ℝ) - quotientInducedCount P N Q|
      ≤ (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
  rw [inducedEmbeddingCountOn_eq_transversal_add_nontransversal P N Q,
    sum_transversalCellTuples_eq_quotientInducedCount h P]
  push_cast
  rw [add_sub_cancel_left, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  exact sum_nontransversalCellTuples_weight_le hm _
    fun T _ => inducedEmbeddingCountOn_le_cellTupleVolume P N T

/-- **Quotient counting on the full carrier**: the `s = univ` specialization, with the diagonal
charge in units of `|V|^(k−1)`. -/
theorem FiniteRelModel.IsIndivisibleFor.abs_inducedEmbeddingCount_sub_quotientInducedCount_le
    [Fintype V] {N : FiniteRelModel L V} {Q : Finpartition (Finset.univ : Finset V)}
    (h : N.IsIndivisibleFor Q) (P : FiniteRelModel L (Fin k)) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCount P N : ℝ) - quotientInducedCount P N Q|
      ≤ (k.choose 2) * m * (Fintype.card V : ℝ) ^ (k - 1) := by
  have := h.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le P hm
  rwa [inducedEmbeddingCountOn_univ, Finset.card_univ] at this

end QuotientCounting

/-! ### The `Fin 3` instance: collision characterization and the `3·m·|s|²` bound -/

/-- A `Fin 3`-indexed triple fails to be injective exactly when two coordinates collide. The
`k = 3` instance of `not_injective_iff_exists_lt_eq`, with the three `i < j` pairs enumerated. -/
theorem not_injective_fin_three {α : Type*} {T : Fin 3 → α} :
    ¬ Function.Injective T ↔ T 0 = T 1 ∨ T 0 = T 2 ∨ T 1 = T 2 := by
  rw [not_injective_iff_exists_lt_eq]
  constructor
  · rintro ⟨i, j, hij, hT⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨1, 2, by decide, h⟩

/-- **Generic diagonal bound.** The `3·m·|s|²` estimate is a statement about *volume*, not about
induced counts: any real weight dominated by the cell-triple volume on the nontransversal triples
obeys it. Three collision events, each contributing at most `m·|s|²`. The `k = 3` instance of
`sum_nontransversalCellTuples_weight_le`, with `3.choose 2 = 3`.

Domination is the only hypothesis — nonnegativity of the weight is never used, since the bound is
one-sided. Consumers supply their own domination lemma: `inducedEmbeddingCountOn` does so via
`inducedEmbeddingCountOn_le_cellTripleVolume` (see
`sum_nontransversal_inducedEmbeddingCountOn_le`), and any *predicted*/expected mass qualifies as
soon as it is shown to be at most the box volume — which is immediate for a volume times a product
of densities in `[0, 1]`. -/
theorem sum_nontransversal_weight_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m)
    (weight : (Fin 3 → Finset V) → ℝ)
    (hw : ∀ T ∈ nontransversalCellTriples Q, weight T ≤ cellTripleVolume T) :
    ∑ T ∈ nontransversalCellTriples Q, weight T ≤ 3 * m * (s.card : ℝ) ^ 2 := by
  have h := sum_nontransversalCellTuples_weight_le hm weight
    fun T hT => (hw T hT).trans_eq (cellTripleVolume_eq_cellTupleVolume T)
  rw [nontransversalCellTriples_eq_nontransversalCellTuples]
  rw [show Nat.choose 3 2 = 3 from rfl] at h
  simpa using h

/-- **Derived diagonal bound.** When every cell of `Q` has cardinality at most `m`, the
nontransversal induced count is at most `3·m·|s|²`. One specialization of
`sum_nontransversal_weight_le`. -/
theorem sum_nontransversal_inducedEmbeddingCountOn_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ((∑ T ∈ nontransversalCellTriples Q, inducedEmbeddingCountOn P M T : ℕ) : ℝ)
      ≤ 3 * m * (s.card : ℝ) ^ 2 := by
  rw [Nat.cast_sum]
  exact sum_nontransversal_weight_le hm _
    fun T _ => inducedEmbeddingCountOn_le_cellTripleVolume P M T

/-- **Predicted-side diagonal bound.** A *predicted* mass of the shape "box volume times a factor
at most `1`" — the shape of every step estimate, where the factor is a product of densities — is
dominated by the volume, hence obeys the same `3·m·|s|²` charge.

This is the second specialization of `sum_nontransversal_weight_le`, and it settles the predicted
side generically: no counting definition, palette, or route structure is needed, only that the
density factor is at most one. Nonnegativity of the factor is not required, the bound being
one-sided. -/
theorem sum_nontransversal_volume_mul_le {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m)
    (factor : (Fin 3 → Finset V) → ℝ) (hf : ∀ T, factor T ≤ 1) :
    ∑ T ∈ nontransversalCellTriples Q, cellTripleVolume T * factor T
      ≤ 3 * m * (s.card : ℝ) ^ 2 :=
  sum_nontransversal_weight_le hm _ fun T _ =>
    calc cellTripleVolume T * factor T
        ≤ cellTripleVolume T * 1 :=
          mul_le_mul_of_nonneg_left (hf T) (cellTripleVolume_nonneg T)
      _ = cellTripleVolume T := mul_one _

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

-- **Degenerate arities `k = 0` and `k = 1`**: every tuple is injective, so the nontransversal
-- family is empty, and the generic bound is `0` on both sides.
example : nontransversalCellTuples (k := 0)
    (⊤ : Finpartition (Finset.univ : Finset (Fin 2))) = ∅ := by decide
example : nontransversalCellTuples (k := 1)
    (⊤ : Finpartition (Finset.univ : Finset (Fin 2))) = ∅ := by decide
example (m : ℕ) : ((Nat.choose 0 2 : ℕ) : ℝ) * m * (s.card : ℝ) ^ (0 - 1) = 0 := by simp
example (m : ℕ) : ((Nat.choose 1 2 : ℕ) : ℝ) * m * (s.card : ℝ) ^ (1 - 1) = 0 := by simp
example {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) (weight : (Fin 0 → Finset V) → ℝ)
    (hw : ∀ T ∈ nontransversalCellTuples Q, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ nontransversalCellTuples Q, weight T ≤ 0 := by
  simpa using sum_nontransversalCellTuples_weight_le hm weight hw
example {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) (weight : (Fin 1 → Finset V) → ℝ)
    (hw : ∀ T ∈ nontransversalCellTuples Q, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ nontransversalCellTuples Q, weight T ≤ 0 := by
  simpa using sum_nontransversalCellTuples_weight_le hm weight hw

-- **`k = 2`: the coefficient is one, and the bound is attained.** With the indiscrete partition
-- of a two-vertex carrier the only cell pair is the diagonal `(univ, univ)`, of volume `4`, and
-- the bound `1 · 2 · 2¹ = 4` is exact.
example : nontransversalCellTuples (k := 2) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
    = {fun _ => Finset.univ} := by decide
example : ∑ T ∈ nontransversalCellTuples (k := 2)
      (⊤ : Finpartition (Finset.univ : Finset (Fin 2))), cellTupleVolume T
    = ((Nat.choose 2 2 : ℕ) : ℝ) * (2 : ℕ)
        * ((Finset.univ : Finset (Fin 2)).card : ℝ) ^ (2 - 1) := by
  rw [show nontransversalCellTuples (k := 2) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
    = {fun _ => Finset.univ} by decide, Finset.sum_singleton, cellTupleVolume]
  norm_num

-- **`k = 3` recovers the `3·m·|s|²` theorem**: the generic coefficient is `3.choose 2 = 3`.
example (m : ℕ) : ((Nat.choose 3 2 : ℕ) : ℝ) * m * (s.card : ℝ) ^ (3 - 1)
    = 3 * m * (s.card : ℝ) ^ 2 := by
  norm_num [show Nat.choose 3 2 = 3 from rfl]
example {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) (weight : (Fin 3 → Finset V) → ℝ)
    (hw : ∀ T ∈ nontransversalCellTriples Q, weight T ≤ cellTripleVolume T) :
    ∑ T ∈ nontransversalCellTriples Q, weight T ≤ 3 * m * (s.card : ℝ) ^ 2 :=
  sum_nontransversal_weight_le hm weight hw

-- **A collision presented in the wrong order** still lands in the nontransversal family: the
-- witness is reordered to `i < j` by the characterization.
example {k : ℕ} {T : Fin k → Finset V} (hT : ∀ i, T i ∈ Q.parts) {i j : Fin k} (hij : j < i)
    (h : T i = T j) : T ∈ nontransversalCellTuples Q :=
  mem_nontransversalCellTuples.mpr ⟨hT, not_injective_iff_exists_lt_eq.mpr ⟨j, i, hij, h.symm⟩⟩

-- **Positional lift, degenerate arities `k = 0` and `k = 1`**: no coordinate-pair position
-- exists, so the bad family is empty and the bound is `0` on both sides.
example : badCellTuples (k := 0) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
    {((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))} = ∅ := by decide
example : badCellTuples (k := 1) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
    {((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))} = ∅ := by decide
example {D : Finset (Finset V × Finset V)} {β : ℝ}
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (weight : (Fin 1 → Finset V) → ℝ)
    (hw : ∀ T ∈ badCellTuples Q D, weight T ≤ cellTupleVolume T) :
    ∑ T ∈ badCellTuples Q D, weight T ≤ 0 := by
  simpa using sum_badCellTuples_weight_le hmass weight hw

-- **Positional lift at `k = 2`: coefficient one, bound attained.** The single bad pair
-- `(univ, univ)` has mass `4`, the only cell pair is bad with volume `4`, and the raw bound
-- `1 · 4 · 2⁰ = 4` is exact.
example : badCellTuples (k := 2) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
      {((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))}
    = {fun _ => Finset.univ} := by decide
example : ∑ T ∈ badCellTuples (k := 2) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
      {((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))}, cellTupleVolume T
    = ((Nat.choose 2 2 : ℕ) : ℝ)
        * (∑ p ∈ ({((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))} :
            Finset (Finset (Fin 2) × Finset (Fin 2))), (p.1.card : ℝ) * p.2.card)
        * ((Finset.univ : Finset (Fin 2)).card : ℝ) ^ (2 - 2) := by
  rw [show badCellTuples (k := 2) (⊤ : Finpartition (Finset.univ : Finset (Fin 2)))
      {((Finset.univ : Finset (Fin 2)), (Finset.univ : Finset (Fin 2)))}
    = {fun _ => Finset.univ} by decide, Finset.sum_singleton, Finset.sum_singleton,
    cellTupleVolume]
  norm_num

-- **`k = 3` recovers the arity-3 bad-pair set**: a triple is bad exactly when one of its three
-- coordinate pairs lies in `D`, in the order `badTripleVolume_le` states it.
example {D : Finset (Finset V × Finset V)} {T : Fin 3 → Finset V} :
    (∃ i j, i < j ∧ (T i, T j) ∈ D)
      ↔ (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D := by
  constructor
  · rintro ⟨i, j, hij, hT⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨0, 2, by decide, h⟩
    · exact ⟨1, 2, by decide, h⟩

-- **`k = 3` recovers `badTripleVolume_le`**: the generic lift, restricted to transversal
-- triples, gives the `3 · β · |s|³` bound with `3 = 3.choose 2`.
example {D : Finset (Finset V × Finset V)} {β : ℝ}
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2) :
    ∑ T ∈ (transversalCellTriples Q).filter
        (fun T => (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ 3 * β * (s.card : ℝ) ^ 3 := by
  have h := sum_badCellTuples_weight_le (Q := Q) (k := 3) hmass cellTupleVolume fun T _ => le_rfl
  rw [show Nat.choose 3 2 = 3 from rfl] at h
  push_cast at h
  calc ∑ T ∈ (transversalCellTriples Q).filter
        (fun T => (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ badCellTuples (k := 3) Q D, ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun T _ _ => by positivity
        intro T hT
        rw [Finset.mem_filter, transversalCellTriples, Finset.mem_filter,
          Fintype.mem_piFinset] at hT
        rw [mem_badCellTuples]
        refine ⟨hT.1.1, ?_⟩
        rcases hT.2 with h01 | h02 | h12
        · exact ⟨0, 1, by decide, h01⟩
        · exact ⟨0, 2, by decide, h02⟩
        · exact ⟨1, 2, by decide, h12⟩
    _ = ∑ T ∈ badCellTuples (k := 3) Q D, cellTupleVolume T :=
        Finset.sum_congr rfl fun T _ => by rw [cellTupleVolume, Fin.prod_univ_three]
    _ ≤ 3 * β * (s.card : ℝ) ^ 3 := h

-- **No containment hypothesis on `D`**: the lift takes an arbitrary pair set.
example {D : Finset (Finset V × Finset V)} {k : ℕ} :
    ∑ T ∈ badCellTuples (k := k) Q D, cellTupleVolume T
      ≤ (k.choose 2) * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * (s.card : ℝ) ^ (k - 2) :=
  sum_badCellTuples_weight_le_mass _ fun _ _ => le_rfl

-- **Signed weights on the positional lift.**
example {D : Finset (Finset V × Finset V)} {k : ℕ} {β : ℝ}
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2) :
    ∑ T ∈ badCellTuples (k := k) Q D, (-cellTupleVolume T)
      ≤ (k.choose 2) * β * (s.card : ℝ) ^ k :=
  sum_badCellTuples_weight_le hmass _ fun T _ => by linarith [cellTupleVolume_nonneg T]

-- **Signed weights.** No nonnegativity is assumed: a weight that is `-1` everywhere (or any
-- negative multiple of the volume) is dominated by the volume and obeys the same bound.
example {k m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ _T ∈ nontransversalCellTuples (k := k) Q, (-1 : ℝ)
      ≤ (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) :=
  sum_nontransversalCellTuples_weight_le hm _ fun T _ => by linarith [cellTupleVolume_nonneg T]
example {k m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    ∑ T ∈ nontransversalCellTuples (k := k) Q, (-2 * cellTupleVolume T)
      ≤ (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) :=
  sum_nontransversalCellTuples_weight_le hm _ fun T _ => by linarith [cellTupleVolume_nonneg T]

-- **Quotient counting on the empty language.** Every model is indivisible for every partition
-- (there are no symbols), and every cell tuple matches the (empty) pattern constraints.
private theorem emptyModel_isIndivisibleFor {W : Type*} [DecidableEq W] {t : Finset W}
    (Q : Finpartition t) : (emptyModel W).IsIndivisibleFor Q :=
  fun _ R => R.elim

-- With the discrete partition `⊥` every cell is a singleton: the six transversal cell triples
-- each carry volume `1`, the quotient count is `6`, and the diagonal remainder is `0`.
example : quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) = 6 := by decide

-- With the indiscrete partition `⊤` there is no transversal triple at all: the quotient count
-- is `0`, and the whole count `6` is diagonal.
example : quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
    (⊤ : Finpartition (Finset.univ : Finset (Fin 3))) = 0 := by decide

-- **The quotient counting theorem, instantiated** at `⊥` (`m = 1`, exact) and `⊤` (`m = 3`).
example : |(inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3))
        (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3))) : ℝ)
      - quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
          (⊥ : Finpartition (Finset.univ : Finset (Fin 3)))|
    ≤ (Nat.choose 3 2) * (1 : ℕ) * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ (3 - 1) :=
  (emptyModel_isIndivisibleFor _).abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le _
    (by decide)
example : |(inducedEmbeddingCount (emptyModel (Fin 3)) (emptyModel (Fin 3)) : ℝ)
      - quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
          (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))|
    ≤ (Nat.choose 3 2) * (3 : ℕ) * (Fintype.card (Fin 3) : ℝ) ^ (3 - 1) :=
  (emptyModel_isIndivisibleFor _).abs_inducedEmbeddingCount_sub_quotientInducedCount_le _
    (by decide)

-- **The quotient count is a lower bound**, and it is exact at `⊥`.
example : quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))
    ≤ inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3))) :=
  (emptyModel_isIndivisibleFor _).quotientInducedCount_le _
example : quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (⊥ : Finpartition (Finset.univ : Finset (Fin 3)))
    = inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3))
      (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3))) := by decide

-- **`k = 0` is guard-free**: the empty pattern has exactly one embedding, the quotient count is
-- `1` (the empty cell tuple is transversal and matches), and the diagonal charge is `0`.
example : quotientInducedCount (emptyModel (Fin 0)) (emptyModel (Fin 3))
    (⊤ : Finpartition (Finset.univ : Finset (Fin 3))) = 1 := by decide
example : |(inducedEmbeddingCountOn (emptyModel (Fin 0)) (emptyModel (Fin 3))
        (fun _ : Fin 0 => (Finset.univ : Finset (Fin 3))) : ℝ)
      - quotientInducedCount (emptyModel (Fin 0)) (emptyModel (Fin 3))
          (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))| ≤ 0 := by
  simpa using
    (emptyModel_isIndivisibleFor _).abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le
      (emptyModel (Fin 0)) (m := 3) (by decide)

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
