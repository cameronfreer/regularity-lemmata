/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.ProductBox
import RegularityLemmata.Partition.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Independent coordinate partitions of a weighted box

Partitioning each coordinate of a box independently partitions the box: a **product cell** is a
choice of one part in every coordinate, and the tuples of a box are exactly the tuples of its
product cells, each counted once.

## Why this is a separate module

`Finite/ProductBox.lean` is deliberately instance-light: it needs `[Fintype ι]` and
`[DecidableEq ι]`, and **no** decidable equality on the carriers. `Finpartition (A i)` needs the
lattice structure on `Finset (V i)`, hence `[DecidableEq (V i)]` fiberwise. That requirement is
legitimate here — the cells are manipulated as finite families of finsets — but it must not leak
backwards, so it is confined to this module and `FiniteBox`, `boxMass`, and `boxDensity` keep
their lighter instance profile.

The instances are written out at every declaration rather than hidden behind `classical`, so a
reader can see exactly what each result costs.

## Refinement direction

`Partition/Basic.lean` fixes the convention: in the `Finpartition` order, `Q ≤ P` means `Q` is
**finer** than `P`. Refinement of a box partition is that relation coordinatewise,
`∀ i, Q i ≤ P i`.

## What the decompositions rest on

The one-dimensional regrouping lemmas of `Partition/Basic.lean` are not what proves the box
decompositions. Those follow from two facts about the product cells themselves — distinct cells
have disjoint tuple sets, and the cells cover `A.tuples` — after which a single `Finset` biUnion
sum splits the mass. Both decompositions are exact and **denominator-free**, so they hold for
signed weights and for boxes of zero mass, with no positivity anywhere.

## Not here

`CoordinateSplit` is not mentioned. Restriction and gluing along a split remain the separate
final tranche.
-/

namespace RegularityLemmata

variable {ι : Type*} {V : ι → Type*}

/-! ### Box partitions and their product cells -/

/-- **A partition of a box**: a `Finpartition` of the allowed values in each coordinate,
chosen independently. Unbundled, exactly as `FiniteBox` is. -/
abbrev BoxPartition [∀ i, DecidableEq (V i)] (A : FiniteBox V) : Type _ :=
  ∀ i, Finpartition (A i)

/-- **The product cells of a box partition**: the boxes obtained by choosing one part in each
coordinate. Built from Mathlib's dependent `piFinset`, the same enumeration `FiniteBox.tuples`
uses, rather than a second mechanism. -/
def boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] {A : FiniteBox V}
    (P : BoxPartition A) : Finset (FiniteBox V) :=
  Fintype.piFinset fun i => (P i).parts

@[simp] theorem mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} :
    C ∈ boxCells P ↔ ∀ i, C i ∈ (P i).parts := Fintype.mem_piFinset

/-- **The number of product cells** is the product of the per-coordinate part counts. -/
@[simp] theorem card_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    (boxCells P).card = ∏ i, (P i).parts.card := Fintype.card_piFinset _

/-- Every product cell is a sub-box of the box being partitioned. -/
theorem boxCells_subset [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] {A : FiniteBox V}
    {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P) (i : ι) : C i ⊆ A i :=
  (P i).le (mem_boxCells.mp hC i)

theorem tuples_subset_of_mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P) :
    C.tuples ⊆ A.tuples := fun _ hx =>
  FiniteBox.mem_tuples.mpr fun i => boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)

/-! ### The cell of a tuple -/

/-- The product cell a tuple lies in: coordinatewise, the part containing its value there. -/
def cellOf [∀ i, DecidableEq (V i)] {A : FiniteBox V} (P : BoxPartition A) (x : ∀ i, V i) :
    FiniteBox V := fun i => (P i).part (x i)

@[simp] theorem cellOf_apply [∀ i, DecidableEq (V i)] {A : FiniteBox V} (P : BoxPartition A)
    (x : ∀ i, V i) (i : ι) : cellOf P x i = (P i).part (x i) := rfl

theorem cellOf_mem_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) {x : ∀ i, V i} (hx : x ∈ A.tuples) :
    cellOf P x ∈ boxCells P :=
  mem_boxCells.mpr fun i => (P i).part_mem.mpr (FiniteBox.mem_tuples.mp hx i)

theorem mem_tuples_cellOf [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) {x : ∀ i, V i} (hx : x ∈ A.tuples) :
    x ∈ (cellOf P x).tuples :=
  FiniteBox.mem_tuples.mpr fun i => (P i).mem_part (FiniteBox.mem_tuples.mp hx i)

/-- A tuple determines its cell: any cell containing it is the one `cellOf` names. -/
theorem eq_cellOf_of_mem_tuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P : BoxPartition A} {C : FiniteBox V} (hC : C ∈ boxCells P)
    {x : ∀ i, V i} (hx : x ∈ C.tuples) : C = cellOf P x := by
  funext i
  refine (P i).eq_of_mem_parts (mem_boxCells.mp hC i) ((P i).part_mem.mpr ?_)
    (FiniteBox.mem_tuples.mp hx i) ((P i).mem_part ?_)
  · exact boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)
  · exact boxCells_subset hC i (FiniteBox.mem_tuples.mp hx i)

/-! ### Disjointness and coverage -/

/-- **Distinct product cells have disjoint tuple sets.** They differ in some coordinate, and two
distinct parts there are disjoint. -/
theorem boxCells_pairwiseDisjoint [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    ((boxCells P : Finset (FiniteBox V)) : Set (FiniteBox V)).PairwiseDisjoint
      FiniteBox.tuples := by
  intro C hC D hD hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hxC hxD
  exact hne ((eq_cellOf_of_mem_tuples (Finset.mem_coe.mp hC) hxC).trans
    (eq_cellOf_of_mem_tuples (Finset.mem_coe.mp hD) hxD).symm)

/-- **The product cells cover the box.** -/
theorem biUnion_boxCells_tuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} (P : BoxPartition A) :
    (boxCells P).biUnion FiniteBox.tuples = A.tuples := by
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hx⟩
    exact tuples_subset_of_mem_boxCells hC hx
  · intro hx
    exact ⟨cellOf P x, cellOf_mem_boxCells P hx, mem_tuples_cellOf P hx⟩

/-! ### Exact decompositions

Both are denominator-free and carry no positivity hypothesis, so they hold for signed weights
and for boxes of zero mass, including the case of an empty coordinate where every side is `0`. -/

/-- **The mass of a box is the sum of the masses of its product cells.** -/
theorem boxMass_eq_sum_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {A : FiniteBox V} (P : BoxPartition A) :
    boxMass w A = ∑ C ∈ boxCells P, boxMass w C := by
  rw [boxMass_apply, ← biUnion_boxCells_tuples P,
    Finset.sum_biUnion (boxCells_pairwiseDisjoint P)]
  rfl

/-- **Predicate mass decomposes the same way**, since the predicate cuts each cell
independently. -/
theorem boxPredMass_eq_sum_boxCells [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {A : FiniteBox V} (P : BoxPartition A) (p : (∀ i, V i) → Prop)
    [DecidablePred p] :
    boxPredMass w A p = ∑ C ∈ boxCells P, boxPredMass w C p := by
  rw [boxPredMass_apply, ← biUnion_boxCells_tuples P, Finset.filter_biUnion,
    Finset.sum_biUnion]
  · rfl
  · exact (boxCells_pairwiseDisjoint P).mono fun C => Finset.filter_subset _ _

/-! ### Reindexing -/

/-- Transporting a box partition along an equivalence of index types. The carrier matches
because `(A.reindex e) j` is `A (e j)` definitionally. -/
def BoxPartition.reindex [∀ i, DecidableEq (V i)] {ι' : Type*} (e : ι' ≃ ι) {A : FiniteBox V}
    (P : BoxPartition A) : BoxPartition (A.reindex e) := fun j => P (e j)

@[simp] theorem BoxPartition.reindex_apply [∀ i, DecidableEq (V i)] {ι' : Type*} (e : ι' ≃ ι)
    {A : FiniteBox V} (P : BoxPartition A) (j : ι') : P.reindex e j = P (e j) := rfl

/-- **Reindexing carries the product cells across**, bijectively. -/
theorem boxCells_reindex [Fintype ι] [DecidableEq ι] {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    [∀ i, DecidableEq (V i)] (e : ι' ≃ ι) {A : FiniteBox V} (P : BoxPartition A) :
    boxCells (P.reindex e) = (boxCells P).image (FiniteBox.reindex e) := by
  ext D
  simp only [mem_boxCells, Finset.mem_image]
  constructor
  · -- `fun i => D (e.symm i)` does not typecheck: its value lies in `V (e (e.symm i))`, not
    -- `V i`. The tuple equivalence is what supplies the transport.
    intro hD
    refine ⟨Equiv.piCongrLeft (fun i => Finset (V i)) e D, fun i => ?_, ?_⟩
    · rw [← Equiv.apply_symm_apply e i, Equiv.piCongrLeft_apply_apply]
      exact hD (e.symm i)
    · funext j
      rw [FiniteBox.reindex_apply, Equiv.piCongrLeft_apply_apply]
  · rintro ⟨C, hC, rfl⟩ j
    exact hC (e j)

theorem card_boxCells_reindex [Fintype ι] [DecidableEq ι] {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] [∀ i, DecidableEq (V i)] (e : ι' ≃ ι) {A : FiniteBox V}
    (P : BoxPartition A) : (boxCells (P.reindex e)).card = (boxCells P).card := by
  rw [card_boxCells, card_boxCells]
  exact Fintype.prod_equiv e _ _ fun _ => rfl

/-! ### Refinement

`Q ≤ P` coordinatewise means `Q` is the finer partition, following `Partition/Basic.lean`. -/

/-- **Every cell of a finer box partition sits inside exactly one cell of the coarser one.**
Uniqueness needs no extra hypothesis: parts of a `Finpartition` are nonempty, so a containing
part is pinned by any point of the finer cell. -/
theorem existsUnique_parent_boxCell [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {A : FiniteBox V} {P Q : BoxPartition A} (hQP : ∀ i, Q i ≤ P i) {D : FiniteBox V}
    (hD : D ∈ boxCells Q) : ∃! C : FiniteBox V, C ∈ boxCells P ∧ ∀ i, D i ⊆ C i := by
  classical
  have hchoice : ∀ i, ∃ C ∈ (P i).parts, D i ⊆ C := fun i => hQP i (mem_boxCells.mp hD i)
  refine ⟨fun i => (hchoice i).choose,
    ⟨mem_boxCells.mpr fun i => (hchoice i).choose_spec.1,
      fun i => (hchoice i).choose_spec.2⟩, ?_⟩
  rintro C' ⟨hC', hsub'⟩
  funext i
  obtain ⟨v, hv⟩ := (Q i).nonempty_of_mem_parts (mem_boxCells.mp hD i)
  exact (P i).eq_of_mem_parts (mem_boxCells.mp hC' i) (hchoice i).choose_spec.1 (hsub' i hv)
    ((hchoice i).choose_spec.2 hv)

/-! ### Tests -/

section Tests

/-- Genuinely different carrier types in the two coordinates. -/
private abbrev VP : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Fin 3

private instance : ∀ i, DecidableEq (VP i)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | 1 => inferInstanceAs (DecidableEq (Fin 3))

private def bxP : FiniteBox VP
  | 0 => Finset.univ
  | 1 => Finset.univ

/-- **Genuinely unequal coordinate partitions.** The first coordinate is left whole and the
second is cut into singletons, so the two coordinates are not partitioned alike. -/
private def mixedP : BoxPartition bxP
  | 0 => Finpartition.indiscrete (by decide)
  | 1 => ⊥

-- Three product cells: one part in the first coordinate, three in the second.
example : (boxCells mixedP).card = 3 := by
  rw [card_boxCells, Fin.prod_univ_two]
  decide

-- **Heterogeneous carriers**, and the cells really do cover the box.
example : (boxCells mixedP).biUnion FiniteBox.tuples = bxP.tuples :=
  biUnion_boxCells_tuples mixedP

-- **An empty index type.** There is one cell, the empty box, and one tuple.
example (A : FiniteBox (fun _ : Fin 0 => Fin 3)) (P : BoxPartition A) :
    (boxCells P).card = 1 := by
  rw [card_boxCells, Finset.prod_of_isEmpty]

-- **An empty coordinate.** The box has no tuples, so every cell mass is `0` and so is the
-- total — with no positivity hypothesis anywhere.
example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ)
    (P : BoxPartition (fun i : Fin 2 => if i = 0 then (∅ : Finset (Fin 3)) else Finset.univ)) :
    ∑ C ∈ boxCells P, boxMass w C = 0 := by
  rw [← boxMass_eq_sum_boxCells w P]
  exact boxMass_of_eq_empty (i := 0) w (by simp)

/-- A weight that is **signed** and **nonuniform** both across coordinates and within each
coordinate. -/
private def wP : ∀ i, VP i → ℝ
  | 0, v => if v = 0 then -2 else 1
  | 1, v => if v = 0 then 3 else -1

-- **Signed, nonuniform weights.** The decomposition is an exact splitting of a finite sum, so it
-- survives weights that are negative and vary within a coordinate.
example : boxMass wP bxP = ∑ C ∈ boxCells mixedP, boxMass wP C :=
  boxMass_eq_sum_boxCells wP mixedP

-- …and that weight really is negative somewhere, so the example is not secretly a nonnegative
-- one, where the decomposition would be a weaker statement.
example : wP 0 0 = -2 := by norm_num [wP]
example : ¬ (0 : ℝ) ≤ wP 0 0 := by norm_num [wP]

-- **Predicate mass decomposes too.**
example (p : (∀ i, VP i) → Prop) [DecidablePred p] :
    boxPredMass (fun _ _ => (1 : ℝ)) bxP p
      = ∑ C ∈ boxCells mixedP, boxPredMass (fun _ _ => (1 : ℝ)) C p :=
  boxPredMass_eq_sum_boxCells _ mixedP p

-- **Coordinate swapping** preserves the cell count.
example (A : FiniteBox (fun _ : Fin 2 => Fin 3)) (P : BoxPartition A) :
    (boxCells (P.reindex (Equiv.swap 0 1))).card = (boxCells P).card :=
  card_boxCells_reindex (Equiv.swap 0 1) P

-- **A genuine strict refinement.** Singletons everywhere are strictly finer than `mixedP`,
-- which leaves the first coordinate whole — the two have different cell counts, so the
-- refinement is not an equality in disguise.
private def fineP : BoxPartition bxP := fun _ => ⊥

example : ∀ i, fineP i ≤ mixedP i := fun _ => bot_le

example : (boxCells fineP).card = 6 := by
  rw [card_boxCells, Fin.prod_univ_two]
  decide

example : (boxCells fineP).card ≠ (boxCells mixedP).card := by
  rw [card_boxCells, card_boxCells, Fin.prod_univ_two, Fin.prod_univ_two]
  decide

-- …yet both decompose the same total mass. This needs no refinement hypothesis at all: each
-- side is `boxMass w bxP` by its own decomposition, so the agreement is a consequence of the
-- two theorems rather than of `fineP` refining `mixedP`.
example (w : ∀ i, VP i → ℝ) :
    ∑ D ∈ boxCells fineP, boxMass w D = ∑ C ∈ boxCells mixedP, boxMass w C := by
  rw [← boxMass_eq_sum_boxCells w fineP, boxMass_eq_sum_boxCells w mixedP]

-- Every fine cell has a unique coarse parent.
example (D : FiniteBox VP) (hD : D ∈ boxCells fineP) :
    ∃! C : FiniteBox VP, C ∈ boxCells mixedP ∧ ∀ i, D i ⊆ C i :=
  existsUnique_parent_boxCell (fun _ => bot_le) hD

end Tests

end RegularityLemmata
