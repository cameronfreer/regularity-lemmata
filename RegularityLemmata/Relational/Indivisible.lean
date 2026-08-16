/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPattern
import RegularityLemmata.Partition.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Indivisibility of a finite relational model over a partition

A relation is **indivisible** for a partition `P` of a finite ground set `s` when its truth
value on a tuple over `s` depends only on the tuple of cells the entries lie in; a model is
indivisible when every one of its relation symbols is. This is the hypothesis under which a
model is the *blow-up* of the induced structure on its cells — the notion Malliaris and
Shelah extract from stable regularity (arXiv:1102.3904) and the one Ackerman, Freer, and
Patel use for invariant measures on blow-ups (arXiv:1712.09305).

Everything here is **arbitrary-arity**: `IsIndivisible` is stated for a relation on
`Fin n → V` for an arbitrary `n`, and `FiniteRelModel.IsIndivisibleFor` quantifies over every
arity of the language. Nothing in the file specializes to binary structure, so it survives
the later generalization of the binary regularity layer.

The content is: the defining transport of truth values (`IsIndivisible.iff_of_part_eq`), cell
constancy in the "all tuples in the box agree" form (`IsIndivisible.const_on_cells`,
`IsIndivisible.const_on_cellBox`), the induced relation on tuples of cells (`quotientRel`)
with both round-trip directions, monotonicity under refinement (`IsIndivisible.mono_of_le`;
in mathlib's order `Q ≤ P` means `Q` is *finer*, see `ARCHITECTURE.md`), and the
`Fintype.piFinset` tiling of the tuples over `s` by cell boxes, which is what later counting
arguments consume.

**Deliberately not claimed.** Nothing here is stability-theoretic: no stability, order
property, or Littlestone hypothesis appears, and no *existence* of a nontrivial indivisible
partition is proved — indivisibility is always an assumption on the pair `(N, P)`. No
blow-up model is constructed either; `quotientRel` is the induced relation on cells, not a
`FiniteRelModel` on `P.parts`. Approximate (`ε`-) indivisibility is a separate notion and is
not defined here.

**Nullary arity.** Arity zero is free: a relation on the unique empty tuple is indivisible
for every partition (`isIndivisible_of_arity_zero`), so `IsIndivisibleFor` says nothing at
arity `0` (`FiniteRelModel.isIndivisibleFor_iff_pos`). The arity-zero bookkeeping stays with
the existing `NullaryCompatible` of `Relational/BinaryPattern.lean` — no competing predicate
is introduced. `quotientRel_zero` identifies the arity-zero quotient with the nullary datum
itself, and `nullaryCompatible_iff_quotientRel` states the resulting equivalence.

**Placement.** This file lives above `Partition/`, not in `Finite/`: as
`Finite/HomogeneousPair.lean` records, importing `Finpartition` into the finite layer would
invert the library's dependency direction.
-/

namespace RegularityLemmata

open Finset FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {n : ℕ}

/-! ### The predicate -/

/-- A relation is indivisible for `P` when its value depends only on the parts of its
arguments. -/
def IsIndivisible {V : Type*} [DecidableEq V] {s : Finset V} (P : Finpartition s) {n : ℕ}
    (R : (Fin n → V) → Prop) : Prop :=
  ∀ x y : Fin n → V, (∀ i, x i ∈ s) → (∀ i, y i ∈ s) →
    (∀ i, P.part (x i) = P.part (y i)) → (R x ↔ R y)

/-- A model is indivisible for `P` when every one of its relations is. Method style:
`N.IsIndivisibleFor P`. -/
def FiniteRelModel.IsIndivisibleFor {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}
    [DecidableEq V] {s : Finset V} (N : FiniteRelModel L V) (P : Finpartition s) : Prop :=
  ∀ n (R : L.Relations n), IsIndivisible P (N.Holds R)

variable {P Q : Finpartition s} {R : (Fin n → V) → Prop}

/-- Indivisibility is decidable on a finite carrier: it is a bounded quantification over
tuples. This is what makes the small `Fin` tests below kernel-checkable. -/
instance decidableIsIndivisible [Fintype V] (P : Finpartition s) (R : (Fin n → V) → Prop)
    [DecidablePred R] : Decidable (IsIndivisible P R) :=
  inferInstanceAs (Decidable (∀ x y : Fin n → V, (∀ i, x i ∈ s) → (∀ i, y i ∈ s) →
    (∀ i, P.part (x i) = P.part (y i)) → (R x ↔ R y)))

/-- The defining transport: entrywise equal parts transports the truth value. -/
theorem IsIndivisible.iff_of_part_eq (h : IsIndivisible P R) {x y : Fin n → V}
    (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s) (hpart : ∀ i, P.part (x i) = P.part (y i)) :
    R x ↔ R y :=
  h x y hx hy hpart

/-- The relation of a single symbol of an indivisible model is indivisible. -/
theorem FiniteRelModel.IsIndivisibleFor.rel {L : FirstOrder.Language} [FiniteRelational L]
    {N : FiniteRelModel L V} (h : N.IsIndivisibleFor P) {m : ℕ} (S : L.Relations m) :
    IsIndivisible P (N.Holds S) :=
  h m S

/-! ### Cell constancy -/

/-- **Cell constancy.** On a box of cells an indivisible relation is constant: any two tuples
with the same entrywise cells agree. -/
theorem IsIndivisible.const_on_cells (h : IsIndivisible P R) {C : Fin n → Finset V}
    (hC : ∀ i, C i ∈ P.parts) {x y : Fin n → V} (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ C i) :
    R x ↔ R y :=
  h x y (fun i ↦ P.le (hC i) (hx i)) (fun i ↦ P.le (hC i) (hy i))
    fun i ↦ (P.part_eq_of_mem (hC i) (hx i)).trans (P.part_eq_of_mem (hC i) (hy i)).symm

/-- Cell constancy in `Fintype.piFinset` form: the cell box `Fintype.piFinset C` is a set on
which an indivisible relation is constant. -/
theorem IsIndivisible.const_on_cellBox (h : IsIndivisible P R) {C : Fin n → Finset V}
    (hC : ∀ i, C i ∈ P.parts) {x y : Fin n → V} (hx : x ∈ Fintype.piFinset C)
    (hy : y ∈ Fintype.piFinset C) : R x ↔ R y :=
  h.const_on_cells hC (Fintype.mem_piFinset.mp hx) (Fintype.mem_piFinset.mp hy)

/-! ### The induced relation on tuples of cells -/

/-- The relation induced on `P.parts`: a tuple of cells is related when some (equivalently,
under indivisibility, every) tuple of representatives is. -/
def quotientRel (P : Finpartition s) {n : ℕ} (R : (Fin n → V) → Prop)
    (C : Fin n → P.parts) : Prop :=
  ∃ x : Fin n → V, (∀ i, x i ∈ (C i : Finset V)) ∧ R x

/-- Cells are recovered from any tuple of representatives — no indivisibility needed. -/
theorem part_eq_of_mem_cells {C : Fin n → P.parts} {x : Fin n → V}
    (hx : ∀ i, x i ∈ (C i : Finset V)) (i : Fin n) : P.part (x i) = (C i : Finset V) :=
  P.part_eq_of_mem (C i).2 (hx i)

/-- **Round trip, cells to tuples.** The induced relation at a tuple of cells is the original
relation at any tuple of representatives. -/
theorem IsIndivisible.quotientRel_iff (h : IsIndivisible P R) (C : Fin n → P.parts)
    {x : Fin n → V} (hx : ∀ i, x i ∈ (C i : Finset V)) : quotientRel P R C ↔ R x := by
  constructor
  · rintro ⟨y, hy, hRy⟩
    exact (h.const_on_cells (fun i ↦ (C i).2) hy hx).mp hRy
  · exact fun hR ↦ ⟨x, hx, hR⟩

/-- **Round trip, tuples to cells.** The induced relation at the tuple of parts of a tuple
over `s` is the original relation there. -/
theorem IsIndivisible.quotientRel_part (h : IsIndivisible P R) {x : Fin n → V}
    (hx : ∀ i, x i ∈ s) :
    quotientRel P R (fun i ↦ ⟨P.part (x i), P.part_mem.mpr (hx i)⟩) ↔ R x :=
  h.quotientRel_iff _ fun i ↦ P.mem_part (hx i)

/-- Under indivisibility the existential induced relation is also the universal one: parts
are nonempty, so "some representative tuple" and "every representative tuple" agree. -/
theorem IsIndivisible.quotientRel_iff_forall (h : IsIndivisible P R) (C : Fin n → P.parts) :
    quotientRel P R C ↔ ∀ x : Fin n → V, (∀ i, x i ∈ (C i : Finset V)) → R x := by
  refine ⟨fun hq x hx ↦ (h.quotientRel_iff C hx).mp hq, fun hall ↦ ?_⟩
  choose x hx using fun i ↦ P.nonempty_of_mem_parts (C i).2
  exact ⟨x, hx, hall x hx⟩

/-! ### Monotonicity under refinement -/

/-- **Refinement monotonicity.** In mathlib's order `Q ≤ P` means `Q` is finer than `P`, and
a finer partition distinguishes more, so indivisibility passes down. -/
theorem IsIndivisible.mono_of_le (h : IsIndivisible P R) (hQP : Q ≤ P) : IsIndivisible Q R := by
  intro x y hx hy hpart
  refine h x y hx hy fun i ↦ ?_
  obtain ⟨A, hA, hsub⟩ := hQP (Q.part_mem.mpr (hx i))
  have hyi : y i ∈ Q.part (x i) := by rw [hpart i]; exact Q.mem_part (hy i)
  exact (P.part_eq_of_mem hA (hsub (Q.mem_part (hx i)))).trans
    (P.part_eq_of_mem hA (hsub hyi)).symm

/-- Refinement monotonicity at the level of models. -/
theorem FiniteRelModel.IsIndivisibleFor.mono_of_le {L : FirstOrder.Language} [FiniteRelational L]
    {N : FiniteRelModel L V} (h : N.IsIndivisibleFor P) (hQP : Q ≤ P) : N.IsIndivisibleFor Q :=
  fun m S ↦ (h m S).mono_of_le hQP

/-! ### The cell-box tiling -/

/-- Cell boxes over distinct tuples of cells are disjoint. -/
theorem disjoint_piFinset_of_ne {C D : Fin n → Finset V} (hC : ∀ i, C i ∈ P.parts)
    (hD : ∀ i, D i ∈ P.parts) (hCD : C ≠ D) :
    Disjoint (Fintype.piFinset C) (Fintype.piFinset D) := by
  obtain ⟨i, hi⟩ : ∃ i, C i ≠ D i := by
    by_contra hcon
    push Not at hcon
    exact hCD (funext hcon)
  refine Finset.disjoint_left.mpr fun x hxC hxD ↦ ?_
  rw [Fintype.mem_piFinset] at hxC hxD
  exact Finset.disjoint_left.mp (P.disjoint (hC i) (hD i) hi) (hxC i) (hxD i)

/-- **The tiling.** The tuples over `s` are the union of the cell boxes. -/
theorem piFinset_const_eq_biUnion (P : Finpartition s) (n : ℕ) :
    (Fintype.piFinset fun _ : Fin n ↦ s)
      = (Fintype.piFinset fun _ : Fin n ↦ P.parts).biUnion fun C ↦ Fintype.piFinset C := by
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_biUnion]
  refine ⟨fun hx ↦ ⟨fun i ↦ P.part (x i), fun i ↦ P.part_mem.mpr (hx i),
    fun i ↦ P.mem_part (hx i)⟩, ?_⟩
  rintro ⟨C, hC, hx⟩
  exact fun i ↦ P.le (hC i) (hx i)

/-- **The tiling, counting form.** The number of tuples over `s` is the sum of the cell-box
sizes — the shape later counting arguments consume. -/
theorem card_piFinset_const (P : Finpartition s) (n : ℕ) :
    (Fintype.piFinset fun _ : Fin n ↦ s).card
      = ∑ C ∈ Fintype.piFinset fun _ : Fin n ↦ P.parts, (Fintype.piFinset C).card := by
  rw [piFinset_const_eq_biUnion P n]
  refine Finset.card_biUnion fun C hC D hD hCD ↦ ?_
  simp only [Finset.mem_coe, Fintype.mem_piFinset] at hC hD
  exact disjoint_piFinset_of_ne hC hD hCD

/-! ### Degenerate cases -/

/-- **Arity zero is free.** There is exactly one empty tuple, so every nullary relation is
indivisible for every partition. -/
theorem isIndivisible_of_arity_zero (P : Finpartition s) (R : (Fin 0 → V) → Prop) :
    IsIndivisible P R := fun x y _ _ _ ↦ by
  rw [show x = y from funext fun i ↦ i.elim0]

/-- **The empty ground set.** Over a partition of `∅` there are no tuples to divide, so every
relation is indivisible at every arity. -/
theorem isIndivisible_of_empty (P : Finpartition (∅ : Finset V)) (R : (Fin n → V) → Prop) :
    IsIndivisible P R := by
  cases n with
  | zero => exact isIndivisible_of_arity_zero P R
  | succ m => exact fun _ _ hx _ _ ↦ absurd (hx 0) (by simp)

/-- **The discrete partition.** Every part of `⊥` is a singleton, so every relation is
indivisible for it: indivisibility is a vacuous requirement at the finest partition. -/
theorem isIndivisible_bot (R : (Fin n → V) → Prop) : IsIndivisible (⊥ : Finpartition s) R := by
  intro x y hx hy hpart
  have hpt : ∀ a ∈ s, (⊥ : Finpartition s).part a = {a} := fun a ha ↦
    Finpartition.part_eq_of_mem _ (Finpartition.mem_bot_iff.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_singleton_self a)
  refine iff_of_eq (congrArg R (funext fun i ↦ ?_))
  exact Finset.singleton_injective
    ((hpt (x i) (hx i)).symm.trans ((hpart i).trans (hpt (y i) (hy i))))

/-- Arity zero contributes nothing to model indivisibility. -/
theorem FiniteRelModel.isIndivisibleFor_iff_pos {L : FirstOrder.Language} [FiniteRelational L]
    (N : FiniteRelModel L V) (P : Finpartition s) :
    N.IsIndivisibleFor P ↔ ∀ m, 0 < m → ∀ S : L.Relations m, IsIndivisible P (N.Holds S) := by
  refine ⟨fun h m _ S ↦ h m S, fun h m S ↦ ?_⟩
  cases m with
  | zero => exact isIndivisible_of_arity_zero P _
  | succ k => exact h _ k.succ_pos S

/-! ### The nullary layer, through `NullaryCompatible` -/

/-- The arity-zero induced relation **is** the nullary datum of the model: on the unique empty
tuple of cells it says exactly that the nullary relation holds. -/
theorem quotientRel_zero {L : FirstOrder.Language} [FiniteRelational L] (N : FiniteRelModel L V)
    (P : Finpartition s) (S : L.Relations 0) (C : Fin 0 → P.parts) :
    quotientRel P (N.Holds S) C ↔ N.Holds S Fin.elim0 := by
  refine ⟨?_, fun h ↦ ⟨Fin.elim0, fun i ↦ i.elim0, h⟩⟩
  rintro ⟨x, -, hR⟩
  rwa [show x = Fin.elim0 from funext fun i ↦ i.elim0] at hR

/-- **The nullary layer is exactly `NullaryCompatible`** (`Relational/BinaryPattern.lean`):
two models agree nullarily iff their arity-zero induced relations agree, over any partitions
of any ground sets. Indivisibility never touches this layer, so no competing nullary
predicate is introduced here. -/
theorem nullaryCompatible_iff_quotientRel {L : FirstOrder.Language} [FiniteRelational L]
    {W : Type*} [DecidableEq W] {t : Finset W} (M : FiniteRelModel L W)
    (N : FiniteRelModel L V) (Q' : Finpartition t) (P : Finpartition s) :
    NullaryCompatible M N ↔ ∀ S : L.Relations 0, ∀ (C : Fin 0 → Q'.parts) (D : Fin 0 → P.parts),
      (quotientRel Q' (M.Holds S) C ↔ quotientRel P (N.Holds S) D) := by
  refine ⟨fun h S C D ↦ ?_, fun h S ↦ ?_⟩
  · rw [quotientRel_zero, quotientRel_zero]
    exact h S
  · have := h S (fun i ↦ i.elim0) fun i ↦ i.elim0
    rwa [quotientRel_zero, quotientRel_zero] at this

/-! ### Tests and adversarial examples -/

section Tests

/-- Parity on `Fin 4`, the running nondegenerate partition: two cells, evens and odds. -/
private abbrev parityPart : Finpartition (Finset.univ : Finset (Fin 4)) :=
  predicatePartition (fun a : Fin 4 ↦ (a : ℕ) % 2 = 0) Finset.univ

-- Nondegenerate positive: "same parity" is indivisible for the parity partition (kernel
-- decide over all 16 × 16 pairs of `Fin 2` tuples).
example : IsIndivisible parityPart
    (fun x : Fin 2 → Fin 4 ↦ (x 0 : ℕ) % 2 = (x 1 : ℕ) % 2) := by decide

-- Nondegenerate negative: equality is NOT indivisible for the parity partition — the cells
-- do not see it. This is the adversarial companion to the previous test.
example : ¬IsIndivisible parityPart (fun x : Fin 2 → Fin 4 ↦ x 0 = x 1) := by decide

-- The discrete partition divides nothing: equality is indivisible there (`isIndivisible_bot`
-- checked concretely).
example : IsIndivisible (⊥ : Finpartition (Finset.univ : Finset (Fin 3)))
    (fun x : Fin 2 → Fin 3 ↦ x 0 = x 1) := by decide

-- …and the indiscrete partition divides everything: equality fails there.
example : ¬IsIndivisible (⊤ : Finpartition (Finset.univ : Finset (Fin 3)))
    (fun x : Fin 2 → Fin 3 ↦ x 0 = x 1) := by decide

-- DEGENERATE: arity zero. Both a `decide` instance and the general theorem, on a partition
-- that does divide things (so the content is arity, not the partition).
example : IsIndivisible parityPart (fun _ : Fin 0 → Fin 4 ↦ True) := by decide

example : IsIndivisible parityPart (fun _ : Fin 0 → Fin 4 ↦ False) :=
  isIndivisible_of_arity_zero _ _

-- DEGENERATE: the empty ground set, at a POSITIVE arity (where the tuple hypotheses are the
-- ones that fail), by `decide` and by the general theorem.
example : IsIndivisible (⊥ : Finpartition (∅ : Finset (Fin 3)))
    (fun x : Fin 1 → Fin 3 ↦ x 0 = 0) := by decide

example : IsIndivisible (⊤ : Finpartition (∅ : Finset (Fin 3)))
    (fun x : Fin 2 → Fin 3 ↦ x 0 = x 1) :=
  isIndivisible_of_empty _ _

-- The tiling, concretely: 4² tuples over `Fin 4` split as 2² boxes of 2² tuples each.
example : (Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 4))).card = 16 := by
  decide

example : (∑ C ∈ Fintype.piFinset fun _ : Fin 2 ↦ parityPart.parts,
    (Fintype.piFinset C).card) = 16 := by decide

-- The tiling theorem itself, as a statement-level instance on that data.
example : (Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 4))).card
    = ∑ C ∈ Fintype.piFinset fun _ : Fin 2 ↦ parityPart.parts, (Fintype.piFinset C).card :=
  card_piFinset_const _ _

-- Refinement monotonicity, statement-level: `⊥` is finer than every partition.
example (R : (Fin 2 → Fin 4) → Prop) (h : IsIndivisible parityPart R) :
    IsIndivisible (⊥ : Finpartition (Finset.univ : Finset (Fin 4))) R :=
  h.mono_of_le bot_le

-- The nullary connection: `NullaryCompatible` of a model with itself is exactly the
-- agreement of the arity-zero induced relations (no new nullary predicate).
example (N : FiniteRelModel (singleRelLang 0) (Fin 4)) :
    NullaryCompatible N N ↔ ∀ S : (singleRelLang 0).Relations 0,
      ∀ C D : Fin 0 → parityPart.parts,
        (quotientRel parityPart (N.Holds S) C ↔ quotientRel parityPart (N.Holds S) D) :=
  nullaryCompatible_iff_quotientRel N N parityPart parityPart

end Tests

end RegularityLemmata
