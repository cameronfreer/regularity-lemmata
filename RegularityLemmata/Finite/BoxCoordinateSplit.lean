/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.ProductBox
import RegularityLemmata.Finite.CoordinateSplit

/-!
# Boxes across a coordinate split

A `CoordinateSplit n` divides the coordinates into a chosen set and its complement. A box over
those coordinates divides with them: it restricts to a box on each side, the two restrictions
glue back to the original, and — because a box's mass is a product over coordinates — the mass
**factorizes** across the split.

## The adapter lives here, not in either parent

`Finite/ProductBox.lean` never mentions `CoordinateSplit`, and `Finite/CoordinateSplit.lean`
never mentions weights or boxes. Neither is a natural home for statements about both, and making
either import the other would tax every consumer that needs only one. This module imports both
and is imported by neither.

## No casts

The restriction of a box to a side is `fun i => A i.1`, and the value type works out on the nose:
for `i : σ.Left` the subtype's underlying coordinate is `i.1`, so `A i.1 : Finset (V i.1)` is
already what a box over `fun i : σ.Left => V i.1` requires. Gluing is a `dite` on membership, and
in each branch the index is definitionally the one the side's box expects. Consequently every
statement here is cast-free, matching the discipline `CoordinateSplit` itself follows.

## The factorization is a product identity, not a measure fact

`boxMass_glue` and `boxMass_split` come from `boxMass_eq_prod_finsetMass` together with
`Finset.prod_mul_prod_compl`: a product over all coordinates is the product over the chosen ones
times the product over the rest. Nothing about signs or normalization enters, so both hold for
**signed** weights, with no positivity and no nonemptiness hypothesis.

## Endpoints

An empty split puts everything on the right, and its left factor is the empty product `1`; a full
split is the mirror image. Both are stated, since they are exactly the cases where a consumer
might otherwise expect a degenerate `0`.
-/

namespace RegularityLemmata

namespace CoordinateSplit

variable {n : ℕ} {V : Fin n → Type*}

/-! ### Restricting a box to the two sides -/

/-- The box on the chosen coordinates. -/
def boxLeft (σ : CoordinateSplit n) (A : FiniteBox V) :
    FiniteBox (fun i : σ.Left => V i.1) := fun i => A i.1

/-- The box on the complementary coordinates. -/
def boxRight (σ : CoordinateSplit n) (A : FiniteBox V) :
    FiniteBox (fun i : σ.Right => V i.1) := fun i => A i.1

@[simp] theorem boxLeft_apply (σ : CoordinateSplit n) (A : FiniteBox V) (i : σ.Left) :
    σ.boxLeft A i = A i.1 := rfl

@[simp] theorem boxRight_apply (σ : CoordinateSplit n) (A : FiniteBox V) (i : σ.Right) :
    σ.boxRight A i = A i.1 := rfl

/-- **Gluing two side boxes into a box.** A `dite` on membership; in each branch the index is
definitionally the one that side's box expects, so no cast appears. -/
def boxGlue (σ : CoordinateSplit n) (AL : FiniteBox (fun i : σ.Left => V i.1))
    (AR : FiniteBox (fun i : σ.Right => V i.1)) : FiniteBox V :=
  fun i => if h : i ∈ σ.left then AL ⟨i, h⟩ else AR ⟨i, h⟩

@[simp] theorem boxGlue_apply_left (σ : CoordinateSplit n)
    (AL : FiniteBox (fun i : σ.Left => V i.1)) (AR : FiniteBox (fun i : σ.Right => V i.1))
    (i : σ.Left) : σ.boxGlue AL AR i.1 = AL i := by
  rw [boxGlue, dite_eq_left i.2]

@[simp] theorem boxGlue_apply_right (σ : CoordinateSplit n)
    (AL : FiniteBox (fun i : σ.Left => V i.1)) (AR : FiniteBox (fun i : σ.Right => V i.1))
    (i : σ.Right) : σ.boxGlue AL AR i.1 = AR i := by
  rw [boxGlue, dite_eq_right i.2]

@[simp] theorem boxLeft_boxGlue (σ : CoordinateSplit n)
    (AL : FiniteBox (fun i : σ.Left => V i.1)) (AR : FiniteBox (fun i : σ.Right => V i.1)) :
    σ.boxLeft (σ.boxGlue AL AR) = AL := funext fun i => boxGlue_apply_left σ AL AR i

@[simp] theorem boxRight_boxGlue (σ : CoordinateSplit n)
    (AL : FiniteBox (fun i : σ.Left => V i.1)) (AR : FiniteBox (fun i : σ.Right => V i.1)) :
    σ.boxRight (σ.boxGlue AL AR) = AR := funext fun i => boxGlue_apply_right σ AL AR i

/-- **Gluing the two restrictions recovers the box.** -/
@[simp] theorem boxGlue_boxLeft_boxRight (σ : CoordinateSplit n) (A : FiniteBox V) :
    σ.boxGlue (σ.boxLeft A) (σ.boxRight A) = A := by
  funext i
  rw [boxGlue]
  split <;> rfl

/-! ### Tuple membership across the split -/

/-- **A tuple lies in a box exactly when both of its halves lie in the corresponding side
boxes.** The membership counterpart of `splitEquiv`. -/
theorem mem_tuples_iff_split (σ : CoordinateSplit n) (A : FiniteBox V) (x : ∀ i, V i) :
    x ∈ A.tuples ↔
      σ.restrictLeft x ∈ (σ.boxLeft A).tuples ∧ σ.restrictRight x ∈ (σ.boxRight A).tuples := by
  simp only [FiniteBox.mem_tuples, boxLeft_apply, boxRight_apply]
  constructor
  · intro h
    exact ⟨fun i => h i.1, fun i => h i.1⟩
  · rintro ⟨hL, hR⟩ i
    by_cases hi : i ∈ σ.left
    · exact hL ⟨i, hi⟩
    · exact hR ⟨i, hi⟩

/-- The same statement read through `splitEquiv`, so the two halves are literally the components
of the transported tuple. -/
theorem mem_tuples_iff_splitEquiv (σ : CoordinateSplit n) (A : FiniteBox V) (x : ∀ i, V i) :
    x ∈ A.tuples ↔
      (σ.splitEquiv V x).1 ∈ (σ.boxLeft A).tuples ∧
        (σ.splitEquiv V x).2 ∈ (σ.boxRight A).tuples :=
  mem_tuples_iff_split σ A x

/-! ### Mass factorization

A box's mass is a product over coordinates, and a product over all coordinates splits as the
product over the chosen ones times the product over the rest. Nothing about signs enters, so
these hold for signed weights. -/

/-- **The mass of a box factorizes across a split.** -/
theorem boxMass_split (σ : CoordinateSplit n) (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass w A
      = boxMass (V := fun i : σ.Left => V i.1) (fun i => w i.1) (σ.boxLeft A)
        * boxMass (V := fun i : σ.Right => V i.1) (fun i => w i.1) (σ.boxRight A) := by
  rw [boxMass_eq_prod_finsetMass, boxMass_eq_prod_finsetMass, boxMass_eq_prod_finsetMass]
  rw [← Finset.prod_mul_prod_compl (M := ℝ) σ.left fun i => finsetMass (w i) (A i)]
  congr 1
  · exact (Finset.prod_coe_sort σ.left fun i => finsetMass (w i) (A i)).symm
  · exact Finset.prod_subtype (M := ℝ) (p := fun i => i ∉ σ.left) σ.leftᶜ
      (fun _ => Finset.mem_compl) fun i => finsetMass (w i) (A i)

/-- **The mass of a glued box is the product of the side masses.** -/
theorem boxMass_glue (σ : CoordinateSplit n) (w : ∀ i, V i → ℝ)
    (AL : FiniteBox (fun i : σ.Left => V i.1)) (AR : FiniteBox (fun i : σ.Right => V i.1)) :
    boxMass w (σ.boxGlue AL AR)
      = boxMass (V := fun i : σ.Left => V i.1) (fun i => w i.1) AL
        * boxMass (V := fun i : σ.Right => V i.1) (fun i => w i.1) AR := by
  rw [boxMass_split σ w, boxLeft_boxGlue, boxRight_boxGlue]

/-! ### Naturality -/

/-- **Swapping the split exchanges the two side boxes.** The index equivalences of
`CoordinateSplit` carry the correspondence, so this is cast-free. -/
theorem boxLeft_swap (σ : CoordinateSplit n) (A : FiniteBox V) (i : σ.swap.Left) :
    σ.swap.boxLeft A i = σ.boxRight A (σ.swapLeftEquiv i) := rfl

theorem boxRight_swap (σ : CoordinateSplit n) (A : FiniteBox V) (i : σ.swap.Right) :
    σ.swap.boxRight A i = σ.boxLeft A (σ.swapRightEquiv i) := rfl

/-- **The factorization is symmetric under swapping**, the two factors exchanging places. -/
theorem boxMass_split_swap (σ : CoordinateSplit n) (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass (V := fun i : σ.swap.Left => V i.1) (fun i => w i.1) (σ.swap.boxLeft A)
        * boxMass (V := fun i : σ.swap.Right => V i.1) (fun i => w i.1) (σ.swap.boxRight A)
      = boxMass (V := fun i : σ.Left => V i.1) (fun i => w i.1) (σ.boxLeft A)
        * boxMass (V := fun i : σ.Right => V i.1) (fun i => w i.1) (σ.boxRight A) := by
  rw [← boxMass_split σ.swap w A, ← boxMass_split σ w A]

/-- **Coordinate reindexing commutes with restriction to a side.** -/
theorem boxLeft_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) (A : FiniteBox V)
    (i : (σ.reindex π).Left) :
    (σ.reindex π).boxLeft (V := fun i => V (π i)) (fun i => A (π i)) i
      = σ.boxLeft A (σ.reindexLeftEquiv π i) := rfl

theorem boxRight_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) (A : FiniteBox V)
    (i : (σ.reindex π).Right) :
    (σ.reindex π).boxRight (V := fun i => V (π i)) (fun i => A (π i)) i
      = σ.boxRight A (σ.reindexRightEquiv π i) := rfl

/-! ### Endpoints

The empty and full splits are legal — `CoordinateSplit` makes properness a predicate, not a
field — and these are the statements a consumer needs so that a degenerate side reads as the
multiplicative unit rather than as `0`. -/

/-- **An empty split has no left coordinates**, so its left factor is the empty product `1`. -/
theorem boxMass_boxLeft_of_left_eq_empty (σ : CoordinateSplit n) (hσ : σ.left = ∅)
    (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass (V := fun i : σ.Left => V i.1) (fun i => w i.1) (σ.boxLeft A) = 1 := by
  -- Destructure first: `i`'s own type mentions `σ.left`, so rewriting there is not
  -- type-correct until the underlying coordinate is a plain variable.
  have : IsEmpty σ.Left := ⟨fun i => by
    obtain ⟨j, hj⟩ := i
    rw [hσ] at hj
    exact Finset.notMem_empty j hj⟩
  exact boxMass_of_isEmpty _ _

/-- …so an empty split leaves the mass on the right factor alone. -/
theorem boxMass_of_left_eq_empty (σ : CoordinateSplit n) (hσ : σ.left = ∅) (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) :
    boxMass w A = boxMass (V := fun i : σ.Right => V i.1) (fun i => w i.1) (σ.boxRight A) := by
  rw [boxMass_split σ w A, boxMass_boxLeft_of_left_eq_empty σ hσ, one_mul]

/-- **A full split has no right coordinates**, so its right factor is the empty product `1`. -/
theorem boxMass_boxRight_of_left_eq_univ (σ : CoordinateSplit n) (hσ : σ.left = Finset.univ)
    (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass (V := fun i : σ.Right => V i.1) (fun i => w i.1) (σ.boxRight A) = 1 := by
  have : IsEmpty σ.Right := ⟨fun i => by
    obtain ⟨j, hj⟩ := i
    rw [hσ] at hj
    exact hj (Finset.mem_univ j)⟩
  exact boxMass_of_isEmpty _ _

/-- …so a full split leaves the mass on the left factor alone. -/
theorem boxMass_of_left_eq_univ (σ : CoordinateSplit n) (hσ : σ.left = Finset.univ)
    (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass w A = boxMass (V := fun i : σ.Left => V i.1) (fun i => w i.1) (σ.boxLeft A) := by
  rw [boxMass_split σ w A, boxMass_boxRight_of_left_eq_univ σ hσ, mul_one]

end CoordinateSplit

/-! ### Tests -/

section Tests

open CoordinateSplit

/-- Genuinely different carrier types in the two coordinates, so the split is not homogeneous. -/
private abbrev VS : Fin 3 → Type
  | 0 => Fin 2
  | 1 => Fin 3
  | 2 => Fin 2

private def bxS : FiniteBox VS
  | 0 => Finset.univ
  | 1 => Finset.univ
  | 2 => Finset.univ

/-- A proper split: coordinate `1` on the left, coordinates `0` and `2` on the right. -/
private def σS : CoordinateSplit 3 := ⟨{1}⟩

example : σS.IsProper := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

-- **Gluing the restrictions recovers the box**, for an arbitrary box.
example (A : FiniteBox VS) : σS.boxGlue (σS.boxLeft A) (σS.boxRight A) = A :=
  boxGlue_boxLeft_boxRight σS A

-- **Tuple membership splits**, for an arbitrary box and tuple.
example (A : FiniteBox VS) (x : ∀ i, VS i) :
    x ∈ A.tuples ↔
      σS.restrictLeft x ∈ (σS.boxLeft A).tuples ∧
        σS.restrictRight x ∈ (σS.boxRight A).tuples :=
  mem_tuples_iff_split σS A x

-- **The mass factorizes**, for an arbitrary — possibly signed — weight.
example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass w A
      = boxMass (V := fun i : σS.Left => VS i.1) (fun i => w i.1) (σS.boxLeft A)
        * boxMass (V := fun i : σS.Right => VS i.1) (fun i => w i.1) (σS.boxRight A) :=
  boxMass_split σS w A

-- …and with counting weights the two factors are `3` and `2 * 2 = 4`, against a total of `12`.
example : boxMass (fun _ _ => (1 : ℝ)) bxS = 12 := by
  rw [boxMass_one, Fin.prod_univ_three]
  norm_num [bxS]

/-- A weight that is negative somewhere, to exercise the factorization with signed weights. -/
private def wS : ∀ i, VS i → ℝ
  | 0, v => if v = 0 then 2 else -1
  | 1, v => if v = 0 then 3 else -1
  | 2, v => if v = 0 then -2 else 1

example : wS 0 1 = -1 := by norm_num [wS]

example (A : FiniteBox VS) :
    boxMass wS A
      = boxMass (V := fun i : σS.Left => VS i.1) (fun i => wS i.1) (σS.boxLeft A)
        * boxMass (V := fun i : σS.Right => VS i.1) (fun i => wS i.1) (σS.boxRight A) :=
  boxMass_split σS wS A

-- **Swap naturality**: the two side boxes exchange, and the factorization is symmetric.
example (A : FiniteBox VS) (i : σS.swap.Left) :
    σS.swap.boxLeft A i = σS.boxRight A (σS.swapLeftEquiv i) := boxLeft_swap σS A i

example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass (V := fun i : σS.swap.Left => VS i.1) (fun i => w i.1) (σS.swap.boxLeft A)
        * boxMass (V := fun i : σS.swap.Right => VS i.1) (fun i => w i.1) (σS.swap.boxRight A)
      = boxMass (V := fun i : σS.Left => VS i.1) (fun i => w i.1) (σS.boxLeft A)
        * boxMass (V := fun i : σS.Right => VS i.1) (fun i => w i.1) (σS.boxRight A) :=
  boxMass_split_swap σS w A

-- **Coordinate-reindexing naturality.**
example (π : Equiv.Perm (Fin 3)) (A : FiniteBox VS) (i : (σS.reindex π).Left) :
    (σS.reindex π).boxLeft (V := fun i => VS (π i)) (fun i => A (π i)) i
      = σS.boxLeft A (σS.reindexLeftEquiv π i) := boxLeft_reindex σS π A i

/-! **The empty and full endpoints.** These are the cases where a degenerate side must read as
the multiplicative unit rather than as `0`. -/

private def emptySplit : CoordinateSplit 3 := ⟨∅⟩

private def fullSplit : CoordinateSplit 3 := ⟨Finset.univ⟩

example : ¬ emptySplit.IsProper := fun h => Finset.not_nonempty_empty h.1

example : ¬ fullSplit.IsProper := by
  rintro ⟨-, ⟨j, hj⟩⟩
  exact (CoordinateSplit.mem_right_iff.mp hj) (Finset.mem_univ j)

example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass (V := fun i : emptySplit.Left => VS i.1) (fun i => w i.1)
      (emptySplit.boxLeft A) = 1 :=
  boxMass_boxLeft_of_left_eq_empty emptySplit rfl w A

example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass w A
      = boxMass (V := fun i : emptySplit.Right => VS i.1) (fun i => w i.1)
        (emptySplit.boxRight A) :=
  boxMass_of_left_eq_empty emptySplit rfl w A

example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass (V := fun i : fullSplit.Right => VS i.1) (fun i => w i.1)
      (fullSplit.boxRight A) = 1 :=
  boxMass_boxRight_of_left_eq_univ fullSplit rfl w A

example (w : ∀ i, VS i → ℝ) (A : FiniteBox VS) :
    boxMass w A
      = boxMass (V := fun i : fullSplit.Left => VS i.1) (fun i => w i.1)
        (fullSplit.boxLeft A) :=
  boxMass_of_left_eq_univ fullSplit rfl w A

end Tests

end RegularityLemmata
