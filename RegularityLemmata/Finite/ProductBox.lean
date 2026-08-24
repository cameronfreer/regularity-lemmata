/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Heterogeneous weighted product boxes

A **box** over a coordinate-indexed family of carriers chooses a finset of allowed values in
each coordinate. Tuples carry the product of their coordinate weights, and the mass of a box
is the total weight of the tuples it contains.

## One notion of mass

`boxMass` is the **weighted sum over the tuples of the box**, and the product factorization is
the *theorem* `boxMass_eq_prod_finsetMass`. This is issue #83's binding shape, and it is what
makes predicate mass and density in later tranches a **restriction of the same construction**
rather than a second definition needing reconciliation.

There is deliberately no separate `sum_tupleWeight_eq_prod_sum`: with this primitive it would
be `boxMass_eq_prod_finsetMass` after unfolding, and the library does not carry two names for
one quantity. `boxMass_apply` is the definitional unfolding, since `boxMass` is a `def` and so
does not match a bare tuple sum syntactically.

## Instances, deliberately minimal

`FiniteBox` needs **no instances**, and `FiniteBox.reindex` needs none either.

`[DecidableEq ι]` is genuinely required by `Fintype.piFinset` — built from `Finset.univ.pi`,
so it must compare indices — and `boxMass` enumerates tuples, so it carries the instance.
Results that live purely on the product side (`boxMass_nonneg`, `boxMass_mono`,
`boxMass_of_eq_empty`) still need it only because they are stated about `boxMass`.

Decidable equality on the carriers `V i` is required nowhere in this file; fiberwise
`DecidableEq` belongs only on later operations that genuinely intersect, image, or union
tuple sets.

The index type is an arbitrary `Fintype`, not `Fin n`, which is what makes the
equivalence-based reindexing below expressible.

## No coordinate split here

Nothing in this file mentions `CoordinateSplit`. Restriction and gluing along a split, and the
factorization of a box mass across one, belong to a separate adapter module depending on both.
Keeping the core independent lets consumers that never split coordinates use boxes directly.
-/

namespace RegularityLemmata

variable {ι : Type*} {V : ι → Type*}

/-- A box: a finset of allowed values in each coordinate.

An `abbrev`, not a `def`: the alias must stay reducible so that `Fintype.piFinset` and
ordinary application see through it, exactly as `RectKernel` is an unbundled alias. -/
abbrev FiniteBox (V : ι → Type*) : Type _ := ∀ i, Finset (V i)

/-- The tuples of a box: those choosing an allowed value in every coordinate. -/
def FiniteBox.tuples [Fintype ι] [DecidableEq ι] (A : FiniteBox V) : Finset (∀ i, V i) :=
  Fintype.piFinset A

@[simp] theorem FiniteBox.mem_tuples [Fintype ι] [DecidableEq ι] {A : FiniteBox V}
    {x : ∀ i, V i} : x ∈ A.tuples ↔ ∀ i, x i ∈ A i :=
  Fintype.mem_piFinset

/-- **Reindexing a box along an equivalence of index types.** A canonical operation, named
rather than left as a raw lambda, so that consumers and later laws can speak about it. Needs
no instances. -/
def FiniteBox.reindex {ι' : Type*} (e : ι' ≃ ι) (A : FiniteBox V) :
    FiniteBox (fun j => V (e j)) := fun j => A (e j)

@[simp] theorem FiniteBox.reindex_apply {ι' : Type*} (e : ι' ≃ ι) (A : FiniteBox V) (j : ι') :
    A.reindex e j = A (e j) := rfl

/-- The weight of a tuple: the product of its coordinate weights. -/
def tupleWeight [Fintype ι] (w : ∀ i, V i → ℝ) (x : ∀ i, V i) : ℝ := ∏ i, w i (x i)

@[simp] theorem tupleWeight_apply [Fintype ι] (w : ∀ i, V i → ℝ) (x : ∀ i, V i) :
    tupleWeight w x = ∏ i, w i (x i) := rfl

/-- **The mass of a box**: the total weight of its tuples.

A weighted sum over tuples, so that predicate mass and density restrict it definitionally.
The product factorization is `boxMass_eq_prod_finsetMass`. -/
def boxMass [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V) : ℝ :=
  ∑ x ∈ A.tuples, tupleWeight w x

/-- The definitional unfolding. Needed because `boxMass` is a `def`, so a bare tuple sum does
not match it syntactically. -/
theorem boxMass_apply [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass w A = ∑ x ∈ A.tuples, tupleWeight w x := rfl

/-! ### Product factorization and finite Fubini -/

/-- **The fundamental identity.** A box's mass factors as the product of its coordinate
masses. `Finset.prod_univ_sum` read in this library's vocabulary: the mathematics is
Mathlib's, the formulation is the weighted one consumers need. -/
theorem boxMass_eq_prod_finsetMass [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxMass w A = ∏ i, finsetMass (w i) (A i) :=
  (Finset.prod_univ_sum A w).symm

/-- **Counting measure.** At unit weights the box mass is the number of tuples, the product of
the coordinate cardinalities. The generic specialization, so consumers need not rediscover it
from a concrete instance. -/
theorem boxMass_one [Fintype ι] [DecidableEq ι] (A : FiniteBox V) :
    boxMass (fun _ _ => (1 : ℝ)) A = ∏ i, ((A i).card : ℝ) := by
  rw [boxMass_eq_prod_finsetMass]
  exact Finset.prod_congr rfl fun i _ => finsetMass_one (A i)

/-! ### Endpoints and signs -/

/-- Nonnegative coordinate weights give a nonnegative box mass. Stated on the box's own
coordinate finsets, not globally, so a weight may be negative off the box. -/
theorem boxMass_nonneg [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v) : 0 ≤ boxMass w A := by
  rw [boxMass_eq_prod_finsetMass]
  exact Finset.prod_nonneg fun i _ => finsetMass_nonneg (hw i)

/-- **Monotone in the box**, given nonnegative weights on the **larger** one. As with
`finsetMass_mono`, the hypothesis must sit on the larger box: without it a bigger box can
carry less mass. -/
theorem boxMass_mono [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A B : FiniteBox V}
    (hw : ∀ i, ∀ v ∈ B i, 0 ≤ w i v) (hAB : ∀ i, A i ⊆ B i) :
    boxMass w A ≤ boxMass w B := by
  rw [boxMass_eq_prod_finsetMass, boxMass_eq_prod_finsetMass]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · exact finsetMass_nonneg fun v hv => hw i v (hAB i hv)
  · exact finsetMass_mono (hw i) (hAB i)

/-- **An empty coordinate empties the box.** No guard is needed: the tuple set is genuinely
empty, so the mass is `0` by the sum, and by the product it is `0` because that factor is. -/
@[simp] theorem boxMass_of_eq_empty [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    {A : FiniteBox V} {i : ι} (hi : A i = ∅) : boxMass w A = 0 := by
  rw [boxMass_eq_prod_finsetMass]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hi, finsetMass_empty]

/-- The empty index type is the unit of the construction: there is exactly one tuple, the
empty one, and its weight is the empty product `1`. -/
@[simp] theorem boxMass_of_isEmpty [Fintype ι] [DecidableEq ι] [IsEmpty ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxMass w A = 1 := by
  rw [boxMass_eq_prod_finsetMass, Finset.prod_of_isEmpty]

/-! ### Reindexing along an equivalence

The index type is an arbitrary `Fintype`, so relabelling coordinates is an equivalence of
index types rather than a permutation of `Fin n`. Both the carrier family and the weights
transport with it. -/

/-- **Reindexing preserves box mass.** Transporting a box along `e : ι' ≃ ι` — carriers,
weights, and coordinate finsets together — leaves the mass unchanged. -/
theorem boxMass_reindex {ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (w : ∀ i, V i → ℝ) (A : FiniteBox V) :
    boxMass (V := fun j => V (e j)) (fun j => w (e j)) (A.reindex e) = boxMass w A := by
  rw [boxMass_eq_prod_finsetMass, boxMass_eq_prod_finsetMass]
  exact Fintype.prod_equiv e _ _ fun _ => rfl

/-! ### Tests and adversarial examples -/

section Tests

/-- Genuinely different carrier types in the two coordinates. -/
private abbrev VH : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Fin 3

/-- The full box over that heterogeneous family: `Fin 2 × Fin 3`. -/
private def bxH : FiniteBox VH
  | 0 => Finset.univ
  | 1 => Finset.univ

-- **Heterogeneous carriers.** The two coordinates have different types, which is the point of
-- a dependent carrier family; a `Fin n → Type` constant family would not exercise it.
example : FiniteBox VH := bxH

-- Counting weights: the box mass is the number of tuples, `2 * 3 = 6`.
example : boxMass (fun _ _ => (1 : ℝ)) bxH = 6 := by
  rw [boxMass_one, Fin.prod_univ_two]
  norm_num [bxH]

-- **An empty coordinate zeroes the mass**, with no positivity or nonemptiness hypothesis.
example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ) :
    boxMass w (fun i => if i = 0 then (∅ : Finset (Fin 3)) else Finset.univ) = 0 :=
  boxMass_of_eq_empty (i := 0) w (by simp)

-- **The empty index type gives mass `1`**, not `0`: there is one tuple, and the empty
-- product is `1`. A "mass is zero when there is nothing" reading would be wrong here.
example (w : ∀ i : Fin 0, (fun _ : Fin 0 => Fin 3) i → ℝ)
    (A : FiniteBox (fun _ : Fin 0 => Fin 3)) : boxMass w A = 1 :=
  boxMass_of_isEmpty w A

-- **Negative weights are allowed off the box.** Nonnegativity is required only on the box's
-- own coordinate finsets, so this mass is still nonnegative even though `w` is negative at a
-- value the box excludes.
example :
    0 ≤ boxMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
      (fun _ : Fin 2 => ({0} : Finset (Fin 3))) := by
  refine boxMass_nonneg ?_
  intro i v hv
  rw [Finset.mem_singleton] at hv
  simp [hv]

-- …and the mass is genuinely computed from the retained value only: `2 * 2 = 4`.
example :
    boxMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
      (fun _ : Fin 2 => ({0} : Finset (Fin 3))) = 4 := by
  rw [boxMass_eq_prod_finsetMass, Fin.prod_univ_two]
  norm_num [finsetMass]

-- Reindexing along the swap of two coordinates preserves the mass.
example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ)
    (A : FiniteBox (fun _ : Fin 2 => Fin 3)) :
    boxMass (V := fun j => (fun _ : Fin 2 => Fin 3) (Equiv.swap 0 1 j))
        (fun j => w (Equiv.swap 0 1 j)) (A.reindex (Equiv.swap 0 1))
      = boxMass w A :=
  boxMass_reindex (Equiv.swap 0 1) w A

end Tests

end RegularityLemmata
