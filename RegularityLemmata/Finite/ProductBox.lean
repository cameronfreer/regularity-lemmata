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
the *theorem* `boxMass_eq_prod_finsetMass`. Taking the sum as primitive is what makes a mass
restricted to a subfamily of tuples — a predicate mass, a density — a **restriction of the same
construction** rather than a second definition needing reconciliation with this one.

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
`DecidableEq` belongs only on operations that genuinely intersect, image, or union tuple sets.

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
rather than left as a raw lambda, so that consumers and laws about relabelling can speak about
it. Needs no instances. -/
def FiniteBox.reindex {ι' : Type*} (e : ι' ≃ ι) (A : FiniteBox V) :
    FiniteBox (fun j => V (e j)) := fun j => A (e j)

@[simp] theorem FiniteBox.reindex_apply {ι' : Type*} (e : ι' ≃ ι) (A : FiniteBox V) (j : ι') :
    A.reindex e j = A (e j) := rfl

/-- The weight of a tuple: the product of its coordinate weights. -/
def tupleWeight [Fintype ι] (w : ∀ i, V i → ℝ) (x : ∀ i, V i) : ℝ := ∏ i, w i (x i)

@[simp] theorem tupleWeight_apply [Fintype ι] (w : ∀ i, V i → ℝ) (x : ∀ i, V i) :
    tupleWeight w x = ∏ i, w i (x i) := rfl

/-- **The mass of a box**: the total weight of its tuples.

A weighted sum over tuples, so that a mass restricted to a subfamily of tuples restricts this
one definitionally. The product factorization is `boxMass_eq_prod_finsetMass`. -/
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

/-! ### Predicate mass and density

A predicate selects a subfamily of a box's tuples. Its mass is the **same weighted sum** over
that subfamily, which is what taking the tuple sum as primitive was for: there is one notion of
mass here, restricted, not a second notion to reconcile.

The hypothesis boundary is deliberate and worth stating in one place.

* `boxPredMass` itself, its true/false endpoints, and the **complement identity** need no sign or
  mass hypothesis at all. The complement identity is an exact splitting of a finite sum, so it
  holds for signed weights.
* Monotonicity in the predicate, and the bound by the total mass, need **nonnegative weights on
  the box** — with signed weights a larger subfamily can carry less mass.
* `boxDensity` divides, guard-free: a zero total mass gives `0`, since `x / 0 = 0`.
* `0 ≤ boxDensity ≤ 1` therefore needs **only** nonnegativity, with no positive-mass side
  condition, because the zero-mass endpoint lands inside the interval rather than outside it.
* `boxDensity_true` and the complement-density identities are the statements that genuinely need
  `0 < boxMass`: at zero mass they would read `0 = 1`. -/

variable {p q : (∀ i, V i) → Prop}

/-- **The mass of the tuples satisfying a predicate.** A restriction of `boxMass` to a subfamily
of the tuples, not a second construction. -/
def boxPredMass [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] : ℝ :=
  ∑ x ∈ A.tuples.filter p, tupleWeight w x

theorem boxPredMass_apply [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] :
    boxPredMass w A p = ∑ x ∈ A.tuples.filter p, tupleWeight w x := rfl

@[simp] theorem boxPredMass_true [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxPredMass w A (fun _ => True) = boxMass w A := by
  rw [boxPredMass, Finset.filter_true, boxMass_apply]

@[simp] theorem boxPredMass_false [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxPredMass w A (fun _ => False) = 0 := by
  rw [boxPredMass, Finset.filter_false, Finset.sum_empty]

/-- **The complement identity is exact and guard-free.** It splits a finite sum, so it needs
neither nonnegativity nor positive mass and holds for signed weights. -/
theorem boxPredMass_add_compl [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] :
    boxPredMass w A p + boxPredMass w A (fun x => ¬ p x) = boxMass w A :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-- A tuple whose coordinate weights are all nonnegative has nonnegative weight. -/
theorem tupleWeight_nonneg [Fintype ι] {w : ∀ i, V i → ℝ} {x : ∀ i, V i}
    (hw : ∀ i, 0 ≤ w i (x i)) : 0 ≤ tupleWeight w x :=
  Finset.prod_nonneg fun i _ => hw i

theorem boxPredMass_nonneg [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v) : 0 ≤ boxPredMass w A p :=
  Finset.sum_nonneg fun x hx => tupleWeight_nonneg fun i =>
    hw i (x i) (FiniteBox.mem_tuples.mp (Finset.mem_filter.mp hx).1 i)

/-- **Monotone in the predicate**, given nonnegative weights on the box. Without that hypothesis
a larger subfamily can carry less mass. -/
theorem boxPredMass_mono [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] [DecidablePred q] (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v)
    (hpq : ∀ x ∈ A.tuples, p x → q x) : boxPredMass w A p ≤ boxPredMass w A q := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x hx _ => ?_)
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hpq x hx.1 hx.2⟩
  · exact tupleWeight_nonneg fun i =>
      hw i (x i) (FiniteBox.mem_tuples.mp (Finset.mem_filter.mp hx).1 i)

/-- A predicate mass never exceeds the total, given nonnegative weights on the box. -/
theorem boxPredMass_le_boxMass [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v) : boxPredMass w A p ≤ boxMass w A := by
  rw [boxPredMass, boxMass_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x hx _ => tupleWeight_nonneg fun i => hw i (x i) (FiniteBox.mem_tuples.mp hx i))

@[simp] theorem boxPredMass_of_eq_empty [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    {A : FiniteBox V} [DecidablePred p] {i : ι} (hi : A i = ∅) : boxPredMass w A p = 0 := by
  rw [boxPredMass, Finset.filter_eq_empty_iff.mpr, Finset.sum_empty]
  intro x hx
  exact absurd (FiniteBox.mem_tuples.mp hx i) (by rw [hi]; exact Finset.notMem_empty _)

/-- **The density of a predicate on a box.** Guard-free: a zero-mass box gives `0`, by the
library's `x / 0 = 0` convention, so no nonemptiness or positivity hypothesis is needed to write
it down. -/
noncomputable def boxDensity [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] : ℝ :=
  boxPredMass w A p / boxMass w A

theorem boxDensity_apply [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] :
    boxDensity w A p = boxPredMass w A p / boxMass w A := rfl

@[simp] theorem boxDensity_of_boxMass_eq_zero [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ}
    {A : FiniteBox V} [DecidablePred p] (h : boxMass w A = 0) : boxDensity w A p = 0 := by
  rw [boxDensity, h, div_zero]

/-- **`False` has density `0` with no hypothesis**, because its mass is `0` and `0 / m = 0` for
every `m`, including `m = 0`. -/
@[simp] theorem boxDensity_false [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxDensity w A (fun _ => False) = 0 := by
  rw [boxDensity, boxPredMass_false, zero_div]

/-- **`True` has density `1` only under positive mass.** At zero mass the guard-free convention
gives `0`, and the statement would read `0 = 1`. -/
theorem boxDensity_true_of_pos [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    (h : 0 < boxMass w A) : boxDensity w A (fun _ => True) = 1 := by
  rw [boxDensity, boxPredMass_true, div_self (ne_of_gt h)]

theorem boxDensity_nonneg [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v) : 0 ≤ boxDensity w A p :=
  div_nonneg (boxPredMass_nonneg hw) (boxMass_nonneg hw)

/-- **Guard-free `≤ 1`.** On a zero-mass box the quotient is `0 / 0 = 0`, which already satisfies
the bound, so nonnegativity alone suffices and no positive-mass side condition appears. -/
theorem boxDensity_le_one [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] (hw : ∀ i, ∀ v ∈ A i, 0 ≤ w i v) : boxDensity w A p ≤ 1 := by
  rcases eq_or_lt_of_le (boxMass_nonneg hw) with h | h
  · rw [boxDensity, ← h, div_zero]
    norm_num
  · rw [boxDensity, div_le_one h]
    exact boxPredMass_le_boxMass hw

/-- **Complement densities sum to one — under positive mass.** Unlike the mass identity this one
genuinely needs the denominator, which is exactly where the guard-free convention stops being
free. -/
theorem boxDensity_add_compl_of_pos [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ}
    {A : FiniteBox V} [DecidablePred p] (h : 0 < boxMass w A) :
    boxDensity w A p + boxDensity w A (fun x => ¬ p x) = 1 := by
  rw [boxDensity, boxDensity, ← add_div, boxPredMass_add_compl, div_self (ne_of_gt h)]

theorem boxDensity_compl_of_pos [Fintype ι] [DecidableEq ι] {w : ∀ i, V i → ℝ} {A : FiniteBox V}
    [DecidablePred p] (h : 0 < boxMass w A) :
    boxDensity w A (fun x => ¬ p x) = 1 - boxDensity w A p := by
  rw [← boxDensity_add_compl_of_pos (p := p) h]
  ring

@[simp] theorem boxDensity_of_eq_empty [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    {A : FiniteBox V} [DecidablePred p] {i : ι} (hi : A i = ∅) : boxDensity w A p = 0 := by
  rw [boxDensity, boxPredMass_of_eq_empty (i := i) w hi, zero_div]

/-! ### Reindexing predicate mass and density

Reindexing a box relabels its coordinates, so a predicate on the original tuples must travel
with them. `Equiv.piCongrLeft` is the transport, and its inverse is `fun j => x (e j)`
definitionally, which is what keeps the dependent carrier indices from needing a cast. -/

/-- **Sums over tuples transport along a reindexing.** The single lemma both the predicate mass
and the density reindexings are built from. -/
theorem sum_tuples_reindex {ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (A : FiniteBox V) (f : (∀ i, V i) → ℝ) :
    ∑ y ∈ (A.reindex e).tuples, f (Equiv.piCongrLeft V e y) = ∑ x ∈ A.tuples, f x := by
  refine Finset.sum_nbij' (fun y => Equiv.piCongrLeft V e y)
    (fun x => (Equiv.piCongrLeft V e).symm x) (fun y hy => ?_) (fun x hx => ?_)
    (fun _ _ => Equiv.symm_apply_apply _ _) (fun _ _ => Equiv.apply_symm_apply _ _)
    (fun _ _ => rfl)
  · rw [FiniteBox.mem_tuples] at hy ⊢
    intro i
    have h := hy (e.symm i)
    rw [FiniteBox.reindex_apply] at h
    -- Rewrite the *index* first. `Equiv.piCongrLeft_apply_apply` is a `simp` lemma, so
    -- normalising here would undo the step rather than complete it.
    rw [← Equiv.apply_symm_apply e i, Equiv.piCongrLeft_apply_apply]
    exact h
  · rw [FiniteBox.mem_tuples] at hx ⊢
    intro j
    rw [FiniteBox.reindex_apply]
    exact hx (e j)

/-- Reindexing transports a tuple's weight. -/
theorem tupleWeight_reindex {ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (w : ∀ i, V i → ℝ) (y : ∀ j : ι', V (e j)) :
    tupleWeight (V := fun j => V (e j)) (fun j => w (e j)) y
      = tupleWeight w (Equiv.piCongrLeft V e y) :=
  Fintype.prod_equiv e _ _ fun j => by rw [Equiv.piCongrLeft_apply_apply]

/-- **Reindexing preserves predicate mass**, with the predicate transported along the tuple
equivalence. -/
theorem boxPredMass_reindex {ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] :
    boxPredMass (V := fun j => V (e j)) (fun j => w (e j)) (A.reindex e)
        (fun y => p (Equiv.piCongrLeft V e y)) = boxPredMass w A p := by
  rw [boxPredMass, boxPredMass, Finset.sum_filter, Finset.sum_filter,
    ← sum_tuples_reindex e A (fun x => if p x then tupleWeight w x else 0)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tupleWeight_reindex]

/-- **Reindexing preserves density**, since both the predicate mass and the total mass
transport. -/
theorem boxDensity_reindex {ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (w : ∀ i, V i → ℝ) (A : FiniteBox V)
    (p : (∀ i, V i) → Prop) [DecidablePred p] :
    boxDensity (V := fun j => V (e j)) (fun j => w (e j)) (A.reindex e)
        (fun y => p (Equiv.piCongrLeft V e y)) = boxDensity w A p := by
  rw [boxDensity, boxDensity, boxPredMass_reindex, boxMass_reindex]

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

/-! #### Predicate mass and density -/

/-- A predicate over the heterogeneous family: the first coordinate is `0`. -/
private def firstIsZero : (∀ i, VH i) → Prop := fun x => x 0 = 0

private instance : DecidablePred firstIsZero := fun x => by
  unfold firstIsZero; infer_instance

-- **Heterogeneous carriers, counting weights.** Of the `2 * 3 = 6` tuples, the `3` with first
-- coordinate `0` are selected, and the density is `1 / 2`. The selection is counted by
-- `decide`; the mass itself is real-valued, so it cannot be.
private theorem card_firstIsZero : (bxH.tuples.filter firstIsZero).card = 3 := by decide

private theorem predMass_firstIsZero :
    boxPredMass (fun _ _ => (1 : ℝ)) bxH firstIsZero = 3 := by
  rw [boxPredMass, Finset.sum_congr rfl
      (fun x _ => show tupleWeight (fun _ _ => (1 : ℝ)) x = 1 by simp [tupleWeight]),
    Finset.sum_const, nsmul_eq_mul, mul_one, card_firstIsZero]
  norm_num

example : boxDensity (fun _ _ => (1 : ℝ)) bxH firstIsZero = 1 / 2 := by
  rw [boxDensity, predMass_firstIsZero, boxMass_one, Fin.prod_univ_two]
  norm_num [bxH]

-- **An empty coordinate zeroes the predicate mass and the density**, with no hypothesis.
example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ) (p : (∀ _ : Fin 2, Fin 3) → Prop)
    [DecidablePred p] :
    boxPredMass w (fun i => if i = 0 then (∅ : Finset (Fin 3)) else Finset.univ) p = 0 :=
  boxPredMass_of_eq_empty (i := 0) w (by simp)

example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ) (p : (∀ _ : Fin 2, Fin 3) → Prop)
    [DecidablePred p] :
    boxDensity w (fun i => if i = 0 then (∅ : Finset (Fin 3)) else Finset.univ) p = 0 :=
  boxDensity_of_eq_empty (i := 0) w (by simp)

-- **A nonempty box of total mass zero.** Every tuple exists, but every weight vanishes, so the
-- density is `0` for *every* predicate — including `True`. This is the case that separates the
-- guard-free convention from a nonemptiness hypothesis, and the reason `boxDensity_true_of_pos`
-- cannot drop its positivity.
example (p : (∀ _ : Fin 2, Fin 3) → Prop) [DecidablePred p] :
    boxDensity (fun _ _ => (0 : ℝ)) (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) p = 0 := by
  refine boxDensity_of_boxMass_eq_zero ?_
  rw [boxMass_eq_prod_finsetMass, Fin.prod_univ_two]
  simp [finsetMass]

example :
    (Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3)))).Nonempty := by decide

-- **The empty index type.** There is one tuple, the empty one; a predicate holding of it has
-- mass `1` and density `1`, since the total mass is the empty product.
example (w : ∀ i : Fin 0, (fun _ : Fin 0 => Fin 3) i → ℝ)
    (A : FiniteBox (fun _ : Fin 0 => Fin 3)) :
    boxDensity w A (fun _ => True) = 1 :=
  boxDensity_true_of_pos (by rw [boxMass_of_isEmpty]; norm_num)

-- **Signed weights and the complement identity.** The identity is an exact splitting of the
-- sum, so it survives a weight that is negative on the box — where monotonicity and the `[0,1]`
-- bound both fail.
example (p : (∀ _ : Fin 2, Fin 3) → Prop) [DecidablePred p] :
    boxPredMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) p
      + boxPredMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) (fun x => ¬ p x)
      = boxMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) :=
  boxPredMass_add_compl _ _ p

-- …and that box really does carry a negative weight, so the previous example is not secretly a
-- nonnegative one: the total mass is `(2 - 1 - 1)^2 = 0`.
example :
    boxMass (fun _ v => if v = 0 then (2 : ℝ) else -1)
      (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) = 0 := by
  rw [boxMass_eq_prod_finsetMass, Fin.prod_univ_two]
  simp [finsetMass, Fin.sum_univ_three]
  norm_num

-- **Nonnegative weights give the interval bound**, with no positivity and no nonemptiness.
example (p : (∀ _ : Fin 2, Fin 3) → Prop) [DecidablePred p]
    (A : FiniteBox (fun _ : Fin 2 => Fin 3)) :
    0 ≤ boxDensity (fun _ v => if v = 0 then (2 : ℝ) else 1) A p ∧
      boxDensity (fun _ v => if v = 0 then (2 : ℝ) else 1) A p ≤ 1 := by
  refine ⟨boxDensity_nonneg ?_, boxDensity_le_one ?_⟩ <;>
    · intro i v _
      split <;> norm_num

-- **Reindexing carries the predicate with the tuples**, for both mass and density.
example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ)
    (A : FiniteBox (fun _ : Fin 2 => Fin 3)) (p : (∀ _ : Fin 2, Fin 3) → Prop)
    [DecidablePred p] :
    boxPredMass (V := fun j => (fun _ : Fin 2 => Fin 3) (Equiv.swap 0 1 j))
        (fun j => w (Equiv.swap 0 1 j)) (A.reindex (Equiv.swap 0 1))
        (fun y => p (Equiv.piCongrLeft _ (Equiv.swap 0 1) y))
      = boxPredMass w A p :=
  boxPredMass_reindex (Equiv.swap 0 1) w A p

example (w : ∀ i : Fin 2, (fun _ : Fin 2 => Fin 3) i → ℝ)
    (A : FiniteBox (fun _ : Fin 2 => Fin 3)) (p : (∀ _ : Fin 2, Fin 3) → Prop)
    [DecidablePred p] :
    boxDensity (V := fun j => (fun _ : Fin 2 => Fin 3) (Equiv.swap 0 1 j))
        (fun j => w (Equiv.swap 0 1 j)) (A.reindex (Equiv.swap 0 1))
        (fun y => p (Equiv.piCongrLeft _ (Equiv.swap 0 1) y))
      = boxDensity w A p :=
  boxDensity_reindex (Equiv.swap 0 1) w A p

end Tests

end RegularityLemmata
