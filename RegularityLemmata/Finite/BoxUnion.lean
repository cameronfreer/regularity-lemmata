/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.ProductBox
import Mathlib.Data.Finset.SymmDiff

/-!
# Finite unions of boxes and the weighted symmetric-difference error

A finite family of boxes covers the tuples lying in at least one of them. Two such families are
compared by the **weighted mass of the tuples covered by exactly one** — their symmetric
difference. That number is the error a consumer charges for replacing one family by the other.

## Semantic unions, no Boolean syntax

A union here is a `Finset (FiniteBox V)` together with the tuple set it covers. There is
deliberately **no** syntax tree of Boolean combinations: finsets of tuples, finite unions, and
explicit mass bounds are enough, and a syntax would have to be designed against a consumer that
does not yet exist.

## One notion of mass, again

There is no mass primitive here. A symmetric difference is not a box, so the error cannot be
written with `boxMass` — but it is still a weighted sum over a finite set of tuples, which is
exactly `finsetMass` applied to `tupleWeight w`. That is what is used throughout, with
`boxMass_eq_finsetMass_tupleWeight` recording that `boxMass` is the same thing on a box's tuples.

The generic estimates it rests on — subadditivity, the union bound over a family, and the
symmetric-difference bound on a mass difference — are properties of `finsetMass` and live in
`Finite/Weight.lean` alongside it, not here.

## Why this is a separate module

`Finset.biUnion` and symmetric difference on tuple sets both need `DecidableEq (∀ i, V i)`, which
in turn needs `[∀ i, DecidableEq (V i)]` fiberwise. `Finite/ProductBox.lean` deliberately carries
no decidable equality on the carriers, so — exactly as with `Partition/BoxPartition.lean` — the
heavier instances are confined here and `FiniteBox`, `boxMass`, `boxPredMass`, and `boxDensity`
keep their lighter profile.

## Where nonnegativity enters, and where it does not

Everything that is an **identity** is hypothesis-free and survives signed weights: additivity
over a disjoint family, symmetry of the error, and its vanishing against itself.

Nonnegativity is required exactly for the **metric-style** claims — the union bound, the triangle
inequality, and the bound of a mass difference by the error — because each compares masses of
different sets, and with signed weights a larger set can carry less mass. The hypotheses are
stated on the sets involved, never globally.

The mass-difference bound needs nonnegativity only on the **symmetric difference**: the shared
intersection cancels between the two masses, so the weight there is unconstrained.
-/

namespace RegularityLemmata

open scoped symmDiff

variable {ι : Type*} {V : ι → Type*}

/-! ### Unions of a finite family of boxes -/

/-- **The tuples covered by a finite family of boxes.** -/
def unionTuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (F : Finset (FiniteBox V)) : Finset (∀ i, V i) :=
  F.biUnion FiniteBox.tuples

@[simp] theorem mem_unionTuples [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {F : Finset (FiniteBox V)} {x : ∀ i, V i} :
    x ∈ unionTuples F ↔ ∃ A ∈ F, x ∈ A.tuples := Finset.mem_biUnion

@[simp] theorem unionTuples_empty [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] :
    unionTuples (∅ : Finset (FiniteBox V)) = ∅ := Finset.biUnion_empty

@[simp] theorem unionTuples_singleton [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (A : FiniteBox V) : unionTuples {A} = A.tuples := Finset.singleton_biUnion

theorem unionTuples_subset [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {F G : Finset (FiniteBox V)} (h : F ⊆ G) : unionTuples F ⊆ unionTuples G :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- **`boxMass` is `finsetMass` of the tuple weight**, over the box's tuples. Stated so that the
box layer and the generic weight layer never drift apart, and so the results below can be phrased
with one mass notion. -/
theorem boxMass_eq_finsetMass_tupleWeight [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxMass w A = finsetMass (tupleWeight w) A.tuples := rfl

/-- **Exact additivity for a disjoint family.** An identity: no positivity hypothesis, so signed
weights are fine. -/
theorem finsetMass_unionTuples_of_pairwiseDisjoint [Fintype ι] [DecidableEq ι]
    [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ) {F : Finset (FiniteBox V)}
    (h : (F : Set (FiniteBox V)).PairwiseDisjoint FiniteBox.tuples) :
    finsetMass (tupleWeight w) (unionTuples F) = ∑ A ∈ F, boxMass w A :=
  Finset.sum_biUnion h

/-- **The union bound**, which does need nonnegativity. A direct specialization of the generic
`finsetMass_biUnion_le`. -/
theorem finsetMass_unionTuples_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F, 0 ≤ tupleWeight w x) :
    finsetMass (tupleWeight w) (unionTuples F) ≤ ∑ A ∈ F, boxMass w A :=
  finsetMass_biUnion_le hw

/-! ### The weighted symmetric-difference error -/

/-- **The error between two finite unions of boxes**: the weighted mass of the tuples covered by
exactly one of them. -/
def boxUnionError [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ)
    (F G : Finset (FiniteBox V)) : ℝ :=
  finsetMass (tupleWeight w) (unionTuples F ∆ unionTuples G)

theorem boxUnionError_apply [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F G : Finset (FiniteBox V)) :
    boxUnionError w F G = finsetMass (tupleWeight w) (unionTuples F ∆ unionTuples G) := rfl

/-- **Symmetric, with no hypothesis.** -/
theorem boxUnionError_comm [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F G : Finset (FiniteBox V)) :
    boxUnionError w F G = boxUnionError w G F := by
  rw [boxUnionError, boxUnionError, symmDiff_comm]

/-- **Zero against itself, with no hypothesis** — an identity, not an estimate, so signed
weights are fine. -/
@[simp] theorem boxUnionError_self [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F : Finset (FiniteBox V)) : boxUnionError w F F = 0 := by
  rw [boxUnionError, symmDiff_self]
  exact finsetMass_empty _

/-- Families covering the same tuples have zero error.

Stated in one direction only, and that is the correct contract: the converse is **false**, since
a nonempty symmetric difference of zero-weight tuples also has zero error. -/
theorem boxUnionError_of_unionTuples_eq [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {F G : Finset (FiniteBox V)} (h : unionTuples F = unionTuples G) :
    boxUnionError w F G = 0 := by
  rw [boxUnionError, h, symmDiff_self]
  exact finsetMass_empty _

theorem boxUnionError_nonneg [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F ∆ unionTuples G, 0 ≤ tupleWeight w x) :
    0 ≤ boxUnionError w F G := finsetMass_nonneg hw

/-- **The triangle inequality.** Nonnegativity is needed on the union of the two pairwise
differences, which is where the intermediate family's own tuples enter. -/
theorem boxUnionError_triangle [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G H : Finset (FiniteBox V)}
    (hw : ∀ x ∈ (unionTuples F ∆ unionTuples G) ∪ (unionTuples G ∆ unionTuples H),
      0 ≤ tupleWeight w x) :
    boxUnionError w F H ≤ boxUnionError w F G + boxUnionError w G H :=
  le_trans (finsetMass_mono hw (symmDiff_triangle _ _ _)) (finsetMass_union_le hw)

/-- **A mass difference between two unions is controlled by the error.** One-sided, assuming
neither disjointness nor nesting, and needing nonnegativity only on the symmetric difference. -/
theorem abs_sub_finsetMass_unionTuples_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F ∆ unionTuples G, 0 ≤ tupleWeight w x) :
    |finsetMass (tupleWeight w) (unionTuples F)
        - finsetMass (tupleWeight w) (unionTuples G)| ≤ boxUnionError w F G :=
  abs_sub_finsetMass_le hw

/-! ### Tests -/

section Tests

private abbrev VU : Fin 2 → Type := fun _ => Fin 2

private instance : ∀ i, DecidableEq (VU i) := fun _ => inferInstanceAs (DecidableEq (Fin 2))

/-- The box fixing the first coordinate to `v` and leaving the second free. -/
private def slab (v : Fin 2) : FiniteBox VU := fun i => if i = 0 then {v} else Finset.univ

private def fullBox : FiniteBox VU := fun _ => Finset.univ

private theorem slab_disjoint : Disjoint (slab 0).tuples (slab 1).tuples := by decide

-- The two slabs are disjoint and together cover everything.
example : unionTuples {slab 0, slab 1} = fullBox.tuples := by decide

-- **Exact additivity for a disjoint family**, with no positivity hypothesis. Counting weights
-- give `2 + 2 = 4`.
example : finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) (unionTuples {slab 0, slab 1})
    = ∑ A ∈ ({slab 0, slab 1} : Finset (FiniteBox VU)), boxMass (fun _ _ => (1 : ℝ)) A := by
  refine finsetMass_unionTuples_of_pairwiseDisjoint _ ?_
  intro A hA B hB hne
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact absurd rfl hne
  · exact slab_disjoint
  · exact slab_disjoint.symm
  · exact absurd rfl hne

-- **Symmetry and self-error need no hypothesis at all**, so they hold for signed weights.
example (w : ∀ i, VU i → ℝ) (F G : Finset (FiniteBox VU)) :
    boxUnionError w F G = boxUnionError w G F := boxUnionError_comm w F G

example (w : ∀ i, VU i → ℝ) (F : Finset (FiniteBox VU)) : boxUnionError w F F = 0 :=
  boxUnionError_self w F

/-- A weight that is negative on part of the carrier, used to show the identities survive it. -/
private def wU : ∀ i, VU i → ℝ := fun _ v => if v = 0 then 2 else -1

example : wU 0 1 = -1 := by norm_num [wU]

example (F : Finset (FiniteBox VU)) : boxUnionError wU F F = 0 := boxUnionError_self wU F

-- **The error is not the union bound.** The two families overlap in the whole `slab 0`, so the
-- symmetric difference is only `slab 1`'s tuples: error `2`, against a sum of masses `2 + 4 = 6`.
example : boxUnionError (fun _ _ => (1 : ℝ)) {slab 0} {slab 0, slab 1}
    = finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) ((slab 1).tuples) := by
  rw [boxUnionError, show unionTuples ({slab 0} : Finset (FiniteBox VU)) ∆
      unionTuples {slab 0, slab 1} = (slab 1).tuples from by decide]

example : finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) ((slab 1).tuples) = 2 := by
  rw [← boxMass_eq_finsetMass_tupleWeight, boxMass_one, Fin.prod_univ_two]
  norm_num [slab]

example :
    finsetMass (tupleWeight (fun _ _ => (1 : ℝ)))
        (unionTuples ({slab 0} : Finset (FiniteBox VU)))
      + finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) (unionTuples {slab 0, slab 1}) = 6 := by
  rw [unionTuples_singleton, ← boxMass_eq_finsetMass_tupleWeight,
    show unionTuples ({slab 0, slab 1} : Finset (FiniteBox VU)) = fullBox.tuples from by decide,
    ← boxMass_eq_finsetMass_tupleWeight, boxMass_one, boxMass_one, Fin.prod_univ_two,
    Fin.prod_univ_two]
  norm_num [slab, fullBox]

-- …so the error `2` is strictly below the trivial bound `6`, which is the point of stating it.
example : (2 : ℝ) < 6 := by norm_num

-- **The triangle inequality and the mass-difference bound**, under nonnegative weights.
example (F G H : Finset (FiniteBox VU)) :
    boxUnionError (fun _ _ => (1 : ℝ)) F H
      ≤ boxUnionError (fun _ _ => (1 : ℝ)) F G + boxUnionError (fun _ _ => (1 : ℝ)) G H := by
  refine boxUnionError_triangle ?_
  intro x _
  simp [tupleWeight]

example (F G : Finset (FiniteBox VU)) :
    |finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) (unionTuples F)
        - finsetMass (tupleWeight (fun _ _ => (1 : ℝ))) (unionTuples G)|
      ≤ boxUnionError (fun _ _ => (1 : ℝ)) F G := by
  refine abs_sub_finsetMass_unionTuples_le ?_
  intro x _
  simp [tupleWeight]

-- **Nonnegativity only on the symmetric difference.** The weight `wU` is negative at `1`, so it
-- is *not* nonnegative on the two unions; the bound still applies whenever the tuples covered by
-- exactly one of them avoid that value. Here the two families agree, so the hypothesis is
-- vacuous and the bound holds with a genuinely signed weight.
example (F : Finset (FiniteBox VU)) :
    |finsetMass (tupleWeight wU) (unionTuples F)
        - finsetMass (tupleWeight wU) (unionTuples F)| ≤ boxUnionError wU F F := by
  refine abs_sub_finsetMass_unionTuples_le ?_
  intro x hx
  rw [symmDiff_self] at hx
  exact absurd hx (Finset.notMem_empty x)

-- **The empty family** covers nothing and has zero mass.
example : unionTuples (∅ : Finset (FiniteBox VU)) = ∅ := unionTuples_empty

example (w : ∀ i, VU i → ℝ) :
    finsetMass (tupleWeight w) (unionTuples (∅ : Finset (FiniteBox VU))) = 0 := by
  rw [unionTuples_empty, finsetMass_empty]

end Tests

end RegularityLemmata
