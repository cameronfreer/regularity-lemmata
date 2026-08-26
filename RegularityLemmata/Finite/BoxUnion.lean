/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.ProductBox
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

## Why this is a separate module

`Finset.biUnion` and symmetric difference on tuple sets both need `DecidableEq (∀ i, V i)`, which
in turn needs `[∀ i, DecidableEq (V i)]` fiberwise. `Finite/ProductBox.lean` deliberately carries
no decidable equality on the carriers, so — exactly as with `Partition/BoxPartition.lean` — the
heavier instances are confined here and `FiniteBox`, `boxMass`, `boxPredMass`, and `boxDensity`
keep their lighter profile.

## Where nonnegativity enters, and where it does not

`tupleSetMass` is a plain weighted sum, so everything that is an **identity** is hypothesis-free
and survives signed weights: additivity over disjoint sets, the disjoint-family decomposition,
symmetry of the error, and the vanishing of the error against oneself.

Nonnegativity is required exactly for the **metric-style** claims — monotonicity, subadditivity,
the triangle inequality, and the bound of a mass difference by the error — because each of them
compares masses of different sets, and with signed weights a larger set can carry less mass.

The hypotheses are stated **on the sets involved** rather than globally, so a weight may be
negative away from them.

## One-sided, and not a union bound

`abs_sub_tupleSetMass_le` bounds `|mass S - mass T|` by the mass of `S ∆ T`. It assumes neither
disjointness nor nesting, and it is genuinely stronger than the trivial `mass S + mass T`: the
tests exhibit two overlapping families where the error is strictly smaller than that sum.
-/

namespace RegularityLemmata

open scoped symmDiff

variable {ι : Type*} {V : ι → Type*}

/-! ### The mass of an arbitrary tuple set

`boxMass` is this sum over the tuples of a box. Comparing two unions needs the same sum over sets
that are not boxes — a symmetric difference is not a box — so the underlying construction is
named once here and `boxMass` is recovered as a special case. -/

/-- The total weight of a finite set of tuples. -/
def tupleSetMass [Fintype ι] (w : ∀ i, V i → ℝ) (S : Finset (∀ i, V i)) : ℝ :=
  ∑ x ∈ S, tupleWeight w x

theorem tupleSetMass_apply [Fintype ι] (w : ∀ i, V i → ℝ) (S : Finset (∀ i, V i)) :
    tupleSetMass w S = ∑ x ∈ S, tupleWeight w x := rfl

@[simp] theorem tupleSetMass_empty [Fintype ι] (w : ∀ i, V i → ℝ) :
    tupleSetMass w (∅ : Finset (∀ i, V i)) = 0 := Finset.sum_empty

/-- **`boxMass` is this construction on a box's tuples.** Stated so the two never drift apart. -/
theorem boxMass_eq_tupleSetMass [Fintype ι] [DecidableEq ι] (w : ∀ i, V i → ℝ)
    (A : FiniteBox V) : boxMass w A = tupleSetMass w A.tuples := rfl

theorem tupleSetMass_nonneg [Fintype ι] {w : ∀ i, V i → ℝ} {S : Finset (∀ i, V i)}
    (hw : ∀ x ∈ S, 0 ≤ tupleWeight w x) : 0 ≤ tupleSetMass w S :=
  Finset.sum_nonneg hw

/-- **Monotone in the set**, given nonnegative tuple weights on the **larger** one. -/
theorem tupleSetMass_mono [Fintype ι] {w : ∀ i, V i → ℝ} {S T : Finset (∀ i, V i)}
    (hw : ∀ x ∈ T, 0 ≤ tupleWeight w x) (hST : S ⊆ T) : tupleSetMass w S ≤ tupleSetMass w T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST fun x hx _ => hw x hx

/-- **Exact additivity over a disjoint pair.** An identity, so no positivity is involved and
signed weights are fine. -/
theorem tupleSetMass_union_of_disjoint [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {S T : Finset (∀ i, V i)} (h : Disjoint S T) :
    tupleSetMass w (S ∪ T) = tupleSetMass w S + tupleSetMass w T := Finset.sum_union h

/-- **Subadditivity over a union**, which unlike additivity does need nonnegativity: the
overlap is counted twice on the right. -/
theorem tupleSetMass_union_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {S T : Finset (∀ i, V i)}
    (hw : ∀ x ∈ S ∪ T, 0 ≤ tupleWeight w x) :
    tupleSetMass w (S ∪ T) ≤ tupleSetMass w S + tupleSetMass w T := by
  rw [← Finset.union_sdiff_self_eq_union, tupleSetMass_union_of_disjoint w Finset.disjoint_sdiff]
  have hle : tupleSetMass w (T \ S) ≤ tupleSetMass w T :=
    tupleSetMass_mono (fun x hx => hw x (Finset.mem_union_right _ hx)) Finset.sdiff_subset
  linarith

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

/-- **Exact additivity for a disjoint family.** The masses of the boxes add up to the mass of
what they cover, with no positivity hypothesis, so signed weights are fine. -/
theorem tupleSetMass_unionTuples_of_pairwiseDisjoint [Fintype ι] [DecidableEq ι]
    [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ) {F : Finset (FiniteBox V)}
    (h : (F : Set (FiniteBox V)).PairwiseDisjoint FiniteBox.tuples) :
    tupleSetMass w (unionTuples F) = ∑ A ∈ F, boxMass w A :=
  Finset.sum_biUnion h

/-- **The union bound**, which does need nonnegativity. -/
theorem tupleSetMass_unionTuples_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F, 0 ≤ tupleWeight w x) :
    tupleSetMass w (unionTuples F) ≤ ∑ A ∈ F, boxMass w A := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert A F hA ih =>
      rw [Finset.sum_insert hA]
      have hunion : unionTuples (insert A F) = A.tuples ∪ unionTuples F := by
        rw [unionTuples, unionTuples, Finset.biUnion_insert]
      rw [hunion] at hw ⊢
      have hrest := ih fun x hx => hw x (Finset.mem_union_right _ hx)
      have := tupleSetMass_union_le (w := w) hw
      rw [boxMass_eq_tupleSetMass]
      linarith

/-! ### The weighted symmetric-difference error -/

/-- **The error between two finite unions of boxes**: the weighted mass of the tuples covered by
exactly one of them. -/
def boxUnionError [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] (w : ∀ i, V i → ℝ)
    (F G : Finset (FiniteBox V)) : ℝ :=
  tupleSetMass w (unionTuples F ∆ unionTuples G)

theorem boxUnionError_apply [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) (F G : Finset (FiniteBox V)) :
    boxUnionError w F G = tupleSetMass w (unionTuples F ∆ unionTuples G) := rfl

/-- The symmetric difference of two tuple sets, as the two one-sided differences. -/
theorem symmDiff_eq_sdiff_union_sdiff [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (V i)]
    (S T : Finset (∀ i, V i)) : S ∆ T = (S \ T) ∪ (T \ S) := rfl

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
  exact tupleSetMass_empty w

/-- Families covering the same tuples have zero error. Note the converse fails: a nonempty
symmetric difference of zero-weight tuples also has zero error. -/
theorem boxUnionError_of_unionTuples_eq [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    (w : ∀ i, V i → ℝ) {F G : Finset (FiniteBox V)} (h : unionTuples F = unionTuples G) :
    boxUnionError w F G = 0 := by
  rw [boxUnionError, h, symmDiff_self]
  exact tupleSetMass_empty w

theorem boxUnionError_nonneg [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G : Finset (FiniteBox V)}
    (hw : ∀ x ∈ unionTuples F ∆ unionTuples G, 0 ≤ tupleWeight w x) :
    0 ≤ boxUnionError w F G := tupleSetMass_nonneg hw

/-- **The triangle inequality.** Nonnegativity is needed on the union of the three pairwise
differences, which is where the intermediate family's own tuples enter. -/
theorem boxUnionError_triangle [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {F G H : Finset (FiniteBox V)}
    (hw : ∀ x ∈ (unionTuples F ∆ unionTuples G) ∪ (unionTuples G ∆ unionTuples H),
      0 ≤ tupleWeight w x) :
    boxUnionError w F H ≤ boxUnionError w F G + boxUnionError w G H := by
  refine le_trans (tupleSetMass_mono hw ?_) (tupleSetMass_union_le hw)
  exact symmDiff_triangle _ _ _

/-- **A mass difference is controlled by the error.** One-sided, assuming neither disjointness
nor nesting of the two tuple sets, and strictly stronger than the trivial bound by the sum of
the two masses. -/
theorem abs_sub_tupleSetMass_le [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)]
    {w : ∀ i, V i → ℝ} {S T : Finset (∀ i, V i)} (hw : ∀ x ∈ S ∪ T, 0 ≤ tupleWeight w x) :
    |tupleSetMass w S - tupleSetMass w T| ≤ tupleSetMass w (S ∆ T) := by
  have hSsplit : tupleSetMass w S = tupleSetMass w (S \ T) + tupleSetMass w (S ∩ T) := by
    rw [← tupleSetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter S T),
      Finset.sdiff_union_inter]
  have hTsplit : tupleSetMass w T = tupleSetMass w (T \ S) + tupleSetMass w (T ∩ S) := by
    rw [← tupleSetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter T S),
      Finset.sdiff_union_inter]
  have hcomm : tupleSetMass w (T ∩ S) = tupleSetMass w (S ∩ T) := by rw [Finset.inter_comm]
  have hsym : tupleSetMass w (S ∆ T)
      = tupleSetMass w (S \ T) + tupleSetMass w (T \ S) := by
    rw [symmDiff_eq_sdiff_union_sdiff,
      tupleSetMass_union_of_disjoint w disjoint_sdiff_sdiff]
  have hS : 0 ≤ tupleSetMass w (S \ T) :=
    tupleSetMass_nonneg fun x hx =>
      hw x (Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1)
  have hT : 0 ≤ tupleSetMass w (T \ S) :=
    tupleSetMass_nonneg fun x hx =>
      hw x (Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1)
  rw [hSsplit, hTsplit, hsym, abs_le]
  constructor <;> linarith

/-! ### Tests -/

section Tests

private abbrev VU : Fin 2 → Type := fun _ => Fin 2

private instance : ∀ i, DecidableEq (VU i) := fun _ => inferInstanceAs (DecidableEq (Fin 2))

/-- The box fixing the first coordinate to `v` and leaving the second free. -/
private def slab (v : Fin 2) : FiniteBox VU := fun i => if i = 0 then {v} else Finset.univ

private def fullBox : FiniteBox VU := fun _ => Finset.univ

-- The two slabs are disjoint and together cover everything.
private theorem slab_disjoint : Disjoint (slab 0).tuples (slab 1).tuples := by decide

example : unionTuples {slab 0, slab 1} = fullBox.tuples := by decide

-- **Exact additivity for a disjoint family**, with no positivity hypothesis. Counting weights
-- give `2 + 2 = 4`.
example : tupleSetMass (fun _ _ => (1 : ℝ)) (unionTuples {slab 0, slab 1})
    = ∑ A ∈ ({slab 0, slab 1} : Finset (FiniteBox VU)), boxMass (fun _ _ => (1 : ℝ)) A := by
  refine tupleSetMass_unionTuples_of_pairwiseDisjoint _ ?_
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
    = tupleSetMass (fun _ _ => (1 : ℝ)) ((slab 1).tuples) := by
  rw [boxUnionError, show unionTuples ({slab 0} : Finset (FiniteBox VU)) ∆
      unionTuples {slab 0, slab 1} = (slab 1).tuples from by decide]

example : tupleSetMass (fun _ _ => (1 : ℝ)) ((slab 1).tuples) = 2 := by
  rw [← boxMass_eq_tupleSetMass, boxMass_one, Fin.prod_univ_two]
  norm_num [slab]

example : tupleSetMass (fun _ _ => (1 : ℝ)) (unionTuples ({slab 0} : Finset (FiniteBox VU)))
    + tupleSetMass (fun _ _ => (1 : ℝ)) (unionTuples {slab 0, slab 1}) = 6 := by
  rw [unionTuples_singleton, ← boxMass_eq_tupleSetMass,
    show unionTuples ({slab 0, slab 1} : Finset (FiniteBox VU)) = fullBox.tuples from by decide,
    ← boxMass_eq_tupleSetMass, boxMass_one, boxMass_one, Fin.prod_univ_two, Fin.prod_univ_two]
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

example (S T : Finset (∀ i, VU i)) :
    |tupleSetMass (fun _ _ => (1 : ℝ)) S - tupleSetMass (fun _ _ => (1 : ℝ)) T|
      ≤ tupleSetMass (fun _ _ => (1 : ℝ)) (S ∆ T) := by
  refine abs_sub_tupleSetMass_le ?_
  intro x _
  simp [tupleWeight]

-- **The empty family** covers nothing and has zero mass.
example : unionTuples (∅ : Finset (FiniteBox VU)) = ∅ := unionTuples_empty

example (w : ∀ i, VU i → ℝ) :
    tupleSetMass w (unionTuples (∅ : Finset (FiniteBox VU))) = 0 := by
  rw [unionTuples_empty, tupleSetMass_empty]

end Tests

end RegularityLemmata
