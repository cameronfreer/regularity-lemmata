/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

/-!
# Raw finite weights and masses

The shared raw-weight vocabulary: a weight is an arbitrary `w : X → ℝ`, and the mass of a
finset is the sum of its weights. Nonnegativity is a **hypothesis**, never a field — that is
what keeps this usable by the kernel layer, the box layer, and the existing weighted-choice
machinery without any of them importing the others.

There is deliberately no normalized probability structure anywhere in the library. A
normalized carrier would exclude the empty carrier, make zero-mass cells awkward, force
conditioning to carry normalization proofs, and add coercion friction to every analytic
estimate. Probabilities and expectations are obtained by dividing by a mass at the point of
use, under the guard-free convention that division by zero is zero.

Note that a **nonempty** finset can have **zero** mass: every weight may be zero. Statements
that genuinely need a positive denominator therefore assume `0 < finsetMass w A`, not
`A.Nonempty`. The distinction is load-bearing and recurs throughout the kernel layer.
-/

namespace RegularityLemmata

variable {X : Type*} {w w' : X → ℝ} {A B : Finset X}

/-- The mass of a finset under a raw weight. -/
def finsetMass (w : X → ℝ) (A : Finset X) : ℝ := ∑ x ∈ A, w x

/-- A weighted sum over a finset. -/
def weightedSum (w : X → ℝ) (A : Finset X) (f : X → ℝ) : ℝ := ∑ x ∈ A, w x * f x

@[simp] theorem finsetMass_empty (w : X → ℝ) : finsetMass w ∅ = 0 := by
  rw [finsetMass, Finset.sum_empty]

@[simp] theorem weightedSum_empty (w : X → ℝ) (f : X → ℝ) : weightedSum w ∅ f = 0 := by
  rw [weightedSum, Finset.sum_empty]

theorem weightedSum_one (w : X → ℝ) (A : Finset X) :
    weightedSum w A (fun _ => 1) = finsetMass w A := by
  rw [weightedSum, finsetMass]
  exact Finset.sum_congr rfl fun x _ => mul_one _

/-- Counting weights recover the cardinality. -/
@[simp] theorem finsetMass_one (A : Finset X) :
    finsetMass (fun _ => (1 : ℝ)) A = (A.card : ℝ) := by
  rw [finsetMass, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem finsetMass_nonneg (hw : ∀ x ∈ A, 0 ≤ w x) : 0 ≤ finsetMass w A :=
  Finset.sum_nonneg hw

/-- Additivity over a disjoint union. -/
theorem finsetMass_union_of_disjoint [DecidableEq X] (w : X → ℝ) (h : Disjoint A B) :
    finsetMass w (A ∪ B) = finsetMass w A + finsetMass w B := by
  rw [finsetMass, finsetMass, finsetMass, Finset.sum_union h]

/-- Monotone in the finset, **given nonnegative weights on the larger one**. Without that
hypothesis a larger finset can carry less mass. -/
theorem finsetMass_mono (hw : ∀ x ∈ B, 0 ≤ w x) (h : A ⊆ B) :
    finsetMass w A ≤ finsetMass w B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x hx _ => hw x hx

/-- **Rescaling a carrier weight rescales its mass.** The identity behind the rescaling
invariance of normalized quantities. -/
theorem finsetMass_smul (c : ℝ) (w : X → ℝ) (A : Finset X) :
    finsetMass (fun x => c * w x) A = c * finsetMass w A := by
  rw [finsetMass, finsetMass, Finset.mul_sum]

theorem finsetMass_add (w w' : X → ℝ) (A : Finset X) :
    finsetMass (fun x => w x + w' x) A = finsetMass w A + finsetMass w' A := by
  rw [finsetMass, finsetMass, finsetMass, Finset.sum_add_distrib]

/-- Additivity over a pairwise-disjoint finite cover. -/
theorem finsetMass_biUnion [DecidableEq X] (w : X → ℝ) {s : Finset (Finset X)}
    (hdisj : (s : Set (Finset X)).PairwiseDisjoint id) :
    finsetMass w (s.biUnion id) = ∑ A ∈ s, finsetMass w A := by
  rw [finsetMass]
  exact Finset.sum_biUnion hdisj

/-! ### Zero mass is not emptiness -/

/-- A nonempty finset all of whose weights vanish has zero mass. This is why positive-mass
hypotheses are not interchangeable with nonemptiness. -/
theorem finsetMass_eq_zero_of_forall_eq_zero (h : ∀ x ∈ A, w x = 0) : finsetMass w A = 0 :=
  Finset.sum_eq_zero h

/-- Under nonnegative weights, positive mass forces a witness of positive weight. -/
theorem exists_pos_of_finsetMass_pos (hw : ∀ x ∈ A, 0 ≤ w x) (h : 0 < finsetMass w A) :
    ∃ x ∈ A, 0 < w x := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_lt.mpr (le_of_eq (finsetMass_eq_zero_of_forall_eq_zero fun x hx =>
    le_antisymm (hcon x hx) (hw x hx))))

/-! ### Tests -/

section Tests

-- A nonuniform weight on `Fin 3`.
example : finsetMass (fun x : Fin 3 => (x.val : ℝ)) Finset.univ = 3 := by
  rw [finsetMass, Fin.sum_univ_three]
  norm_num

-- **Nonempty, but zero mass.** The reason positive-mass hypotheses are not nonemptiness
-- hypotheses.
example : finsetMass (fun _ : Fin 3 => (0 : ℝ)) Finset.univ = 0 ∧
    (Finset.univ : Finset (Fin 3)).Nonempty :=
  ⟨finsetMass_eq_zero_of_forall_eq_zero fun _ _ => rfl, Finset.univ_nonempty⟩

-- Weights may be negative, so mass is not monotone without the nonnegativity hypothesis.
example : finsetMass (fun _ : Fin 3 => (-1 : ℝ)) Finset.univ
    < finsetMass (fun _ : Fin 3 => (-1 : ℝ)) ∅ := by
  rw [finsetMass_empty, finsetMass, Fin.sum_univ_three]
  norm_num

end Tests

end RegularityLemmata
