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
import Mathlib.Data.Finset.SymmDiff

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

open scoped symmDiff

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

/-! ### Subadditivity and the symmetric-difference bound

Additivity over a disjoint union is an identity and needs no sign hypothesis. Everything below
compares masses of **different** finsets, which is exactly when a signed weight can make a
larger set lighter, so each carries nonnegativity — stated on the sets involved, never
globally. -/

/-- **Subadditive over a union.** Unlike `finsetMass_union_of_disjoint` this needs
nonnegativity, because the overlap is counted twice on the right. -/
theorem finsetMass_union_le [DecidableEq X] {w : X → ℝ} {A B : Finset X}
    (hw : ∀ x ∈ A ∪ B, 0 ≤ w x) : finsetMass w (A ∪ B) ≤ finsetMass w A + finsetMass w B := by
  rw [← Finset.union_sdiff_self_eq_union, finsetMass_union_of_disjoint w Finset.disjoint_sdiff]
  have hle : finsetMass w (B \ A) ≤ finsetMass w B :=
    finsetMass_mono (fun x hx => hw x (Finset.mem_union_right _ hx)) Finset.sdiff_subset
  linarith

/-- **The union bound over a finite family.** Proved by induction: the pinned Mathlib has
cardinality and density versions of this, but no weighted one. -/
theorem finsetMass_biUnion_le [DecidableEq X] {w : X → ℝ} {κ : Type*} [DecidableEq κ]
    {s : Finset κ} {t : κ → Finset X} (hw : ∀ x ∈ s.biUnion t, 0 ≤ w x) :
    finsetMass w (s.biUnion t) ≤ ∑ k ∈ s, finsetMass w (t k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.biUnion_insert] at *
      have hrest := ih fun x hx => hw x (Finset.mem_union_right _ hx)
      have hpair := finsetMass_union_le (w := w) hw
      linarith

/-- **A mass difference is controlled by the symmetric difference.**

Nonnegativity is required **only on `A ∆ B`**: the two masses share the mass of `A ∩ B`, which
cancels in the difference, so the weight is unconstrained there. The bound assumes neither
disjointness nor nesting. -/
theorem abs_sub_finsetMass_le [DecidableEq X] {w : X → ℝ} {A B : Finset X}
    (hw : ∀ x ∈ A ∆ B, 0 ≤ w x) :
    |finsetMass w A - finsetMass w B| ≤ finsetMass w (A ∆ B) := by
  have hA : finsetMass w A = finsetMass w (A \ B) + finsetMass w (A ∩ B) := by
    rw [← finsetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter A B),
      Finset.sdiff_union_inter]
  have hB : finsetMass w B = finsetMass w (B \ A) + finsetMass w (B ∩ A) := by
    rw [← finsetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter B A),
      Finset.sdiff_union_inter]
  have hcomm : finsetMass w (B ∩ A) = finsetMass w (A ∩ B) := by rw [Finset.inter_comm]
  have hsplit : finsetMass w (A ∆ B) = finsetMass w (A \ B) + finsetMass w (B \ A) := by
    rw [Finset.symmDiff_def, finsetMass_union_of_disjoint w disjoint_sdiff_sdiff]
  have hAB : 0 ≤ finsetMass w (A \ B) :=
    finsetMass_nonneg fun x hx =>
      hw x (by rw [Finset.symmDiff_def]; exact Finset.mem_union_left _ hx)
  have hBA : 0 ≤ finsetMass w (B \ A) :=
    finsetMass_nonneg fun x hx =>
      hw x (by rw [Finset.symmDiff_def]; exact Finset.mem_union_right _ hx)
  rw [hA, hB, hcomm, hsplit, abs_le]
  constructor <;> linarith

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

/-! ### Relative mass

The fraction of a cell's mass carried by a test set. These are exactly the `[0,1]`
coefficients that the bilinear domination lemma of `Finite/Inequalities.lean` consumes, so
the `≤ 1` bound must hold with **no** positive-mass hypothesis. -/

/-- The relative mass of `S` inside the cell `C`, guard-free: `0` on a zero-mass cell. -/
noncomputable def relMass [DecidableEq X] (w : X → ℝ) (S C : Finset X) : ℝ :=
  finsetMass w (S ∩ C) / finsetMass w C

theorem relMass_nonneg [DecidableEq X] {C : Finset X} (hw : ∀ x ∈ C, 0 ≤ w x)
    (S : Finset X) : 0 ≤ relMass w S C :=
  div_nonneg (finsetMass_nonneg fun x hx => hw x (Finset.mem_of_mem_inter_right hx))
    (finsetMass_nonneg hw)

/-- **Guard-free `≤ 1`.** On a zero-mass cell the quotient is `0/0 = 0`, so no positivity
hypothesis is needed — which is what lets the contraction argument avoid a positive-mass
side condition on every cell. -/
theorem relMass_le_one [DecidableEq X] {C : Finset X} (hw : ∀ x ∈ C, 0 ≤ w x)
    (S : Finset X) : relMass w S C ≤ 1 := by
  rcases eq_or_lt_of_le (finsetMass_nonneg hw) with h | h
  · rw [relMass, ← h, div_zero]
    norm_num
  · rw [relMass, div_le_one h]
    exact finsetMass_mono hw Finset.inter_subset_right

/-- At the full cell the relative mass is `1` — unless the cell has zero mass, where it is
`0`. Both cases are correct; neither needs a guard. -/
theorem relMass_self_of_pos [DecidableEq X] {C : Finset X} (h : 0 < finsetMass w C) :
    relMass w C C = 1 := by
  rw [relMass, Finset.inter_self, div_self (ne_of_gt h)]

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
