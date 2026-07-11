/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Engel-form (Titu) inequalities under the division convention

The Cauchy–Schwarz quotient inequality
`(∑ f)² / (∑ g) ≤ ∑ f² / g` in the form used by the energy calculus: denominators are
only assumed **nonnegative**, with the convention hypothesis `g i = 0 → f i = 0` making
the `x / 0 = 0` cases degenerate rather than false.

Mathlib proves the strictly-positive-denominator form
(`Finset.sq_sum_div_le_sum_sq_div`); this file wraps it, splitting off the
zero-denominator indices. The two- and three-term forms are instantiations.
-/

namespace RegularityLemmata

/-- Engel form / Titu's lemma over a finset, with nonnegative denominators and the
`x / 0 = 0` convention hypothesis. -/
theorem titu_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℝ) (I : Finset ι)
    (hg : ∀ i ∈ I, 0 ≤ g i) (hfg : ∀ i ∈ I, g i = 0 → f i = 0) :
    (∑ i ∈ I, f i) ^ 2 / (∑ i ∈ I, g i) ≤ ∑ i ∈ I, f i ^ 2 / g i := by
  set P := I.filter fun i => 0 < g i with hP
  have hzero : ∀ i ∈ I, ¬ 0 < g i → g i = 0 := fun i hi hng =>
    le_antisymm (not_lt.mp hng) (hg i hi)
  have hsumf : ∑ i ∈ I, f i = ∑ i ∈ P, f i := by
    rw [hP]
    refine (Finset.sum_filter_of_ne fun i hi hfi => ?_).symm
    by_contra hng
    exact hfi (hfg i hi (hzero i hi hng))
  have hsumg : ∑ i ∈ I, g i = ∑ i ∈ P, g i := by
    rw [hP]
    refine (Finset.sum_filter_of_ne fun i hi hgi => ?_).symm
    by_contra hng
    exact hgi (hzero i hi hng)
  calc (∑ i ∈ I, f i) ^ 2 / ∑ i ∈ I, g i
      = (∑ i ∈ P, f i) ^ 2 / ∑ i ∈ P, g i := by rw [hsumf, hsumg]
    _ ≤ ∑ i ∈ P, f i ^ 2 / g i :=
        Finset.sq_sum_div_le_sum_sq_div P f fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ I, f i ^ 2 / g i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i hi _ => ?_
        exact div_nonneg (sq_nonneg _) (hg i hi)

/-- Two-term Engel form with the division convention. -/
theorem titu_two {a b p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : p = 0 → a = 0) (hb : q = 0 → b = 0) :
    (a + b) ^ 2 / (p + q) ≤ a ^ 2 / p + b ^ 2 / q := by
  have := titu_finset (![a, b]) (![p, q]) Finset.univ
    (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two] using this

/-- Three-term Engel form with the division convention. -/
theorem titu_three {a b c p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ha : p = 0 → a = 0) (hb : q = 0 → b = 0) (hc : r = 0 → c = 0) :
    (a + b + c) ^ 2 / (p + q + r) ≤ a ^ 2 / p + b ^ 2 / q + c ^ 2 / r := by
  have := titu_finset (![a, b, c]) (![p, q, r]) Finset.univ
    (fun i _ => by fin_cases i <;> assumption)
    (fun i _ => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_three, add_assoc] using this

/-- Engel form with an explicit defect: the two-term inequality improves by the
weighted squared deviation of the first cell's ratio from the pooled ratio. -/
theorem engel_defect_lower {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (a + b) ^ 2 / (p + q) + p * (a / p - (a + b) / (p + q)) ^ 2 ≤ a ^ 2 / p + b ^ 2 / q := by
  have hpq : (0 : ℝ) < p + q := by linarith
  have key : a ^ 2 / p + b ^ 2 / q
      - ((a + b) ^ 2 / (p + q) + p * (a / p - (a + b) / (p + q)) ^ 2)
      = (a * q - b * p) ^ 2 / (q * (p + q) ^ 2) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (a * q - b * p) ^ 2 / (q * (p + q) ^ 2) := by positivity
  linarith

/-! ### Tests and adversarial examples -/

-- A strict instance: (1+2)²/(1+1) = 4.5 ≤ 1 + 4 = 5.
example : ((1 : ℝ) + 2) ^ 2 / (1 + 1) ≤ 1 ^ 2 / 1 + 2 ^ 2 / 1 :=
  titu_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Zero-denominator convention exercised: p = 0 forces a = 0, and the inequality
-- degenerates to b²/q ≤ 0 + b²/q.
example : ((0 : ℝ) + 3) ^ 2 / (0 + 2) ≤ 0 ^ 2 / 0 + 3 ^ 2 / 2 :=
  titu_two le_rfl (by norm_num) (fun _ => rfl) (by norm_num)

-- Three-term instance.
example : ((1 : ℝ) + 1 + 1) ^ 2 / (1 + 1 + 1) ≤ 1 ^ 2 / 1 + 1 ^ 2 / 1 + 1 ^ 2 / 1 :=
  titu_three (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- All denominators zero: both sides collapse to 0.
example : ((0 : ℝ) + 0) ^ 2 / (0 + 0) ≤ 0 ^ 2 / 0 + 0 ^ 2 / 0 :=
  titu_two le_rfl le_rfl (fun _ => rfl) (fun _ => rfl)

end RegularityLemmata
