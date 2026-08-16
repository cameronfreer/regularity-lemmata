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

/-- Two-factor perturbation bound: replacing each factor of a product by a nearby
value perturbs the product by at most the sum of the factor errors, provided the
retained factors `x` and `e` have absolute value at most one (densities are in `[0,1]`).
Consumed by path and triangle counting. -/
theorem abs_mul_sub_mul_le {x y d e : ℝ} (hx : |x| ≤ 1) (he : |e| ≤ 1) :
    |x * y - d * e| ≤ |x - d| + |y - e| := by
  have key : x * y - d * e = x * (y - e) + e * (x - d) := by ring
  rw [key]
  calc |x * (y - e) + e * (x - d)|
      ≤ |x * (y - e)| + |e * (x - d)| := abs_add_le _ _
    _ = |x| * |y - e| + |e| * |x - d| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |y - e| + 1 * |x - d| :=
        add_le_add (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_right he (abs_nonneg _))
    _ = |x - d| + |y - e| := by ring

/-- Three-factor perturbation bound: replacing each factor of a triple product by a nearby
value perturbs the product by at most the sum of the three factor errors, given the
retained factors have absolute value at most one. Consumed by strong three-vertex
counting. -/
theorem abs_mul_mul_sub_mul_mul_le {a b c a' b' c' : ℝ}
    (hb : |b| ≤ 1) (hc : |c| ≤ 1) (ha' : |a'| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b * c - a' * b' * c'| ≤ |a - a'| + |b - b'| + |c - c'| := by
  have key : a * b * c - a' * b' * c'
      = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by ring
  rw [key]
  have h1 : |(a - a') * b * c| ≤ |a - a'| := by
    rw [abs_mul, abs_mul]
    calc |a - a'| * |b| * |c| ≤ |a - a'| * 1 * 1 := by gcongr
      _ = |a - a'| := by ring
  have h2 : |a' * (b - b') * c| ≤ |b - b'| := by
    rw [abs_mul, abs_mul]
    calc |a'| * |b - b'| * |c| ≤ 1 * |b - b'| * 1 := by gcongr
      _ = |b - b'| := by ring
  have h3 : |a' * b' * (c - c')| ≤ |c - c'| := by
    rw [abs_mul, abs_mul]
    calc |a'| * |b'| * |c - c'| ≤ 1 * 1 * |c - c'| := by gcongr
      _ = |c - c'| := by ring
  have hstep : |(a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c')|
      ≤ |(a - a') * b * c| + |a' * (b - b') * c| + |a' * b' * (c - c')| := by
    have hxy := abs_add_le ((a - a') * b * c) (a' * (b - b') * c)
    have hxyz := abs_add_le ((a - a') * b * c + a' * (b - b') * c) (a' * b' * (c - c'))
    linarith
  linarith [hstep, h1, h2, h3]

/-! ### Bilinear domination by 0/1 rectangles

A `[0,1]`-weighted bilinear combination of a matrix's entries is bounded by the largest
**0/1** combination — that is, by the sup over genuine sub-rectangles. Stated abstractly
here because the hypotheses mention only a real matrix and two coefficient vectors.

This is the load-bearing step behind contraction of a stepped rectangle sum, where the
coefficients are relative cell masses. Note the constant: the bound is `ε`, **not** `2ε` —
no extreme-point machinery is needed, because `cᵢ * yᵢ ≤ max yᵢ 0` holds pointwise. -/

/-- A `[0,1]`-weighted sum is dominated by the sum over its nonnegative part — the 0/1
choice `cᵢ = 1 ↔ 0 ≤ yᵢ`. -/
theorem sum_mul_le_sum_filter_nonneg {ι : Type*} [DecidableEq ι] {c : ι → ℝ} (I : Finset ι)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1) (y : ι → ℝ) :
    ∑ i ∈ I, c i * y i ≤ ∑ i ∈ I.filter (fun i => 0 ≤ y i), y i := by
  classical
  calc ∑ i ∈ I, c i * y i
      ≤ ∑ i ∈ I, max (y i) 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        rcases le_or_gt 0 (y i) with h | h
        · calc c i * y i ≤ 1 * y i := mul_le_mul_of_nonneg_right (hc1 i hi) h
            _ = y i := one_mul _
            _ ≤ max (y i) 0 := le_max_left _ _
        · calc c i * y i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc0 i hi) h.le
            _ ≤ max (y i) 0 := le_max_right _ _
    _ = ∑ i ∈ I.filter (fun i => 0 ≤ y i), y i := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : 0 ≤ y i
        · simp [h]
        · simp [h, max_eq_right (not_le.mp h).le]

/-- The mirror bound, with the 0/1 choice `cᵢ = 1 ↔ yᵢ < 0`. -/
theorem sum_filter_neg_le_sum_mul {ι : Type*} [DecidableEq ι] {c : ι → ℝ} (I : Finset ι)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1) (y : ι → ℝ) :
    ∑ i ∈ I.filter (fun i => y i < 0), y i ≤ ∑ i ∈ I, c i * y i := by
  classical
  calc ∑ i ∈ I.filter (fun i => y i < 0), y i
      = ∑ i ∈ I, min (y i) 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : y i < 0
        · simp [h, min_eq_left h.le]
        · simp [h, min_eq_right (not_lt.mp h)]
    _ ≤ ∑ i ∈ I, c i * y i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rcases le_or_gt 0 (y i) with h | h
        · calc min (y i) 0 ≤ 0 := min_le_right _ _
            _ ≤ c i * y i := mul_nonneg (hc0 i hi) h
        · calc min (y i) 0 = y i := min_eq_left h.le
            _ = 1 * y i := (one_mul _).symm
            _ ≤ c i * y i := mul_le_mul_of_nonpos_right (hc1 i hi) h.le

/-- **Bilinear domination, at constant `1`.** If every sub-rectangle sum of `x` is within
`ε`, then so is every `[0,1]`-weighted bilinear combination.

The `1` here is what keeps the downstream common-refinement constant at `2` rather than
`4`: contraction is free, and the only factor of two comes from a triangle inequality. -/
theorem abs_sum_bilinear_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {c : ι → ℝ}
    {d : κ → ℝ} (I : Finset ι) (J : Finset κ)
    (hc0 : ∀ i ∈ I, 0 ≤ c i) (hc1 : ∀ i ∈ I, c i ≤ 1)
    (hd0 : ∀ j ∈ J, 0 ≤ d j) (hd1 : ∀ j ∈ J, d j ≤ 1) (x : ι → κ → ℝ) {ε : ℝ}
    (hrect : ∀ I' ⊆ I, ∀ J' ⊆ J, |∑ i ∈ I', ∑ j ∈ J', x i j| ≤ ε) :
    |∑ i ∈ I, c i * ∑ j ∈ J, d j * x i j| ≤ ε := by
  classical
  have hswap : ∀ I' ⊆ I, ∑ i ∈ I', (∑ j ∈ J, d j * x i j)
      = ∑ j ∈ J, d j * (∑ i ∈ I', x i j) := by
    intro I' _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  set y : ι → ℝ := fun i => ∑ j ∈ J, d j * x i j with hy
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- Lower bound: choose the negative parts on both sides.
    set I' : Finset ι := I.filter (fun i => y i < 0) with hI'
    have hI'sub : I' ⊆ I := Finset.filter_subset _ _
    have h1 : ∑ i ∈ I', y i ≤ ∑ i ∈ I, c i * y i :=
      sum_filter_neg_le_sum_mul I hc0 hc1 y
    set z : κ → ℝ := fun j => ∑ i ∈ I', x i j with hz
    set J' : Finset κ := J.filter (fun j => z j < 0) with hJ'
    have h2 : ∑ j ∈ J', z j ≤ ∑ j ∈ J, d j * z j :=
      sum_filter_neg_le_sum_mul J hd0 hd1 z
    have h3 : ∑ i ∈ I', y i = ∑ j ∈ J, d j * z j := by rw [hy, hswap I' hI'sub]
    have h4 : ∑ j ∈ J', z j = ∑ i ∈ I', ∑ j ∈ J', x i j := by
      rw [hz]; exact (Finset.sum_comm).symm
    have h5 : -ε ≤ ∑ i ∈ I', ∑ j ∈ J', x i j :=
      (abs_le.mp (hrect I' hI'sub J' (Finset.filter_subset _ _))).1
    linarith [h1, h2, h3 ▸ h2, h4 ▸ h5]
  · -- Upper bound: choose the nonnegative parts on both sides.
    set I' : Finset ι := I.filter (fun i => 0 ≤ y i) with hI'
    have hI'sub : I' ⊆ I := Finset.filter_subset _ _
    have h1 : ∑ i ∈ I, c i * y i ≤ ∑ i ∈ I', y i :=
      sum_mul_le_sum_filter_nonneg I hc0 hc1 y
    set z : κ → ℝ := fun j => ∑ i ∈ I', x i j with hz
    set J' : Finset κ := J.filter (fun j => 0 ≤ z j) with hJ'
    have h2 : ∑ j ∈ J, d j * z j ≤ ∑ j ∈ J', z j :=
      sum_mul_le_sum_filter_nonneg J hd0 hd1 z
    have h3 : ∑ i ∈ I', y i = ∑ j ∈ J, d j * z j := by rw [hy, hswap I' hI'sub]
    have h4 : ∑ j ∈ J', z j = ∑ i ∈ I', ∑ j ∈ J', x i j := by
      rw [hz]; exact (Finset.sum_comm).symm
    have h5 : ∑ i ∈ I', ∑ j ∈ J', x i j ≤ ε :=
      (abs_le.mp (hrect I' hI'sub J' (Finset.filter_subset _ _))).2
    linarith [h1, h2, h3, h4 ▸ h5]

/-! ### Tests and adversarial examples -/

-- **Contraction is not vacuous**: at all-ones coefficients the bilinear sum *is* a
-- rectangle sum, so the bound is attained rather than merely implied.
example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (x : ι → κ → ℝ) {ε : ℝ}
    (hrect : ∀ I' ⊆ I, ∀ J' ⊆ J, |∑ i ∈ I', ∑ j ∈ J', x i j| ≤ ε) :
    |∑ i ∈ I, (1 : ℝ) * ∑ j ∈ J, (1 : ℝ) * x i j| ≤ ε :=
  abs_sum_bilinear_le I J (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) x hrect

-- Zero coefficients give zero, well inside the bound — the degenerate cell case.
example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (x : ι → κ → ℝ) {ε : ℝ}
    (hrect : ∀ I' ⊆ I, ∀ J' ⊆ J, |∑ i ∈ I', ∑ j ∈ J', x i j| ≤ ε) :
    |∑ i ∈ I, (0 : ℝ) * ∑ j ∈ J, (0 : ℝ) * x i j| ≤ ε :=
  abs_sum_bilinear_le I J (fun _ _ => le_rfl) (fun _ _ => zero_le_one)
    (fun _ _ => le_rfl) (fun _ _ => zero_le_one) x hrect

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

-- Two-factor perturbation: |0.9·0.9 − 0.8·0.8| = 0.17 ≤ 0.1 + 0.1 = 0.2.
example : |(0.9 : ℝ) * 0.9 - 0.8 * 0.8| ≤ |(0.9 : ℝ) - 0.8| + |(0.9 : ℝ) - 0.8| :=
  abs_mul_sub_mul_le (by norm_num) (by norm_num)

-- Three-factor perturbation.
example : |(0.9 : ℝ) * 0.9 * 0.9 - 0.8 * 0.8 * 0.8|
    ≤ |(0.9 : ℝ) - 0.8| + |(0.9 : ℝ) - 0.8| + |(0.9 : ℝ) - 0.8| :=
  abs_mul_mul_sub_mul_mul_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RegularityLemmata
