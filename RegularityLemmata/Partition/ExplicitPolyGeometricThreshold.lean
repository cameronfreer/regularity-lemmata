/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RegularityLemmata.Partition.PolyGeometricThreshold

/-!
# Explicit polynomial-geometric thresholds

This module gives effective versions of `PolyGeometricThreshold`. The first route uses a
factorial estimate to define a closed natural-number threshold after which

`K * r ^ d * (1 - x) ^ r < 1`.

The second route retains the logarithmic dependence on the event-count coefficient. It is
suited to the equal-block sampling schedule, where an explicit comparison with the host floor
is needed. Its division-free endpoint bounds `E * b ^ r` by `B ^ r` from a polynomial event
count and a contracting ratio `b / B`.
-/

namespace RegularityLemmata

open Real

/-- A factorial estimate gives an explicit threshold where a polynomial is beaten by a
geometric factor. -/
theorem nat_mul_pow_mul_one_sub_pow_lt_one
    (K d r : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hr : (K : ℝ) * (Nat.factorial (d + 1) : ℝ) < x ^ (d + 1) * r) :
    (K : ℝ) * (r : ℝ) ^ d * (1 - x) ^ r < 1 := by
  have hr0 : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    have hnonneg : (0 : ℝ) ≤ (K : ℝ) * (Nat.factorial (d + 1) : ℝ) := by
      positivity
    norm_num at hr
    linarith
  have hq0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hqexp : (1 - x) ^ r ≤ Real.exp (-(x * r)) := by
    calc
      (1 - x) ^ r ≤ (Real.exp (-x)) ^ r :=
        pow_le_pow_left₀ hq0 (Real.one_sub_le_exp_neg x) r
      _ = Real.exp (-(x * r)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hxr : 0 < x * r := mul_pos hx (by positivity)
  have hseries := Real.pow_div_factorial_le_exp (x * r) hxr.le (d + 1)
  have hfrac : 0 < (x * r) ^ (d + 1) / (Nat.factorial (d + 1) : ℝ) := by
    positivity
  have hexpInv : Real.exp (-(x * r)) ≤
      ((x * r) ^ (d + 1) / (Nat.factorial (d + 1) : ℝ))⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hfrac).2 hseries
  have hfactorial : (0 : ℝ) < Nat.factorial (d + 1) := by
    positivity
  have hxpow : 0 < x ^ (d + 1) := pow_pos hx _
  have hrR : 0 < (r : ℝ) := by
    positivity
  have hbound : (K : ℝ) * (r : ℝ) ^ d *
      ((x * r) ^ (d + 1) / (Nat.factorial (d + 1) : ℝ))⁻¹ < 1 := by
    rw [inv_div, mul_pow, ← mul_div_assoc]
    rw [div_lt_one (mul_pos hxpow (pow_pos hrR _))]
    calc
      (K : ℝ) * (r : ℝ) ^ d * (Nat.factorial (d + 1) : ℝ)
          = (r : ℝ) ^ d * ((K : ℝ) * (Nat.factorial (d + 1) : ℝ)) := by ring
      _ < (r : ℝ) ^ d * (x ^ (d + 1) * r) :=
        mul_lt_mul_of_pos_left hr (pow_pos hrR _)
      _ = x ^ (d + 1) * (r : ℝ) ^ (d + 1) := by rw [pow_succ]; ring
  calc
    (K : ℝ) * (r : ℝ) ^ d * (1 - x) ^ r
        ≤ (K : ℝ) * (r : ℝ) ^ d * Real.exp (-(x * r)) := by gcongr
    _ ≤ (K : ℝ) * (r : ℝ) ^ d *
        ((x * r) ^ (d + 1) / (Nat.factorial (d + 1) : ℝ))⁻¹ := by gcongr
    _ < 1 := hbound

/-- The explicit natural threshold supplied by the factorial estimate. -/
noncomputable def polyGeometricThreshold (K d : ℕ) (x : ℝ) : ℕ :=
  ⌊(K : ℝ) * (Nat.factorial (d + 1) : ℝ) / x ^ (d + 1)⌋₊ + 1

/-- Beyond `polyGeometricThreshold K d x`, the polynomial-geometric expression is strictly
below one. -/
theorem polyGeometricThreshold_spec (K d : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ∀ r ≥ polyGeometricThreshold K d x, (K : ℝ) * (r : ℝ) ^ d * (1 - x) ^ r < 1 := by
  intro r hr
  apply nat_mul_pow_mul_one_sub_pow_lt_one K d r x hx hx1
  have hlt : (K : ℝ) * (Nat.factorial (d + 1) : ℝ) / x ^ (d + 1) < r := by
    calc
      (K : ℝ) * (Nat.factorial (d + 1) : ℝ) / x ^ (d + 1)
          < (polyGeometricThreshold K d x : ℕ) := by
            simpa [polyGeometricThreshold] using
              Nat.lt_floor_add_one
                ((K : ℝ) * (Nat.factorial (d + 1) : ℝ) / x ^ (d + 1))
      _ ≤ r := by exact_mod_cast hr
  have hxpow : 0 < x ^ (d + 1) := pow_pos hx _
  rw [div_lt_iff₀ hxpow] at hlt
  simpa [mul_assoc, mul_comm] using hlt

/-- On `[4, ∞)`, the logarithm is bounded by twice the square root. -/
theorem log_le_two_sqrt {r : ℝ} (hr : 4 ≤ r) : Real.log r ≤ 2 * Real.sqrt r := by
  have hr0 : 0 ≤ r := by linarith
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt r := by
    rw [Real.le_sqrt (by norm_num) hr0]
    norm_num
    exact hr
  have hsqrtPos : 0 < Real.sqrt r := lt_of_lt_of_le (by norm_num) hsqrt2
  have hlog := Real.log_le_sub_one_of_pos hsqrtPos
  have hrewrite : Real.log r = 2 * Real.log (Real.sqrt r) := by
    calc
      Real.log r = Real.log ((Real.sqrt r) ^ 2) := by rw [Real.sq_sqrt hr0]
      _ = (2 : ℕ) * Real.log (Real.sqrt r) := Real.log_pow _ _
      _ = 2 * Real.log (Real.sqrt r) := by norm_num
  rw [hrewrite]
  calc
    2 * Real.log (Real.sqrt r) ≤ 2 * (Real.sqrt r - 1) := by gcongr
    _ ≤ 2 * Real.sqrt r := by linarith

/-- A log-sensitive explicit criterion. Unlike the factorial threshold, this charges only
`log K` and `d * sqrt r`, the scale needed for comparison with the host floor. -/
theorem nat_mul_pow_mul_one_sub_pow_lt_one_of_log_bounds
    (K d r : ℕ) (x : ℝ) (hKpos : 0 < K) (hr4 : 4 ≤ r)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 4 * Real.log K ≤ x * r)
    (hd : 8 * d * Real.sqrt r ≤ x * r) :
    (K : ℝ) * (r : ℝ) ^ d * (1 - x) ^ r < 1 := by
  have hrpos : (0 : ℝ) < r := by positivity
  have hq0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hqexp : (1 - x) ^ r ≤ Real.exp (-(x * r)) := by
    calc
      (1 - x) ^ r ≤ (Real.exp (-x)) ^ r :=
        pow_le_pow_left₀ hq0 (Real.one_sub_le_exp_neg x) r
      _ = Real.exp (-(x * r)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hlogr : Real.log r ≤ 2 * Real.sqrt r :=
    log_le_two_sqrt (by exact_mod_cast hr4)
  have hKquarter : Real.log K ≤ x * r / 4 := by linarith
  have hdquarter : (d : ℝ) * Real.log r ≤ x * r / 4 := by
    have : (d : ℝ) * Real.log r ≤ d * (2 * Real.sqrt r) := by gcongr
    exact this.trans (by
      have hd' : 8 * (d : ℝ) * Real.sqrt r ≤ x * r := by exact_mod_cast hd
      linarith)
  have harg : Real.log K + (d : ℝ) * Real.log r - x * r < 0 := by
    have hxr : 0 < x * r := mul_pos hx hrpos
    linarith
  have hrewrite : (K : ℝ) * (r : ℝ) ^ d * Real.exp (-(x * r)) =
      Real.exp (Real.log K + (d : ℝ) * Real.log r - x * r) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
    rw [Real.exp_log (by positivity : (0 : ℝ) < K)]
    rw [Real.exp_nat_mul, Real.exp_log hrpos]
  calc
    (K : ℝ) * (r : ℝ) ^ d * (1 - x) ^ r
        ≤ (K : ℝ) * (r : ℝ) ^ d * Real.exp (-(x * r)) := by gcongr
    _ = Real.exp (Real.log K + (d : ℝ) * Real.log r - x * r) := hrewrite
    _ < 1 := Real.exp_lt_one_iff.mpr harg

/-- Division-free sampler form of the log-sensitive criterion. -/
theorem event_mul_pow_lt_of_log_bounds
    (K d r E b B : ℕ) (x : ℝ) (hKpos : 0 < K) (hr4 : 4 ≤ r)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 4 * Real.log K ≤ x * r)
    (hd : 8 * d * Real.sqrt r ≤ x * r)
    (hE : E ≤ K * r ^ d) (hB : 0 < B)
    (hratio : (b : ℝ) / B ≤ 1 - x) :
    E * b ^ r < B ^ r := by
  have hEreal : (E : ℝ) ≤ K * (r : ℝ) ^ d := by exact_mod_cast hE
  have hratio0 : 0 ≤ (b : ℝ) / B := by positivity
  have hratioPow : ((b : ℝ) / B) ^ r ≤ (1 - x) ^ r := by gcongr
  have hsmall : (E : ℝ) * ((b : ℝ) / B) ^ r < 1 := by
    calc
      (E : ℝ) * ((b : ℝ) / B) ^ r
          ≤ (K * (r : ℝ) ^ d) * (1 - x) ^ r := by gcongr
      _ < 1 := by
        simpa [mul_assoc] using
          nat_mul_pow_mul_one_sub_pow_lt_one_of_log_bounds K d r x
            hKpos hr4 hx hx1 hK hd
  have hBreal : 0 < (B : ℝ) ^ r := pow_pos (by exact_mod_cast hB) r
  have hscaled : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) <
      (B : ℝ) ^ r * 1 := mul_lt_mul_of_pos_left hsmall hBreal
  have hBne : (B : ℝ) ≠ 0 := by positivity
  have heq : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) =
      (E : ℝ) * (b : ℝ) ^ r := by
    rw [div_pow]
    field_simp
  have hreal : (E : ℝ) * (b : ℝ) ^ r < (B : ℝ) ^ r := by
    rw [heq, mul_one] at hscaled
    exact hscaled
  exact_mod_cast hreal

end RegularityLemmata
