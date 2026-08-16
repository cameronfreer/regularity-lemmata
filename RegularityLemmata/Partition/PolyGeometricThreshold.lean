/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polynomial trace counts are eventually beaten by geometric concentration

The schedule-layer endpoint of the equal-block sampling route: for fixed `C`, `d`, and
`0 ≤ r < 1`, eventually `C * n^d * r^n < 1`.  This is what closes the simultaneous-sampling
union bound — the family of traces (test sets) is polynomial in the host size, while the
per-event violation fraction is geometric (`HypergeometricTail` at a deviation-scaled
binomial-moment order) — and it yields an EXISTENTIAL host threshold; the explicit
finite-size display lives in `ExplicitPolyGeometricThreshold`.
-/

open Filter Asymptotics

namespace RegularityLemmata

/-- Any fixed polynomial trace count is eventually beaten by a geometric tail. -/
theorem exists_forall_const_mul_pow_mul_geometric_lt_one
    (C r : ℝ) (d : ℕ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ N : ℕ, ∀ n ≥ N, C * (n : ℝ) ^ d * r ^ n < 1 := by
  have hrnorm : ‖r‖ < (1 : ℝ) := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hlittle : (fun n : ℕ ↦ (n : ℝ) ^ d * r ^ n) =o[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
    simpa only [one_pow] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) d hrnorm)
  have htend : Tendsto (fun n : ℕ ↦ C * ((n : ℝ) ^ d * r ^ n)) atTop (nhds 0) := by
    have hzero := hlittle.tendsto_zero_of_tendsto tendsto_const_nhds
    simpa only [mul_zero] using tendsto_const_nhds.mul hzero
  have hevent : ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ d * r ^ n < 1 := by
    simpa only [mul_assoc] using (tendsto_order.mp htend).2 1 zero_lt_one
  exact Filter.eventually_atTop.mp hevent

/-- A finite multiple of a polynomial trace count is likewise eventually beaten. -/
theorem exists_forall_nat_mul_pow_mul_geometric_lt_one
    (K d : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ N : ℕ, ∀ n ≥ N, K * (n : ℝ) ^ d * r ^ n < 1 :=
  exists_forall_const_mul_pow_mul_geometric_lt_one K r d hr0 hr1

end RegularityLemmata
