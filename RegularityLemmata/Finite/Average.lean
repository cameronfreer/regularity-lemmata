/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.RectKernel
import Mathlib.Algebra.BigOperators.Field

/-!
# One-variable finite averages

`averageOn S φ` is the average of `φ : α → ℝ` over a finset, guard-free with value `0` on the
empty set (via `x / 0 = 0`), mirroring `densityOn`'s convention. `densityOn` is its indicator
shadow (`averageOn_indicator`), and the two-variable `rectAverageCount` factors through it in
both orders (`rectAverageCount_eq_averageOn_left`/`_right`), so kernel averages, fiber
averages, and densities share one vocabulary.

The mass form `averageOn_mul_card` is the restriction primitive: statements about sums
restrict along subsets, and the average forms are recovered by dividing.
-/

namespace RegularityLemmata

variable {α X Y : Type*} {S : Finset α} {φ ψ : α → ℝ} {c : ℝ}

/-- The average of `φ` over `S`; `0` on the empty set via `x / 0 = 0`. -/
noncomputable def averageOn (S : Finset α) (φ : α → ℝ) : ℝ := (∑ x ∈ S, φ x) / S.card

@[simp] theorem averageOn_empty (φ : α → ℝ) : averageOn (∅ : Finset α) φ = 0 := by
  simp [averageOn]

/-- The mass form, guard-free: on the empty set both sides are `0`. -/
theorem averageOn_mul_card (S : Finset α) (φ : α → ℝ) :
    averageOn S φ * S.card = ∑ x ∈ S, φ x := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have h0 : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hS
    rw [averageOn, div_mul_cancel₀ _ h0]

theorem averageOn_const (hS : S.Nonempty) (c : ℝ) : averageOn S (fun _ ↦ c) = c := by
  have h0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [averageOn, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self h0,
    mul_one]

theorem averageOn_congr (h : ∀ x ∈ S, φ x = ψ x) : averageOn S φ = averageOn S ψ := by
  rw [averageOn, averageOn, Finset.sum_congr rfl h]

theorem averageOn_nonneg (h : ∀ x ∈ S, 0 ≤ φ x) : 0 ≤ averageOn S φ :=
  div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

/-- Upper bound from a pointwise bound; the nonnegativity of the bound absorbs the empty
set's junk value `0`. -/
theorem averageOn_le_of_le (h : ∀ x ∈ S, φ x ≤ c) (hc : 0 ≤ c) : averageOn S φ ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa using hc
  · have h0 : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hS
    rw [averageOn, div_le_iff₀ h0]
    calc ∑ x ∈ S, φ x ≤ ∑ _x ∈ S, c := Finset.sum_le_sum h
      _ = c * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- A `[0,1]`-valued function has a `[0,1]`-valued average, the empty set included. -/
theorem averageOn_mem_Icc (h : ∀ x ∈ S, φ x ∈ Set.Icc (0 : ℝ) 1) :
    averageOn S φ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨averageOn_nonneg fun x hx ↦ (h x hx).1, averageOn_le_of_le (fun x hx ↦ (h x hx).2) one_pos.le⟩

/-- **`densityOn` is the indicator shadow of `averageOn`.** -/
theorem averageOn_indicator (S : Finset α) (p : α → Prop) [DecidablePred p] :
    averageOn S (fun x ↦ if p x then 1 else 0) = densityOn S p := by
  rw [averageOn, densityOn, Finset.sum_boole]

/-! ### Rectangle-fiber bridges

The counting kernel average factors through `averageOn` in both orders, guard-free: an empty
side makes both sides `0`. -/

/-- Outer average over the left carrier of inner fiber averages. -/
theorem rectAverageCount_eq_averageOn_left (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) :
    rectAverageCount f A B = averageOn A fun x ↦ averageOn B (f x) := by
  simp only [rectAverageCount, rectAverage, rectSum, finsetMass, one_mul, averageOn,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Finset.sum_div, div_div, mul_comm ((B.card : ℝ)) _]

/-- Outer average over the right carrier of inner fiber averages. -/
theorem rectAverageCount_eq_averageOn_right (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) :
    rectAverageCount f A B = averageOn B fun y ↦ averageOn A fun x ↦ f x y := by
  simp only [rectAverageCount, rectAverage, rectSum, finsetMass, one_mul, averageOn,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm, ← Finset.sum_div, div_div]

/-! ### Tests and adversarial examples -/

section Tests

-- The empty set: the junk value is `0`, consistent with `densityOn`.
example : averageOn (∅ : Finset (Fin 3)) (fun _ ↦ 100) = 0 := averageOn_empty _

-- A concrete two-point average.
example : averageOn ({0, 1} : Finset (Fin 2)) (fun x ↦ (x.val : ℝ)) = 1 / 2 := by
  rw [averageOn]
  norm_num [Finset.sum_insert, Finset.mem_singleton]

-- The indicator shadow on a concrete predicate.
example : averageOn (Finset.univ : Finset (Fin 4)) (fun x ↦ if x.val < 1 then 1 else 0)
    = densityOn Finset.univ (fun x : Fin 4 ↦ x.val < 1) :=
  averageOn_indicator _ _

-- NOTE (adversarial, documented): `averageOn_le_of_le` genuinely needs `0 ≤ c` — on the
-- empty set the average is `0`, which no negative bound dominates.
example : ¬ (averageOn (∅ : Finset (Fin 3)) (fun _ ↦ -2) ≤ -1) := by
  rw [averageOn_empty]
  norm_num

end Tests

end RegularityLemmata
