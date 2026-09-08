/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Kernel

/-!
# Worked specialization 3: a signed residual

The decomposition applies to **signed** kernels, and the typical signed kernel is a residual: a
kernel minus a prediction. Here the prediction is the kernel's own average on the whole
rectangle, so the residual `f − rectAverage f A B` has values in `[-2, 2]` when `f` has values in
`[-1, 1]`. Rescaling by `1/2` makes it unit-bounded, and the decomposition of the rescaled
residual, read back at scale `2`, gives at most `⌈1/ε²⌉₊` rectangles with coefficients at most
`2/ε` and a residual cut norm at most `2ε · M`. The point of the example is the bookkeeping of a
signed, non-indicator kernel; nothing here assumes `f ≥ 0`.

Only the advertised import `RegularityLemmata.Kernel` is used.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] {A : Finset X} {B : Finset Y}

omit [DecidableEq X] [DecidableEq Y] in
/-- The centred residual of a unit-bounded kernel is `2`-bounded on the rectangle, under
nonnegative weights. -/
theorem residual_absBounded (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) :
    IsAbsBoundedOnRectangle (fun x y => f x y - rectAverage f wX wY A B) 2 A B := by
  intro x hx y hy
  have h1 := hf x hx y hy
  have h2 := abs_rectAverage_le (by norm_num : (0 : ℝ) ≤ 1) hwX hwY hf
  calc |f x y - rectAverage f wX wY A B| ≤ |f x y| + |rectAverage f wX wY A B| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- **Decomposing a signed residual.** The centred residual of a unit-bounded kernel is a
combination of at most `⌈1/ε²⌉₊` weighted rectangles with coefficients at most `2/ε`, plus a
residual of cut norm at most `2ε · M`. -/
theorem signedResidual_cutDecomposition (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset X) (T : Fin k → Finset Y),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ l, |c l| ≤ 2 / ε) ∧
      (∀ l, S l ⊆ A ∧ T l ⊆ B) ∧
      rectCutNorm (fun x y => (f x y - rectAverage f wX wY A B) - rectCombination c S T x y)
        wX wY A B ≤ 2 * ε * (finsetMass wX A * finsetMass wY B) := by
  -- Rescale the residual to unit boundedness.
  set g : RectKernel X Y := fun x y => (f x y - rectAverage f wX wY A B) / 2 with hg
  have hgb : IsAbsUnitBoundedOnRectangle g A B := by
    intro x hx y hy
    have := residual_absBounded f wX wY hwX hwY hf x hx y hy
    rw [hg]
    simp only
    rw [abs_div, abs_two]
    linarith
  obtain ⟨k, c, S, T, hk, hc, hST, hcut⟩ :=
    kernel_frieze_kannan_cutDecomposition g wX wY hwX hwY hgb hε
  refine ⟨k, fun l => 2 * c l, S, T, hk, fun l => ?_, hST, ?_⟩
  · rw [abs_mul, abs_two]
    calc 2 * |c l| ≤ 2 * (1 / ε) := by nlinarith [hc l]
      _ = 2 / ε := by ring
  · -- The rescaled residual is `2` times the decomposition's residual, and the cut norm scales.
    have hscale : (fun x y => (f x y - rectAverage f wX wY A B)
        - rectCombination (fun l => 2 * c l) S T x y)
        = fun x y => 2 * (g x y - rectCombination c S T x y) := by
      funext x y
      simp only [hg, rectCombination_apply, mul_sub, Finset.mul_sum, mul_assoc]
      ring
    rw [hscale]
    have hle := rectCutNorm_le_iff.mp hcut
    rw [rectCutNorm_le_iff]
    intro S' hS' T' hT'
    rw [rectSum_smul, abs_mul, abs_two]
    have := hle S' hS' T' hT'
    linarith

end RegularityLemmataExamples
