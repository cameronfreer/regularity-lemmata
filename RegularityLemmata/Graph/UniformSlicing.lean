/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Uniformity

/-!
# Route (b) step 2: slicing inheritance for uniform pairs

`ARCHITECTURE.md` route (b) ladder, step 2 (design freeze 2026-07-20): if `(A, B)` is
`ε`-uniform and `W_A ⊆ A`, `W_B ⊆ B` retain fractions `κ_A, κ_B ≥ ε` of their hosts,
then the slice density stays within `ε` of the host density
(`IsUniformPair.slice_density_close`) and `(W_A, W_B)` is uniform at every tolerance
`ε'` with `ε ≤ ε'·κ_A`, `ε ≤ ε'·κ_B`, and `2ε ≤ ε'` (`IsUniformPair.slice`) — in
particular at `ε' = max (ε/κ) (2ε)`.

The degradation is structural, not an artifact: a sub-block that is `ε'`-large in the
slice is only `ε'·κ`-large in the host (the `1/κ` factor), and the deviation is routed
through the host density by the triangle inequality (the doubling). Fraction
hypotheses are in **multiplication form** (`κ·|A| ≤ |W_A|`), per the frozen Unit 7
discipline — never natural-number division.

Load-bearing for route (b) step 1 (trimming the pairwise-uniform collection to
comparable sizes) and step 3 (the one-subset representative theorem).
-/

namespace RegularityLemmata

variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {A B WA WB : Finset α}
  {ε ε' κA κB : ℝ}

/-- **Density control under slicing**: a slice retaining a `κ ≥ ε` fraction of each
side of an `ε`-uniform pair has density within `ε` of the host pair's. -/
theorem IsUniformPair.slice_density_close (h : IsUniformPair R A B ε)
    (hWA : WA ⊆ A) (hWB : WB ⊆ B) (hκA : ε ≤ κA) (hκB : ε ≤ κB)
    (hA : κA * (A.card : ℝ) ≤ (WA.card : ℝ))
    (hB : κB * (B.card : ℝ) ≤ (WB.card : ℝ)) :
    |pairDensity R WA WB - pairDensity R A B| ≤ ε :=
  h hWA hWB
    (le_trans (mul_le_mul_of_nonneg_right hκA (Nat.cast_nonneg _)) hA)
    (le_trans (mul_le_mul_of_nonneg_right hκB (Nat.cast_nonneg _)) hB)

/-- **Slicing inheritance**: slices retaining `κ_A, κ_B ≥ ε` fractions of an
`ε`-uniform pair are `ε'`-uniform whenever `ε ≤ ε'·κ_A`, `ε ≤ ε'·κ_B`, and
`2ε ≤ ε'`. -/
theorem IsUniformPair.slice (hε : 0 ≤ ε) (h : IsUniformPair R A B ε)
    (hWA : WA ⊆ A) (hWB : WB ⊆ B) (hκA : ε ≤ κA) (hκB : ε ≤ κB)
    (hA : κA * (A.card : ℝ) ≤ (WA.card : ℝ))
    (hB : κB * (B.card : ℝ) ≤ (WB.card : ℝ))
    (hε'A : ε ≤ ε' * κA) (hε'B : ε ≤ ε' * κB) (hε2 : 2 * ε ≤ ε') :
    IsUniformPair R WA WB ε' := by
  intro X' hX' Y' hY' hXc hYc
  have hε' : 0 ≤ ε' := le_trans (by linarith) hε2
  -- An `ε'`-large sub-block of the slice is `ε`-large in the host.
  have hXA : ε * (A.card : ℝ) ≤ (X'.card : ℝ) := by
    calc ε * (A.card : ℝ)
        ≤ ε' * κA * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_right hε'A (Nat.cast_nonneg _)
      _ = ε' * (κA * (A.card : ℝ)) := mul_assoc _ _ _
      _ ≤ ε' * (WA.card : ℝ) := mul_le_mul_of_nonneg_left hA hε'
      _ ≤ (X'.card : ℝ) := hXc
  have hYB : ε * (B.card : ℝ) ≤ (Y'.card : ℝ) := by
    calc ε * (B.card : ℝ)
        ≤ ε' * κB * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right hε'B (Nat.cast_nonneg _)
      _ = ε' * (κB * (B.card : ℝ)) := mul_assoc _ _ _
      _ ≤ ε' * (WB.card : ℝ) := mul_le_mul_of_nonneg_left hB hε'
      _ ≤ (Y'.card : ℝ) := hYc
  have h1 : |pairDensity R X' Y' - pairDensity R A B| ≤ ε :=
    h (hX'.trans hWA) (hY'.trans hWB) hXA hYB
  have h2 : |pairDensity R WA WB - pairDensity R A B| ≤ ε :=
    h.slice_density_close hWA hWB hκA hκB hA hB
  calc |pairDensity R X' Y' - pairDensity R WA WB|
      ≤ |pairDensity R X' Y' - pairDensity R A B|
        + |pairDensity R A B - pairDensity R WA WB| := abs_sub_le _ _ _
    _ ≤ ε + ε := add_le_add h1 (by rw [abs_sub_comm]; exact h2)
    _ ≤ ε' := by linarith

/-! ### Tests -/

section Tests

-- The trivial slice (`κ = 1`, `W = A`) recovers the pair at the doubled tolerance:
-- the degradation specializes exactly to the triangle-inequality factor.
example (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : IsUniformPair R A B ε) :
    IsUniformPair R A B (2 * ε) :=
  h.slice hε subset_rfl subset_rfl hε1 hε1 (by norm_num) (by norm_num)
    (by nlinarith) (by nlinarith) le_rfl

-- Composition with monotonicity: any slice tolerance may be relaxed onward.
example (hε : 0 ≤ ε) (h : IsUniformPair R A B ε)
    (hWA : WA ⊆ A) (hWB : WB ⊆ B) (hκA : ε ≤ κA) (hκB : ε ≤ κB)
    (hA : κA * (A.card : ℝ) ≤ (WA.card : ℝ))
    (hB : κB * (B.card : ℝ) ≤ (WB.card : ℝ))
    (hε'A : ε ≤ ε' * κA) (hε'B : ε ≤ ε' * κB) (hε2 : 2 * ε ≤ ε')
    {ε'' : ℝ} (hε'' : ε' ≤ ε'') :
    IsUniformPair R WA WB ε'' :=
  (h.slice hε hWA hWB hκA hκB hA hB hε'A hε'B hε2).mono hε''

end Tests

end RegularityLemmata
