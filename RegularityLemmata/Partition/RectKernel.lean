/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RectKernel
import Mathlib.Order.Partition.Finpartition

/-!
# Rectangular kernels over independent partitions

Decomposing a weighted rectangle sum along **independent** partitions of the two carriers,
and the stepped predicted sum that the Frieze–Kannan iteration will test against. The design
freeze is `docs/design/rectangular-kernels.md`.

## Two gates, pinned by the statements

**Nonnegative weights are required to divide out a mass.** `rectAverage_mul_mass` says
`rectAverage · mass = rectSum`, which is false for signed weights: a cell can have zero total
mass while carrying a nonzero rectangle sum, because positive and negative weights cancel.
With nonnegative weights, zero mass forces every weight in the cell to vanish, hence a zero
sum. Every average-level decomposition here therefore carries nonnegativity hypotheses, while
the sum-level ones do not.

**No cell mass is cancelled without splitting the zero-mass case.** The denominator-free
form `rectAverage_mul_mass_decomposition` is the primitive; the familiar weighted-average
identity is derived from it under positive mass.

The two coordinates are genuinely independent: refining the left partition leaves every
right-hand construction untouched, and conversely. `steppedRectSum` is symmetric under `op`
together with exchanging the partitions, and its two coordinate summations commute.

No Frieze–Kannan iteration and no part-count recurrence appear here.
-/

namespace RegularityLemmata

variable {X Y : Type*} {f : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ}
variable {A : Finset X} {B : Finset Y}

/-! ### Decomposition over disjoint covers -/

/-- **The exact sum decomposition**, over arbitrary pairwise-disjoint finite covers of the
two carriers. No weight hypotheses: this is an identity between sums. -/
theorem rectSum_biUnion [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) {sA : Finset (Finset X)} {sB : Finset (Finset Y)}
    (hA : (sA : Set (Finset X)).PairwiseDisjoint id)
    (hB : (sB : Set (Finset Y)).PairwiseDisjoint id) :
    rectSum f wX wY (sA.biUnion id) (sB.biUnion id)
      = ∑ p ∈ sA ×ˢ sB, rectSum f wX wY p.1 p.2 := by
  calc rectSum f wX wY (sA.biUnion id) (sB.biUnion id)
      = ∑ x ∈ sA.biUnion id, ∑ y ∈ sB.biUnion id, wX x * wY y * f x y := rfl
    _ = ∑ C ∈ sA, ∑ x ∈ id C, ∑ y ∈ sB.biUnion id, wX x * wY y * f x y :=
        Finset.sum_biUnion hA
    _ = ∑ C ∈ sA, ∑ x ∈ id C, ∑ D ∈ sB, ∑ y ∈ id D, wX x * wY y * f x y :=
        Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_biUnion hB
    _ = ∑ C ∈ sA, ∑ D ∈ sB, ∑ x ∈ id C, ∑ y ∈ id D, wX x * wY y * f x y :=
        Finset.sum_congr rfl fun C _ => Finset.sum_comm
    _ = ∑ p ∈ sA ×ˢ sB, rectSum f wX wY p.1 p.2 := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => rfl

/-- The mass of a carrier decomposes along a partition of it. -/
theorem finsetMass_finpartition [DecidableEq X] (w : X → ℝ) (P : Finpartition A) :
    finsetMass w A = ∑ C ∈ P.parts, finsetMass w C := by
  have h : finsetMass w (P.parts.biUnion id) = ∑ C ∈ P.parts, finsetMass w (id C) :=
    finsetMass_biUnion w P.supIndep.pairwiseDisjoint
  rwa [P.biUnion_parts] at h

/-- **The Finpartition wrapper**: independent partitions of the two carriers. -/
theorem rectSum_finpartition [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) :
    rectSum f wX wY A B
      = ∑ p ∈ P.parts ×ˢ Q.parts, rectSum f wX wY p.1 p.2 := by
  have h := rectSum_biUnion f wX wY P.supIndep.pairwiseDisjoint Q.supIndep.pairwiseDisjoint
  rwa [P.biUnion_parts, Q.biUnion_parts] at h

/-! ### Dividing out a mass needs nonnegative weights -/

/-- **The cancellation gate.** `rectAverage · mass = rectSum`, with the zero-mass case split
off rather than assumed away.

Nonnegativity is load-bearing: with signed weights a rectangle can have zero total mass and a
nonzero sum, and the identity fails. With nonnegative weights, zero mass forces every weight
to vanish, so both sides are `0`. -/
theorem rectAverage_mul_mass (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectAverage f wX wY A B * (finsetMass wX A * finsetMass wY B) = rectSum f wX wY A B := by
  rcases eq_or_ne (finsetMass wX A * finsetMass wY B) 0 with h | h
  · rw [rectAverage, h, div_zero, zero_mul]
    -- Zero mass with nonnegative weights forces every weight to vanish.
    rcases mul_eq_zero.mp h with hx | hy
    · have hzero : ∀ x ∈ A, wX x = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hwX).mp hx
      exact (Finset.sum_eq_zero fun x hx' => Finset.sum_eq_zero fun y _ => by
        rw [hzero x hx', zero_mul, zero_mul]).symm
    · have hzero : ∀ y ∈ B, wY y = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hwY).mp hy
      exact (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy' => by
        rw [hzero y hy', mul_zero, zero_mul]).symm
  · rw [rectAverage, div_mul_cancel₀ _ h]

/-- **The denominator-free average decomposition.** Correct on empty and zero-mass
rectangles, which is why it is the primitive form rather than the weighted-average
identity. -/
theorem rectAverage_mul_mass_decomposition [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectAverage f wX wY A B * (finsetMass wX A * finsetMass wY B)
      = ∑ p ∈ P.parts ×ˢ Q.parts,
          rectAverage f wX wY p.1 p.2 * (finsetMass wX p.1 * finsetMass wY p.2) := by
  rw [rectAverage_mul_mass hwX hwY, rectSum_finpartition f wX wY P Q]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact (rectAverage_mul_mass
    (fun x hx => hwX x ((P.le hp.1) hx)) (fun y hy => hwY y ((Q.le hp.2) hy))).symm

/-! ### The stepped predicted sum

A *predicted sum*, not a pointwise stepped kernel: the design freeze prefers this form
because a total kernel would force a convention outside the carriers' support. -/

/-- The predicted sum of `f` over a test rectangle `S ×ˢ T`, using the cell averages of the
two partitions. -/
noncomputable def steppedRectSum [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (S : Finset X) (T : Finset Y) : ℝ :=
  ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
    rectAverage f wX wY C D * (finsetMass wX (S ∩ C) * finsetMass wY (T ∩ D))

/-- **Left and right stepification commute**: the two coordinate summations are independent,
so either order gives the same predicted sum. -/
theorem steppedRectSum_comm [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (S : Finset X) (T : Finset Y) :
    steppedRectSum f wX wY P Q S T
      = ∑ D ∈ Q.parts, ∑ C ∈ P.parts,
          rectAverage f wX wY C D * (finsetMass wX (S ∩ C) * finsetMass wY (T ∩ D)) := by
  rw [steppedRectSum, Finset.sum_comm]

/-- **Consistency on the full rectangle**: at `S = A`, `T = B` the prediction is exact. This
is the statement that stepping loses nothing at the resolution of the partitions
themselves. -/
theorem steppedRectSum_self [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    steppedRectSum f wX wY P Q A B = rectSum f wX wY A B := by
  rw [steppedRectSum, rectSum_finpartition f wX wY P Q, Finset.sum_product]
  refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun D hD => ?_
  rw [Finset.inter_eq_right.mpr (P.le hC), Finset.inter_eq_right.mpr (Q.le hD)]
  exact rectAverage_mul_mass (fun x hx => hwX x ((P.le hC) hx))
    (fun y hy => hwY y ((Q.le hD) hy))

/-- **Independence of the two coordinates**: the predicted sum depends on the left partition
only through the left cell masses, so replacing the right partition leaves the left-hand
data untouched — and conversely, by `steppedRectSum_comm`. -/
theorem steppedRectSum_congr_left [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) {P P' : Finpartition A} (_Q : Finpartition B)
    (S : Finset X) (T : Finset Y) (h : P.parts = P'.parts) :
    steppedRectSum f wX wY P _Q S T = steppedRectSum f wX wY P' _Q S T := by
  rw [steppedRectSum, steppedRectSum, h]

/-! ### Transpose transport -/

/-- `op` exchanges the two sides of the predicted sum together with the two partitions. -/
theorem steppedRectSum_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (S : Finset X) (T : Finset Y) :
    steppedRectSum f.op wY wX Q P T S = steppedRectSum f wX wY P Q S T := by
  rw [steppedRectSum, steppedRectSum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => by
    rw [rectAverage_op]
    ring

/-- `op` exchanges the two sides of the decomposition. -/
theorem rectSum_finpartition_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) :
    rectSum f.op wY wX B A = ∑ p ∈ P.parts ×ˢ Q.parts, rectSum f wX wY p.1 p.2 := by
  rw [rectSum_op, rectSum_finpartition f wX wY P Q]

/-! ### Tests and adversarial examples -/

section Tests

/-- Nonuniform left weights. -/
private def uL : Fin 2 → ℝ := ![2, 3]

/-- Nonuniform right weights. -/
private def uR : Fin 3 → ℝ := ![1, 2, 3]

-- **The cancellation gate fails for signed weights.** A nonempty rectangle whose total left
-- mass is zero by cancellation, but whose rectangle sum is not zero — so the nonnegativity
-- hypothesis in `rectAverage_mul_mass` cannot be dropped.
example :
    rectSum (fun _ _ => (1 : ℝ)) (fun x : Fin 2 => if x = 0 then (1 : ℝ) else -1)
        (fun _ : Fin 1 => (1 : ℝ)) {0} Finset.univ ≠ 0 := by
  rw [rectSum]
  norm_num

example :
    finsetMass (fun x : Fin 2 => if x = 0 then (1 : ℝ) else -1) Finset.univ = 0 := by
  rw [finsetMass, Fin.sum_univ_two]
  norm_num

-- With nonnegative weights the cancellation identity holds, including at zero mass.
example (f : RectKernel (Fin 2) (Fin 3)) :
    rectAverage f (fun _ => (0 : ℝ)) uR Finset.univ Finset.univ
        * (finsetMass (fun _ : Fin 2 => (0 : ℝ)) Finset.univ * finsetMass uR Finset.univ)
      = rectSum f (fun _ => (0 : ℝ)) uR Finset.univ Finset.univ :=
  rectAverage_mul_mass (fun _ _ => le_rfl) (fun y _ => by
    fin_cases y <;> norm_num [uR])

-- The denominator-free decomposition over independent partitions, at nonuniform weights.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectAverage f uL uR Finset.univ Finset.univ
        * (finsetMass uL Finset.univ * finsetMass uR Finset.univ)
      = ∑ p ∈ P.parts ×ˢ Q.parts,
          rectAverage f uL uR p.1 p.2 * (finsetMass uL p.1 * finsetMass uR p.2) :=
  rectAverage_mul_mass_decomposition P Q
    (fun x _ => by fin_cases x <;> norm_num [uL])
    (fun y _ => by fin_cases y <;> norm_num [uR])

-- **Empty carrier**: every decomposition is `0 = 0`.
example (f : RectKernel (Fin 2) (Fin 3)) :
    rectSum f uL uR ∅ Finset.univ = 0 := rectSum_empty_left _ _ _ _

-- Left and right stepification commute.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (S : Finset (Fin 2))
    (T : Finset (Fin 3)) :
    steppedRectSum f uL uR P Q S T
      = ∑ D ∈ Q.parts, ∑ C ∈ P.parts,
          rectAverage f uL uR C D * (finsetMass uL (S ∩ C) * finsetMass uR (T ∩ D)) :=
  steppedRectSum_comm f uL uR P Q S T

end Tests

end RegularityLemmata
