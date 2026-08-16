/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.Basic
import RegularityLemmata.Partition.RectKernel

/-!
# Rectangular kernel energy and the parallel-axis identity

The energy of a rectangular weighted kernel against a pair of **independent** partitions,
and the exact identity relating a refinement's energy gain to the mass-weighted variance of
the refined cell averages. The design freeze is `docs/design/rectangular-kernels.md`.

`rectBlockEnergy` is the mass-weighted square of a cell's average; `rectEnergyNum` sums it
over the product of the two partitions' parts; `rectEnergy` normalizes by the rectangle
mass, guard-free.

## The zero-mass principle

Every proof here follows the same rule, and it is the reason nonnegativity of the carrier
weights is a hypothesis throughout: **no parent or child mass is cancelled before the
zero-mass case is split off**. Under nonnegative weights a vanishing parent mass forces
every child mass to vanish too, so both sides of each identity collapse to `0`; with signed
weights that implication fails and so do the identities.

## The parallel-axis identity

`rectEnergyNum_sub_rectBlockEnergy` is the heart: the energy gained by passing from the
single block `A ×ˢ B` to the cells of `P ×ˢ Q` is exactly the mass-weighted variance of the
cell averages around the parent average. Refinement monotonicity is its nonnegativity, and
is recorded as an immediate corollary rather than proved separately.

## Refinement of a partition pair

What the Frieze–Kannan iteration consumes is the comparison of two partition **pairs**, and
`rectEnergyNum_eq_add_rectRefinementVarianceNum` is that statement: under `P' ≤ P` and
`Q' ≤ Q` the energy gain is exactly `rectRefinementVarianceNum`. It is the **primitive**
here — the left-only identity is its specialization at `Q' = Q`, the right-only identity is
transported from the left-only one through `op`, and all three monotonicity statements are
corollaries of nonnegativity. Downstream files must consume these rather than construct a
private substitute.

Following `refinementVarianceNum` in `Graph/Strong.lean`, the variance definition is
**proof-free**: refinement hypotheses enter the identity theorems, never the data.

No Frieze–Kannan iteration and no part-count recurrence appear here.
-/

namespace RegularityLemmata

variable {X Y : Type*} {f : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ}
variable {A : Finset X} {B : Finset Y}

/-! ### Block energy -/

/-- The energy of one rectangle: its average squared, weighted by its mass. -/
noncomputable def rectBlockEnergy (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  rectAverage f wX wY A B ^ 2 * (finsetMass wX A * finsetMass wY B)

theorem rectBlockEnergy_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectBlockEnergy f wX wY A B :=
  mul_nonneg (sq_nonneg _)
    (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))

/-- **The mass upper bound.** For an absolutely unit-bounded kernel the block energy is at
most the block's mass. Guard-free: at zero mass both sides are `0`. -/
theorem rectBlockEnergy_le_mass (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) :
    rectBlockEnergy f wX wY A B ≤ finsetMass wX A * finsetMass wY B := by
  have habs := abs_rectAverage_le (by norm_num : (0:ℝ) ≤ 1) hwX hwY hf
  have hsq : rectAverage f wX wY A B ^ 2 ≤ 1 := by
    have := abs_le.mp habs
    nlinarith [this.1, this.2]
  calc rectBlockEnergy f wX wY A B
      ≤ 1 * (finsetMass wX A * finsetMass wY B) :=
        mul_le_mul_of_nonneg_right hsq
          (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))
    _ = finsetMass wX A * finsetMass wY B := one_mul _

/-! ### Energy over a pair of partitions -/

/-- The un-normalized energy of `f` against independent partitions of the two carriers. -/
noncomputable def rectEnergyNum [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) : ℝ :=
  ∑ p ∈ P.parts ×ˢ Q.parts, rectBlockEnergy f wX wY p.1 p.2

/-- The normalized energy, guard-free: `0` when the rectangle has zero mass. -/
noncomputable def rectEnergy [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) : ℝ :=
  rectEnergyNum f wX wY P Q / (finsetMass wX A * finsetMass wY B)

/-- The rectangle mass factors over the product of the two partitions' parts. -/
theorem sum_mass_product [DecidableEq X] [DecidableEq Y] (wX : X → ℝ) (wY : Y → ℝ)
    (P : Finpartition A) (Q : Finpartition B) :
    ∑ p ∈ P.parts ×ˢ Q.parts, (finsetMass wX p.1 * finsetMass wY p.2)
      = finsetMass wX A * finsetMass wY B := by
  rw [Finset.sum_product, ← Finset.sum_mul_sum, ← finsetMass_finpartition wX P,
    ← finsetMass_finpartition wY Q]

theorem rectEnergyNum_nonneg [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectEnergyNum f wX wY P Q := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact rectBlockEnergy_nonneg (fun x hx => hwX x ((P.le hp.1) hx))
    (fun y hy => hwY y ((Q.le hp.2) hy))

theorem rectEnergyNum_le_mass [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) :
    rectEnergyNum f wX wY P Q ≤ finsetMass wX A * finsetMass wY B := by
  rw [← sum_mass_product wX wY P Q]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact rectBlockEnergy_le_mass (fun x hx => hwX x ((P.le hp.1) hx))
    (fun y hy => hwY y ((Q.le hp.2) hy))
    (fun x hx y hy => hf x ((P.le hp.1) hx) y ((Q.le hp.2) hy))

theorem rectEnergy_nonneg [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectEnergy f wX wY P Q :=
  div_nonneg (rectEnergyNum_nonneg P Q hwX hwY)
    (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))

/-- **Guard-free `≤ 1`.** At zero rectangle mass the normalized energy is `0/0 = 0`, so no
positive-mass hypothesis is needed. -/
theorem rectEnergy_le_one [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) : rectEnergy f wX wY P Q ≤ 1 := by
  have hm : 0 ≤ finsetMass wX A * finsetMass wY B :=
    mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  rcases eq_or_lt_of_le hm with h | h
  · rw [rectEnergy, ← h, div_zero]
    norm_num
  · rw [rectEnergy, div_le_one h]
    exact rectEnergyNum_le_mass P Q hwX hwY hf

/-! ### The parallel-axis identity -/

/-- The mass-weighted variance of the cell averages around the parent average. -/
noncomputable def rectVarianceNum [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) : ℝ :=
  ∑ p ∈ P.parts ×ˢ Q.parts,
    (rectAverage f wX wY p.1 p.2 - rectAverage f wX wY A B) ^ 2
      * (finsetMass wX p.1 * finsetMass wY p.2)

theorem rectVarianceNum_nonneg [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectVarianceNum f wX wY P Q := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (finsetMass_nonneg fun x hx => hwX x ((P.le hp.1) hx))
      (finsetMass_nonneg fun y hy => hwY y ((Q.le hp.2) hy)))

/-- **The parallel-axis identity.** Passing from the single block `A ×ˢ B` to the cells of
`P ×ˢ Q` gains exactly the mass-weighted variance of the cell averages.

Both cancellations it needs — the first moment and the total mass — come from the
denominator-free decompositions of `Partition/RectKernel.lean`, so no mass is divided out
and the zero-mass case is handled uniformly. -/
theorem rectEnergyNum_sub_rectBlockEnergy [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P Q - rectBlockEnergy f wX wY A B
      = rectVarianceNum f wX wY P Q := by
  classical
  set μ := rectAverage f wX wY A B with hμ
  -- The first moment: the cell sums recombine to the parent's.
  have hfirst : ∑ p ∈ P.parts ×ˢ Q.parts,
      rectAverage f wX wY p.1 p.2 * (finsetMass wX p.1 * finsetMass wY p.2)
      = μ * (finsetMass wX A * finsetMass wY B) :=
    (rectAverage_mul_mass_decomposition P Q hwX hwY).symm
  -- The zeroth moment: the cell masses recombine to the parent's.
  have hzeroth := sum_mass_product wX wY P Q
  rw [rectEnergyNum, rectVarianceNum, rectBlockEnergy, ← hμ]
  have hexpand : ∀ p ∈ P.parts ×ˢ Q.parts,
      (rectAverage f wX wY p.1 p.2 - μ) ^ 2 * (finsetMass wX p.1 * finsetMass wY p.2)
        = rectBlockEnergy f wX wY p.1 p.2
          - 2 * μ * (rectAverage f wX wY p.1 p.2
              * (finsetMass wX p.1 * finsetMass wY p.2))
          + μ ^ 2 * (finsetMass wX p.1 * finsetMass wY p.2) := by
    intro p _
    rw [rectBlockEnergy]
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hfirst, hzeroth]
  ring

/-- **Refinement monotonicity**, an immediate corollary: the cells of `P ×ˢ Q` carry at
least the energy of the single block they refine. -/
theorem rectBlockEnergy_le_rectEnergyNum [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectBlockEnergy f wX wY A B ≤ rectEnergyNum f wX wY P Q := by
  have h := rectEnergyNum_sub_rectBlockEnergy (f := f) P Q hwX hwY
  have hv := rectVarianceNum_nonneg (f := f) P Q hwX hwY
  linarith

/-! ### Transpose transport -/

/-- `op` exchanges the two sides of the block energy. -/
theorem rectBlockEnergy_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectBlockEnergy f.op wY wX B A = rectBlockEnergy f wX wY A B := by
  rw [rectBlockEnergy, rectBlockEnergy, rectAverage_op, mul_comm (finsetMass wY B)]

/-- …and of the total energy. -/
theorem rectEnergyNum_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) :
    rectEnergyNum f.op wY wX Q P = rectEnergyNum f wX wY P Q := by
  rw [rectEnergyNum, rectEnergyNum, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ =>
    rectBlockEnergy_op f wX wY C D

/-! ### Refinement of a partition pair

The parallel-axis identity above compares a partition pair against the *single block* it
refines. The identity the Frieze–Kannan iteration actually consumes compares two partition
**pairs**, `P' ≤ P` and `Q' ≤ Q`. That joint statement is the primitive here; the one-sided
identities are specializations of it, at `Q' = Q` and at `P' = P`.

Following `refinementVarianceNum` in `Graph/Strong.lean`, the variance is **proof-free**: it
is defined for arbitrary partition pairs by filtering the fine parts inside each coarse part,
and the refinement hypotheses enter the identity theorem rather than the definition. -/

/-- The mass-weighted variance of the cells of `P' ×ˢ Q'` around the cells of `P ×ˢ Q` that
contain them. Proof-free: `P' ≤ P` and `Q' ≤ Q` are *not* required to state it. -/
noncomputable def rectRefinementVarianceNum [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (P' : Finpartition A) (Q' : Finpartition B) : ℝ :=
  ∑ pd ∈ P.parts ×ˢ Q.parts,
    ∑ p ∈ (P'.parts.filter (· ⊆ pd.1)) ×ˢ (Q'.parts.filter (· ⊆ pd.2)),
      (rectAverage f wX wY p.1 p.2 - rectAverage f wX wY pd.1 pd.2) ^ 2
        * (finsetMass wX p.1 * finsetMass wY p.2)

theorem rectRefinementVarianceNum_nonneg [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B) (P' : Finpartition A) (Q' : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectRefinementVarianceNum f wX wY P Q P' Q' := by
  refine Finset.sum_nonneg fun pd _ => Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (finsetMass_nonneg fun x hx => hwX x ((P'.le hp.1.1) hx))
      (finsetMass_nonneg fun y hy => hwY y ((Q'.le hp.2.1) hy)))

/-- Summing over the fine parts inside each coarse cell recovers the sum over all fine
cells — the two-coordinate form of `sum_over_parents`. -/
theorem sum_product_parts_eq_sum_over_parents [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q Q' : Finpartition B} (hP : P' ≤ P) (hQ : Q' ≤ Q)
    (g : Finset X → Finset Y → ℝ) :
    ∑ pd ∈ P.parts ×ˢ Q.parts,
        ∑ p ∈ (P'.parts.filter (· ⊆ pd.1)) ×ˢ (Q'.parts.filter (· ⊆ pd.2)), g p.1 p.2
      = ∑ p ∈ P'.parts ×ˢ Q'.parts, g p.1 p.2 := by
  classical
  rw [Finset.sum_product, Finset.sum_product]
  calc ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
        ∑ p ∈ (P'.parts.filter (· ⊆ C)) ×ˢ (Q'.parts.filter (· ⊆ D)), g p.1 p.2
      = ∑ C ∈ P.parts, ∑ C' ∈ P'.parts.filter (· ⊆ C),
          ∑ D ∈ Q.parts, ∑ D' ∈ Q'.parts.filter (· ⊆ D), g C' D' := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun D _ => by rw [Finset.sum_product]
    _ = ∑ C ∈ P.parts, ∑ C' ∈ P'.parts.filter (· ⊆ C), ∑ D' ∈ Q'.parts, g C' D' :=
        Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun C' _ =>
          sum_over_parents hQ (g C')
    _ = ∑ C' ∈ P'.parts, ∑ D' ∈ Q'.parts, g C' D' :=
        sum_over_parents hP fun C' => ∑ D' ∈ Q'.parts, g C' D'

/-- **The refinement-pair parallel-axis identity.** Refining *both* partitions gains exactly
the mass-weighted variance of the fine cell averages around the coarse ones.

This is the primitive: the one-sided identities below are specializations, not separate
proofs. Each coarse cell contributes its own copy of `rectEnergyNum_sub_rectBlockEnergy`,
applied to the fine parts inside it via `refinementOnPart`. -/
theorem rectEnergyNum_eq_add_rectRefinementVarianceNum [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q Q' : Finpartition B} (hP : P' ≤ P) (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P' Q'
      = rectEnergyNum f wX wY P Q + rectRefinementVarianceNum f wX wY P Q P' Q' := by
  classical
  have hcell : ∀ pd ∈ P.parts ×ˢ Q.parts,
      ∑ p ∈ (P'.parts.filter (· ⊆ pd.1)) ×ˢ (Q'.parts.filter (· ⊆ pd.2)),
          rectBlockEnergy f wX wY p.1 p.2
        = rectBlockEnergy f wX wY pd.1 pd.2
          + ∑ p ∈ (P'.parts.filter (· ⊆ pd.1)) ×ˢ (Q'.parts.filter (· ⊆ pd.2)),
              (rectAverage f wX wY p.1 p.2 - rectAverage f wX wY pd.1 pd.2) ^ 2
                * (finsetMass wX p.1 * finsetMass wY p.2) := by
    rintro ⟨C, D⟩ hpd
    rw [Finset.mem_product] at hpd
    have h := rectEnergyNum_sub_rectBlockEnergy (f := f) (wX := wX) (wY := wY)
      (refinementOnPart hP hpd.1) (refinementOnPart hQ hpd.2)
      (fun x hx => hwX x ((P.le hpd.1) hx)) (fun y hy => hwY y ((Q.le hpd.2) hy))
    rw [rectEnergyNum, rectVarianceNum, parts_refinementOnPart, parts_refinementOnPart] at h
    linarith
  rw [rectEnergyNum,
    ← sum_product_parts_eq_sum_over_parents hP hQ
      (fun C' D' => rectBlockEnergy f wX wY C' D'),
    rectRefinementVarianceNum, rectEnergyNum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hcell

/-- **Left-only refinement**, by taking `Q' = Q`. -/
theorem rectEnergyNum_eq_add_rectRefinementVarianceNum_left [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q : Finpartition B} (hP : P' ≤ P)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P' Q
      = rectEnergyNum f wX wY P Q + rectRefinementVarianceNum f wX wY P Q P' Q :=
  rectEnergyNum_eq_add_rectRefinementVarianceNum hP le_rfl hwX hwY

/-- With the right partition unrefined the inner right sum collapses to the coarse cell
itself, so the left-only variance is a single sum over the refined left parts. -/
theorem rectRefinementVarianceNum_right_self [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B) (P' : Finpartition A) :
    rectRefinementVarianceNum f wX wY P Q P' Q
      = ∑ pd ∈ P.parts ×ˢ Q.parts, ∑ C' ∈ P'.parts.filter (· ⊆ pd.1),
          (rectAverage f wX wY C' pd.2 - rectAverage f wX wY pd.1 pd.2) ^ 2
            * (finsetMass wX C' * finsetMass wY pd.2) := by
  classical
  refine Finset.sum_congr rfl fun pd hpd => ?_
  rw [Finset.mem_product] at hpd
  rw [parts_filter_subset_eq_singleton hpd.2, Finset.sum_product]
  exact Finset.sum_congr rfl fun C' _ => Finset.sum_singleton _ _

/-- `op` exchanges the two sides of the refinement variance, together with both partition
pairs. -/
theorem rectRefinementVarianceNum_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (P' : Finpartition A) (Q' : Finpartition B) :
    rectRefinementVarianceNum f.op wY wX Q P Q' P'
      = rectRefinementVarianceNum f wX wY P Q P' Q' := by
  classical
  rw [rectRefinementVarianceNum, rectRefinementVarianceNum, Finset.sum_product,
    Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl fun C' _ => Finset.sum_congr rfl fun D' _ => by
    rw [rectAverage_op, rectAverage_op, mul_comm (finsetMass wY D')]

/-- The mirror collapse: with the left partition unrefined, the left-only variance is a
single sum over the refined right parts. Transported from
`rectRefinementVarianceNum_right_self` through `op`. -/
theorem rectRefinementVarianceNum_left_self [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (Q' : Finpartition B) :
    rectRefinementVarianceNum f wX wY P Q P Q'
      = ∑ pd ∈ P.parts ×ˢ Q.parts, ∑ D' ∈ Q'.parts.filter (· ⊆ pd.2),
          (rectAverage f wX wY pd.1 D' - rectAverage f wX wY pd.1 pd.2) ^ 2
            * (finsetMass wX pd.1 * finsetMass wY D') := by
  classical
  have h := rectRefinementVarianceNum_right_self (f := f.op) (wX := wY) (wY := wX) Q P Q'
  rw [rectRefinementVarianceNum_op] at h
  rw [h, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ =>
    Finset.sum_congr rfl fun D' _ => by
      rw [rectAverage_op, rectAverage_op, mul_comm (finsetMass wY D')]

/-- **Right-only refinement**, derived from the left-only identity through `op` rather than
reproved. -/
theorem rectEnergyNum_eq_add_rectRefinementVarianceNum_right [DecidableEq X] [DecidableEq Y]
    {P : Finpartition A} {Q Q' : Finpartition B} (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P Q'
      = rectEnergyNum f wX wY P Q + rectRefinementVarianceNum f wX wY P Q P Q' := by
  have h := rectEnergyNum_eq_add_rectRefinementVarianceNum_left (f := f.op) (wX := wY)
    (wY := wX) (P := Q) (P' := Q') (Q := P) hQ hwY hwX
  rwa [rectEnergyNum_op, rectEnergyNum_op, rectRefinementVarianceNum_op] at h

/-! ### Monotonicity

All three monotonicity statements are immediate corollaries of the corresponding identity
together with `rectRefinementVarianceNum_nonneg`; none needs its own argument. -/

theorem rectEnergyNum_le_rectEnergyNum [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q Q' : Finpartition B} (hP : P' ≤ P) (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P Q ≤ rectEnergyNum f wX wY P' Q' := by
  have h := rectEnergyNum_eq_add_rectRefinementVarianceNum (f := f) hP hQ hwX hwY
  have hv := rectRefinementVarianceNum_nonneg (f := f) P Q P' Q' hwX hwY
  linarith

theorem rectEnergyNum_le_rectEnergyNum_left [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q : Finpartition B} (hP : P' ≤ P)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P Q ≤ rectEnergyNum f wX wY P' Q :=
  rectEnergyNum_le_rectEnergyNum hP le_rfl hwX hwY

theorem rectEnergyNum_le_rectEnergyNum_right [DecidableEq X] [DecidableEq Y]
    {P : Finpartition A} {Q Q' : Finpartition B} (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergyNum f wX wY P Q ≤ rectEnergyNum f wX wY P Q' :=
  rectEnergyNum_le_rectEnergyNum le_rfl hQ hwX hwY

/-! ### Normalized forms

Dividing the identity by the fixed rectangle mass is guard-free: at zero mass every term is
`0/0 = 0` and the identity reads `0 = 0 + 0`. -/

theorem rectEnergy_eq_add_rectRefinementVarianceNum [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q Q' : Finpartition B} (hP : P' ≤ P) (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergy f wX wY P' Q'
      = rectEnergy f wX wY P Q
        + rectRefinementVarianceNum f wX wY P Q P' Q'
            / (finsetMass wX A * finsetMass wY B) := by
  rw [rectEnergy, rectEnergy, ← add_div,
    rectEnergyNum_eq_add_rectRefinementVarianceNum hP hQ hwX hwY]

theorem rectEnergy_le_rectEnergy [DecidableEq X] [DecidableEq Y]
    {P P' : Finpartition A} {Q Q' : Finpartition B} (hP : P' ≤ P) (hQ : Q' ≤ Q)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectEnergy f wX wY P Q ≤ rectEnergy f wX wY P' Q' := by
  have hm : 0 ≤ finsetMass wX A * finsetMass wY B :=
    mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  rcases eq_or_lt_of_le hm with h | h
  · rw [rectEnergy, rectEnergy, ← h, div_zero, div_zero]
  · rw [rectEnergy, rectEnergy, div_le_div_iff_of_pos_right h]
    exact rectEnergyNum_le_rectEnergyNum hP hQ hwX hwY

/-! ### Tests and adversarial examples -/

section Tests

private def vL : Fin 2 → ℝ := ![2, 3]
private def vR : Fin 3 → ℝ := ![1, 2, 3]

-- **Rescaling one carrier weight leaves the block energy's average factor fixed**, so the
-- energy scales exactly with the mass — the invariance the design freeze asks for.
example (f : RectKernel (Fin 2) (Fin 3)) (A : Finset (Fin 2)) (B : Finset (Fin 3)) :
    rectBlockEnergy f (fun x => 5 * vL x) vR A B
      = rectAverage f vL vR A B ^ 2 * (5 * finsetMass vL A * finsetMass vR B) := by
  rw [rectBlockEnergy, rectAverage_smul_weight_left (by norm_num) f vL vR A B,
    finsetMass_smul]

-- **Zero mass**: the normalized energy is `0`, not undefined, and the `≤ 1` bound survives.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3)))
    (hf : IsAbsUnitBoundedOnRectangle f Finset.univ Finset.univ) :
    rectEnergy f (fun _ => (0 : ℝ)) vR P Q ≤ 1 :=
  rectEnergy_le_one P Q (fun _ _ => le_rfl)
    (fun y _ => by fin_cases y <;> norm_num [vR]) hf

-- Refinement monotonicity at nonuniform weights.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectBlockEnergy f vL vR Finset.univ Finset.univ
      ≤ rectEnergyNum f vL vR P Q :=
  rectBlockEnergy_le_rectEnergyNum P Q
    (fun x _ => by fin_cases x <;> norm_num [vL])
    (fun y _ => by fin_cases y <;> norm_num [vR])

-- `op` transport of the total energy, between genuinely different carriers.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectEnergyNum f.op vR vL Q P = rectEnergyNum f vL vR P Q :=
  rectEnergyNum_op f vL vR P Q

private theorem hvL : ∀ x ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ vL x :=
  fun x _ => by fin_cases x <;> norm_num [vL]

private theorem hvR : ∀ y ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ vR y :=
  fun y _ => by fin_cases y <;> norm_num [vR]

-- **Only the left partition refines**: the right one is carried along unchanged.
example (f : RectKernel (Fin 2) (Fin 3)) {P P' : Finpartition (Finset.univ : Finset (Fin 2))}
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (hP : P' ≤ P) :
    rectEnergyNum f vL vR P' Q
      = rectEnergyNum f vL vR P Q + rectRefinementVarianceNum f vL vR P Q P' Q :=
  rectEnergyNum_eq_add_rectRefinementVarianceNum_left hP hvL hvR

-- **Only the right partition refines** — the `op`-derived identity.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    {Q Q' : Finpartition (Finset.univ : Finset (Fin 3))} (hQ : Q' ≤ Q) :
    rectEnergyNum f vL vR P Q'
      = rectEnergyNum f vL vR P Q + rectRefinementVarianceNum f vL vR P Q P Q' :=
  rectEnergyNum_eq_add_rectRefinementVarianceNum_right hQ hvL hvR

-- **Both refine**: the joint primitive, and its normalized form.
example (f : RectKernel (Fin 2) (Fin 3)) {P P' : Finpartition (Finset.univ : Finset (Fin 2))}
    {Q Q' : Finpartition (Finset.univ : Finset (Fin 3))} (hP : P' ≤ P) (hQ : Q' ≤ Q) :
    rectEnergy f vL vR P' Q'
      = rectEnergy f vL vR P Q
        + rectRefinementVarianceNum f vL vR P Q P' Q'
            / (finsetMass vL Finset.univ * finsetMass vR Finset.univ) :=
  rectEnergy_eq_add_rectRefinementVarianceNum hP hQ hvL hvR

-- **`op` exchanges the two one-sided identities**: a right-only refinement variance on `f`
-- is a left-only one on `f.op`, so neither side needs its own proof.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q Q' : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectRefinementVarianceNum f.op vR vL Q P Q' P
      = rectRefinementVarianceNum f vL vR P Q P Q' :=
  rectRefinementVarianceNum_op f vL vR P Q P Q'

/-! #### Concrete degenerate and nondegenerate cells

The abstract tests above are instances of the identities; these compute both sides on a
two-point carrier, where the refinement is `⊥ ≤ indiscrete`. -/

/-- A kernel that is nonconstant across the left carrier — the reason the variance is
strictly positive below. -/
private def kNC : RectKernel (Fin 2) (Fin 1) := fun x _ => if x = 0 then (1 : ℝ) else 0

/-- Left weights with a **zero-mass child**: the parent `{0, 1}` has mass `1`, but the
child `{1}` has mass `0`. -/
private def w10 : Fin 2 → ℝ := ![1, 0]

private theorem hA2 : ({0, 1} : Finset (Fin 2)) ≠ ⊥ := by decide
private theorem hB1 : ({0} : Finset (Fin 1)) ≠ ⊥ := by decide

private noncomputable def PI : Finpartition ({0, 1} : Finset (Fin 2)) :=
  Finpartition.indiscrete hA2

private noncomputable def QI : Finpartition ({0} : Finset (Fin 1)) :=
  Finpartition.indiscrete hB1

-- The singleton partition refines the indiscrete one, so the identities apply.
example : (⊥ : Finpartition ({0, 1} : Finset (Fin 2))) ≤ PI := bot_le

-- **Strictly positive variance.** Splitting `{0, 1}` separates the kernel's two values, and
-- the refinement variance is `1/4 + 1/4 > 0` — so the identity is not vacuous and the
-- monotonicity corollaries are not equalities in general.
example : 0 < rectRefinementVarianceNum kNC (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    PI QI ⊥ QI := by
  rw [rectRefinementVarianceNum, PI, QI, Finpartition.indiscrete_parts,
    Finpartition.indiscrete_parts]
  norm_num [rectAverage, rectSum, finsetMass, kNC, Finset.filter_insert,
    Finset.filter_singleton]

-- **A zero-mass child inside a positive-mass parent.** The child's average is `0/0 = 0`,
-- but it is multiplied by its own zero mass, so it contributes nothing and the variance
-- vanishes — no cancellation of a child mass is needed anywhere.
example : rectRefinementVarianceNum kNC w10 (fun _ => (1 : ℝ)) PI QI ⊥ QI = 0 := by
  rw [rectRefinementVarianceNum, PI, QI, Finpartition.indiscrete_parts,
    Finpartition.indiscrete_parts]
  norm_num [rectAverage, rectSum, finsetMass, kNC, w10, Finset.filter_insert,
    Finset.filter_singleton]

-- **Zero carrier mass**: the normalized energy is `0`, not undefined.
example : rectEnergy kNC (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) PI QI = 0 := by
  rw [rectEnergy, rectEnergyNum, PI, QI, Finpartition.indiscrete_parts,
    Finpartition.indiscrete_parts]
  norm_num [rectBlockEnergy, rectAverage, rectSum, finsetMass, kNC]

end Tests

end RegularityLemmata
