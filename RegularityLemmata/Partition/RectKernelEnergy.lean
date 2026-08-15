/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
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

end Tests

end RegularityLemmata
