/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RectKernel
import Mathlib.Tactic.FinCases

/-!
# The partition-free cut norm of a rectangular kernel

`rectCutNorm f wX wY A B` is the largest absolute weighted rectangle sum over test rectangles
`S ⊆ A`, `T ⊆ B` — the cut norm in the library's raw-weight, denominator-free units (a
normalized form divides by the total mass and is derived, never primitive). It measures a
kernel against **nothing**: no partition, no stepped prediction. The partition-indexed
`rectCutDiscrepancy` (`Partition/RectKernelCut.lean`) is the cut norm of the stepped residual,
and the bridge between the two lives there.

This is the quantity the cut-matrix decomposition (`docs/design/cut-matrix-decomposition.md`)
bounds on its residual `f − ∑ cₖ 𝟙_{Sₖ} ⊗ 𝟙_{Tₖ}`.

Conventions, matching the discrepancy: the supremum is a `Finset.sup'` over the product of
powersets, nonempty because `∅ ×ˢ ∅` is always a test rectangle; the elimination `iff` is the
public interface; `op` exchanges the sides; positive rescaling of a carrier weight scales the
norm; on zero total mass with nonnegative weights the norm is `0` (guard-free); and an
absolutely `C`-bounded kernel has cut norm at most `C` times the total mass.
-/

namespace RegularityLemmata

variable {X Y : Type*} {f : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ}
variable {A : Finset X} {B : Finset Y}

/-- The cut norm: the largest absolute rectangle sum over `S ⊆ A`, `T ⊆ B`. -/
noncomputable def rectCutNorm (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  (A.powerset ×ˢ B.powerset).sup'
    (Finset.Nonempty.product ⟨∅, Finset.empty_mem_powerset A⟩
      ⟨∅, Finset.empty_mem_powerset B⟩)
    fun p => |rectSum f wX wY p.1 p.2|

/-- Elimination API: bounding the cut norm is exactly the quantified rectangle bound. -/
theorem rectCutNorm_le_iff {c : ℝ} :
    rectCutNorm f wX wY A B ≤ c ↔ ∀ S ⊆ A, ∀ T ⊆ B, |rectSum f wX wY S T| ≤ c := by
  rw [rectCutNorm, Finset.sup'_le_iff]
  constructor
  · intro h S hS T hT
    exact h (S, T) (Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hS, Finset.mem_powerset.mpr hT⟩)
  · rintro h ⟨S, T⟩ hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    exact h S hp.1 T hp.2

/-- Every test rectangle's absolute sum is at most the cut norm. -/
theorem abs_rectSum_le_rectCutNorm {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) :
    |rectSum f wX wY S T| ≤ rectCutNorm f wX wY A B :=
  rectCutNorm_le_iff.mp le_rfl S hS T hT

theorem rectCutNorm_nonneg : 0 ≤ rectCutNorm f wX wY A B :=
  le_trans (abs_nonneg _)
    (abs_rectSum_le_rectCutNorm (Finset.empty_subset A) (Finset.empty_subset B))

/-- `op` exchanges the two sides of the cut norm. -/
theorem rectCutNorm_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X)
    (B : Finset Y) : rectCutNorm f.op wY wX B A = rectCutNorm f wX wY A B := by
  refine le_antisymm ?_ ?_
  · rw [rectCutNorm_le_iff]
    intro T hT S hS
    rw [rectSum_op]
    exact abs_rectSum_le_rectCutNorm hS hT
  · rw [rectCutNorm_le_iff]
    intro S hS T hT
    rw [← rectSum_op]
    exact abs_rectSum_le_rectCutNorm hT hS

/-- Positive rescaling of the left carrier weight scales the cut norm by the same factor
(design-freeze convention 6). -/
theorem rectCutNorm_smul_weight_left {c : ℝ} (hc : 0 < c) (f : RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectCutNorm f (fun x => c * wX x) wY A B = c * rectCutNorm f wX wY A B := by
  refine le_antisymm ?_ ?_
  · rw [rectCutNorm_le_iff]
    intro S hS T hT
    rw [rectSum_smul_weight_left, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (abs_rectSum_le_rectCutNorm hS hT) hc.le
  · rw [← le_div_iff₀' hc, rectCutNorm_le_iff]
    intro S hS T hT
    have h := abs_rectSum_le_rectCutNorm (f := f) (wX := fun x => c * wX x) (wY := wY) hS hT
    rw [rectSum_smul_weight_left, abs_mul, abs_of_pos hc] at h
    rwa [le_div_iff₀' hc]

/-- **The trivial bound.** An absolutely `C`-bounded kernel has cut norm at most `C` times the
total mass, under nonnegative weights; guard-free, and the reason a cut-norm target `ε · M`
with `ε ≥ C` is met by the zero decomposition. -/
theorem rectCutNorm_le_mul_mass {C : ℝ} (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hC : 0 ≤ C) (hf : IsAbsBoundedOnRectangle f C A B) :
    rectCutNorm f wX wY A B ≤ C * (finsetMass wX A * finsetMass wY B) := by
  rw [rectCutNorm_le_iff]
  intro S hS T hT
  have hwS : ∀ x ∈ S, 0 ≤ wX x := fun x hx => hwX x (hS hx)
  have hwT : ∀ y ∈ T, 0 ≤ wY y := fun y hy => hwY y (hT hy)
  refine (abs_rectSum_le hwS hwT fun x hx y hy => hf x (hS hx) y (hT hy)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact mul_le_mul (finsetMass_mono hwX hS) (finsetMass_mono hwY hT)
    (finsetMass_nonneg hwT) (finsetMass_nonneg hwX)

/-- **Zero total mass gives zero cut norm** under nonnegative weights: every rectangle sum
inside the carriers vanishes (`rectSum_eq_zero_of_finsetMass_mul_eq_zero`). -/
theorem rectCutNorm_eq_zero_of_finsetMass_mul_eq_zero (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) (h : finsetMass wX A * finsetMass wY B = 0) :
    rectCutNorm f wX wY A B = 0 := by
  refine le_antisymm ?_ rectCutNorm_nonneg
  rw [rectCutNorm_le_iff]
  intro S hS T hT
  rw [rectSum_eq_zero_of_finsetMass_mul_eq_zero hwX hwY hS hT h, abs_zero]

/-! ### Tests and adversarial examples -/

section Tests

/-- The `±1` chequerboard on `Fin 2 × Fin 2`. -/
private def cheq : RectKernel (Fin 2) (Fin 2) := fun x y => if x = y then 1 else -1

-- **The chequerboard has cut norm exactly `1`** at unit weights on the full `2 × 2` rectangle,
-- although its total rectangle sum is `0`: a single cell witnesses `≥ 1`, and every one of the
-- sixteen test rectangles has absolute sum at most `1`. This is the concrete instance the
-- decomposition's forced-update test uses (`M = 4`, so `ε < 1/4` forces a round).
example : rectCutNorm cheq (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [rectCutNorm_le_iff]
    intro S _ T _
    fin_cases S <;> fin_cases T <;> simp [cheq, rectSum]
  · have h := abs_rectSum_le_rectCutNorm (f := cheq) (wX := fun _ => 1) (wY := fun _ => 1)
      (Finset.subset_univ ({0} : Finset (Fin 2))) (Finset.subset_univ ({0} : Finset (Fin 2)))
    simpa [cheq, rectSum] using h

-- **Empty carriers**: the cut norm is `0` (statement-level through the zero-mass lemma).
example (f : RectKernel (Fin 2) (Fin 3)) :
    rectCutNorm f (fun _ => 1) (fun _ => 1) ∅ Finset.univ = 0 :=
  rectCutNorm_eq_zero_of_finsetMass_mul_eq_zero (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (by simp [finsetMass])

-- **Zero mass on a nonempty carrier with a nonzero kernel**: weights identically `0`.
example : rectCutNorm cheq (fun _ => 0) (fun _ => 0) Finset.univ Finset.univ = 0 :=
  rectCutNorm_eq_zero_of_finsetMass_mul_eq_zero (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by simp [finsetMass])

-- **The trivial bound** at `C = 1` on the chequerboard: `1 ≤ 1 · (2 · 2)`.
example : rectCutNorm cheq (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    ≤ 1 * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
      * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ) :=
  rectCutNorm_le_mul_mass (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) zero_le_one
    (fun x _ y _ => by unfold cheq; split_ifs <;> norm_num)

-- **Rescaling** the left weight by `3` triples the cut norm; **`op`** leaves it fixed.
example : rectCutNorm cheq (fun _ => 3 * 1) (fun _ => 1) Finset.univ Finset.univ
    = 3 * rectCutNorm cheq (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ :=
  rectCutNorm_smul_weight_left (by norm_num) cheq _ _ _ _
example : rectCutNorm cheq.op (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    = rectCutNorm cheq (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ :=
  rectCutNorm_op cheq _ _ _ _

end Tests

end RegularityLemmata
