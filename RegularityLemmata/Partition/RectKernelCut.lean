/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Inequalities
import RegularityLemmata.Partition.Basic
import RegularityLemmata.Partition.RectKernel

/-!
# Cut discrepancy for rectangular weighted kernels

The rectangle error of a weighted kernel against its stepped prediction, the cut
discrepancy as the supremum of that error over test rectangles, and the **contraction**
of stepping: passing to a stepped prediction never increases the rectangle error.

The design freeze is `docs/design/rectangular-kernels.md`. No Frieze–Kannan iteration and
no part-count recurrence appear here; those live in `Partition/RectKernelFriezeKannan.lean`.

## The contraction constant is `1`

`abs_steppedRectSum_le` is the load-bearing estimate. Written in relative cell masses, a
stepped rectangle sum is a `[0,1]`-weighted bilinear combination of the cell sums, and
`abs_sum_bilinear_le` bounds any such combination by the supremum over genuine cell-union
rectangles. So stepping costs a factor of **`1`**, not `2` — the only factor of two in the
downstream common-refinement adapter comes from a triangle inequality.

Two facts make this work without side conditions, and both are deliberately upstream:
`relMass_le_one` is guard-free, so no cell needs a positive-mass hypothesis; and
`abs_sum_bilinear_le` needs no extreme-point machinery, because `cᵢ * yᵢ ≤ max yᵢ 0` holds
pointwise.

## Provenance

Cut norms and stepped (step-function) approximations are standard; see L. Lovász, *Large
Networks and Graph Limits*, AMS 2012, for the background. The formulation here — raw
carrier weights on two heterogeneous carriers, independent partitions, the guard-free
`x / 0 = 0` conventions, and the constant-`1` contraction in the form proved below — is
this repository's, and is not a restatement of a lemma from that source. The abstract
inequality it rests on is `abs_sum_bilinear_le` in `Finite/Inequalities.lean`, proved
independently there.
-/

namespace RegularityLemmata

variable {X Y : Type*} {f : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ}
variable {A : Finset X} {B : Finset Y}

/-! ### Rectangle error and cut discrepancy -/

/-- The error of the `P ×ˢ Q`-stepped prediction on the test rectangle `S ×ˢ T`. -/
noncomputable def rectError [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (S : Finset X) (T : Finset Y) : ℝ :=
  rectSum f wX wY S T - steppedRectSum f wX wY P Q S T

/-- On the full rectangle the prediction is exact, so the error vanishes. -/
theorem rectError_self [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectError f wX wY P Q A B = 0 := by
  rw [rectError, steppedRectSum_self f wX wY P Q hwX hwY, sub_self]

/-- The cut discrepancy: the largest rectangle error over test sets `S ⊆ A`, `T ⊆ B`. -/
noncomputable def rectCutDiscrepancy [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) : ℝ :=
  (A.powerset ×ˢ B.powerset).sup'
    (Finset.Nonempty.product ⟨∅, Finset.empty_mem_powerset A⟩
      ⟨∅, Finset.empty_mem_powerset B⟩)
    fun p => |rectError f wX wY P Q p.1 p.2|

/-- Elimination API: bounding the cut discrepancy is exactly the quantified rectangle
bound. -/
theorem rectCutDiscrepancy_le_iff [DecidableEq X] [DecidableEq Y] {P : Finpartition A}
    {Q : Finpartition B} {c : ℝ} :
    rectCutDiscrepancy f wX wY P Q ≤ c
      ↔ ∀ S ⊆ A, ∀ T ⊆ B, |rectError f wX wY P Q S T| ≤ c := by
  rw [rectCutDiscrepancy, Finset.sup'_le_iff]
  constructor
  · intro h S hS T hT
    exact h (S, T) (Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hS, Finset.mem_powerset.mpr hT⟩)
  · rintro h ⟨S, T⟩ hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    exact h S hp.1 T hp.2

theorem rectCutDiscrepancy_nonneg [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) : 0 ≤ rectCutDiscrepancy f wX wY P Q := by
  have hmem : ((∅ : Finset X), (∅ : Finset Y)) ∈ A.powerset ×ˢ B.powerset :=
    Finset.mem_product.mpr ⟨Finset.empty_mem_powerset A, Finset.empty_mem_powerset B⟩
  have h : |rectError f wX wY P Q ∅ ∅| ≤ rectCutDiscrepancy f wX wY P Q :=
    Finset.le_sup' (fun p => |rectError f wX wY P Q p.1 p.2|) hmem
  exact le_trans (abs_nonneg _) h

/-! ### Reindexing a weighted point sum by cells

The weighted corollary of `sum_over_parts`. It is **purely algebraic**: no nonnegativity of
the weights and no positive-mass hypothesis. Those enter only where an average is cancelled
or an inequality is proved, never here. -/

/-- A weighted sum whose coefficient depends on the containing cell reindexes to a sum over
cells against the traces' masses. -/
theorem sum_part_mul_weight [DecidableEq X] (P : Finpartition A) (S : Finset X) (hS : S ⊆ A)
    (w : X → ℝ) (c : Finset X → ℝ) :
    ∑ x ∈ S, c (P.part x) * w x = ∑ C ∈ P.parts, c C * finsetMass w (S ∩ C) := by
  rw [sum_over_parts P (S := S) hS (fun C x => c C * w x)]
  exact Finset.sum_congr rfl fun C _ => by rw [finsetMass, Finset.mul_sum]

/-! ### The residual kernel

The kernel `f` minus its own stepped value: at `(x, y)` the prediction subtracted is the
average over the cell pair containing `x` and `y`.

**Outside-support convention.** `Finpartition.part` returns `∅` off the carrier, and an
empty rectangle has average `0`, so the residual **equals `f`** outside `A ×ˢ B`. That is a
clean convention rather than a defect, but it means every substantive statement below is
**carrier-local**: the tower and error identities all quantify over test rectangles
`S ⊆ A`, `T ⊆ B`.

**Where hypotheses begin.** The residual-to-error bridge is pure algebra — it needs neither
nonnegative weights nor positive masses, only `S ⊆ A` and `T ⊆ B`. Conditional-expectation
behaviour, in particular the tower identity, is where nonnegativity genuinely enters: with
signed weights a cell can have zero total mass while a trace inside it has nonzero mass, and
the zero-cell argument breaks. -/

/-- The kernel minus its own stepped prediction, pointwise. -/
noncomputable def rectResidual [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) : RectKernel X Y :=
  fun x y => f x y - rectAverage f wX wY (P.part x) (Q.part y)

/-- The defining equation. Deliberately **not** `@[simp]`: unconditional unfolding turns
every rectangle sum into `part`-indexed averages, which is exactly what
`rectSum_rectResidual_eq_rectError` exists to avoid. -/
theorem rectResidual_apply [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) (x : X) (y : Y) :
    rectResidual f wX wY P Q x y
      = f x y - rectAverage f wX wY (P.part x) (Q.part y) := rfl

/-- Off the left carrier the residual is `f` itself: `P.part x = ∅`, and an empty rectangle
has average `0`. -/
@[simp] theorem rectResidual_of_notMem_left [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {x : X} (hx : x ∉ A) (y : Y) : rectResidual f wX wY P Q x y = f x y := by
  rw [rectResidual_apply, P.part_eq_empty.mpr hx, rectAverage,
    rectSum_empty_left, zero_div, sub_zero]

/-- …and off the right carrier likewise. -/
@[simp] theorem rectResidual_of_notMem_right [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (x : X) {y : Y} (hy : y ∉ B) : rectResidual f wX wY P Q x y = f x y := by
  rw [rectResidual_apply, Q.part_eq_empty.mpr hy, rectAverage,
    rectSum_empty_right, zero_div, sub_zero]

/-! ### Relative cell-mass coefficients

The bridge from the stepped prediction to a bilinear form: the coefficients are the
relative masses of the test rectangle inside each cell, and they land in `[0,1]` with no
positive-mass hypothesis. -/

/-- **The stepped prediction as a bilinear form in the relative cell masses.**

Guard-free, and the zero-mass case is split rather than cancelled: when a cell has zero
mass, its relative mass is `0 / 0 = 0` on one side, and the trace of the test set inside it
has zero mass on the other, so both sides drop the cell. -/
theorem steppedRectSum_eq_relMass_bilinear [DecidableEq X] [DecidableEq Y]
    (P : Finpartition A) (Q : Finpartition B) (S : Finset X) (T : Finset Y)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    steppedRectSum f wX wY P Q S T
      = ∑ C ∈ P.parts, relMass wX S C
          * ∑ D ∈ Q.parts, relMass wY T D * rectSum f wX wY C D := by
  classical
  rw [steppedRectSum]
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hwC : ∀ x ∈ C, 0 ≤ wX x := fun x hx => hwX x ((P.le hC) hx)
  have hwD : ∀ y ∈ D, 0 ≤ wY y := fun y hy => hwY y ((Q.le hD) hy)
  have hmC : 0 ≤ finsetMass wX C := finsetMass_nonneg hwC
  have hmD : 0 ≤ finsetMass wY D := finsetMass_nonneg hwD
  have hsub : finsetMass wX (S ∩ C) ≤ finsetMass wX C :=
    finsetMass_mono hwC Finset.inter_subset_right
  have hsubT : finsetMass wY (T ∩ D) ≤ finsetMass wY D :=
    finsetMass_mono hwD Finset.inter_subset_right
  have hsubnn : 0 ≤ finsetMass wX (S ∩ C) :=
    finsetMass_nonneg fun x hx => hwC x (Finset.mem_of_mem_inter_right hx)
  have hsubTnn : 0 ≤ finsetMass wY (T ∩ D) :=
    finsetMass_nonneg fun y hy => hwD y (Finset.mem_of_mem_inter_right hy)
  rcases eq_or_lt_of_le hmC with hC0 | hCpos
  · -- Zero-mass left cell: both sides vanish.
    have hSC : finsetMass wX (S ∩ C) = 0 := le_antisymm (hC0 ▸ hsub) hsubnn
    rw [relMass, ← hC0, div_zero, zero_mul, hSC, zero_mul, mul_zero]
  rcases eq_or_lt_of_le hmD with hD0 | hDpos
  · -- Zero-mass right cell: both sides vanish.
    have hTD : finsetMass wY (T ∩ D) = 0 := le_antisymm (hD0 ▸ hsubT) hsubTnn
    have hrel : relMass wY T D = 0 := by rw [relMass, ← hD0, div_zero]
    rw [hTD, mul_zero, mul_zero, hrel, zero_mul, mul_zero]
  -- Positive mass on both sides: divide out only now.
  have hrs : rectSum f wX wY C D
      = rectAverage f wX wY C D * (finsetMass wX C * finsetMass wY D) :=
    (rectAverage_mul_mass hwC hwD).symm
  rw [relMass, relMass, hrs]
  field_simp

/-! ### Contraction of stepping, at constant `1` -/

/-- Cell-union rectangles are test rectangles: a union of `P`-parts sits inside `A`. -/
theorem biUnion_parts_subset [DecidableEq X] {P : Finpartition A} {I : Finset (Finset X)}
    (hI : I ⊆ P.parts) : I.biUnion id ⊆ A := by
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨C, hCI, hxC⟩ := hx
  exact (P.le (hI hCI)) hxC

/-- **Contraction, at constant `1`.** If every rectangle sum of `f` is within `ε`, then so
is every stepped prediction — for **any** test rectangle and any pair of partitions.

This is the estimate the common-refinement adapter rests on, and the reason its constant is
`2` rather than `4`: stepping is free, and the factor of two is a triangle inequality. -/
theorem abs_steppedRectSum_le [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (S : Finset X) (T : Finset Y)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ}
    (hrect : ∀ S' ⊆ A, ∀ T' ⊆ B, |rectSum f wX wY S' T'| ≤ ε) :
    |steppedRectSum f wX wY P Q S T| ≤ ε := by
  classical
  rw [steppedRectSum_eq_relMass_bilinear P Q S T hwX hwY]
  refine abs_sum_bilinear_le P.parts Q.parts
    (fun C hC => relMass_nonneg (fun x hx => hwX x ((P.le hC) hx)) S)
    (fun C hC => relMass_le_one (fun x hx => hwX x ((P.le hC) hx)) S)
    (fun D hD => relMass_nonneg (fun y hy => hwY y ((Q.le hD) hy)) T)
    (fun D hD => relMass_le_one (fun y hy => hwY y ((Q.le hD) hy)) T)
    (fun C D => rectSum f wX wY C D) ?_
  -- The 0/1 combinations are exactly the cell-union rectangles.
  intro I hI J hJ
  have hdisjI : (I : Set (Finset X)).PairwiseDisjoint id :=
    P.supIndep.pairwiseDisjoint.subset (by rw [Finset.coe_subset]; exact hI)
  have hdisjJ : (J : Set (Finset Y)).PairwiseDisjoint id :=
    Q.supIndep.pairwiseDisjoint.subset (by rw [Finset.coe_subset]; exact hJ)
  have hsplit := rectSum_biUnion f wX wY hdisjI hdisjJ
  rw [Finset.sum_product] at hsplit
  rw [← hsplit]
  exact hrect _ (biUnion_parts_subset hI) _ (biUnion_parts_subset hJ)

/-- The same bound in error form: a stepped prediction of a kernel whose rectangle sums are
all small is itself small, so the rectangle error is at most twice the input bound. This is
the triangle step, with its constant `2` made explicit. -/
theorem abs_rectError_le_two_mul [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ}
    (hrect : ∀ S' ⊆ A, ∀ T' ⊆ B, |rectSum f wX wY S' T'| ≤ ε) :
    |rectError f wX wY P Q S T| ≤ 2 * ε := by
  have h1 : |rectSum f wX wY S T| ≤ ε := hrect S hS T hT
  have h2 : |steppedRectSum f wX wY P Q S T| ≤ ε :=
    abs_steppedRectSum_le P Q S T hwX hwY hrect
  calc |rectError f wX wY P Q S T|
      ≤ |rectSum f wX wY S T| + |steppedRectSum f wX wY P Q S T| := by
        rw [rectError]; exact abs_sub _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

/-! ### Transpose transport

Design-freeze convention 7: `op` exchanges every left/right construction. The discrepancy
statement goes through `rectCutDiscrepancy_le_iff` in both directions rather than through
the two `sup'` index sets directly. -/

/-- `op` exchanges the two sides of the rectangle error, together with the partitions and
the test rectangle. -/
theorem rectError_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) (S : Finset X) (T : Finset Y) :
    rectError f.op wY wX Q P T S = rectError f wX wY P Q S T := by
  rw [rectError, rectError, rectSum_op, steppedRectSum_op]

/-- …and of the cut discrepancy. -/
theorem rectCutDiscrepancy_op [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) :
    rectCutDiscrepancy f.op wY wX Q P = rectCutDiscrepancy f wX wY P Q := by
  refine le_antisymm ?_ ?_
  · rw [rectCutDiscrepancy_le_iff]
    intro T hT S hS
    rw [rectError_op]
    exact rectCutDiscrepancy_le_iff.mp le_rfl S hS T hT
  · rw [rectCutDiscrepancy_le_iff]
    intro S hS T hT
    rw [← rectError_op]
    exact rectCutDiscrepancy_le_iff.mp le_rfl T hT S hS

/-! ### Positive rescaling of a carrier weight

Design-freeze convention 6: rescaling a carrier weight by `c > 0` scales the **raw**
discrepancy by exactly `c`.

Positivity is what makes the proof uniform, in two places: `rectAverage_smul_weight_left`
needs `c ≠ 0`, and `|c| = c` is what carries the factor through the absolute value. It is
**not** that the identity fails at `c = 0` — there both sides vanish, since zero left
weights force zero rectangle sums, zero cell masses, and hence `0 / 0 = 0` averages. That
degenerate case simply wants a different argument, and no consumer has asked for it;
`0 < c` is the public contract until one does. -/

theorem rectError_smul_weight_left [DecidableEq X] [DecidableEq Y] {c : ℝ} (hc : 0 < c)
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A)
    (Q : Finpartition B) (S : Finset X) (T : Finset Y) :
    rectError f (fun x => c * wX x) wY P Q S T = c * rectError f wX wY P Q S T := by
  have hstep : steppedRectSum f (fun x => c * wX x) wY P Q S T
      = c * steppedRectSum f wX wY P Q S T := by
    rw [steppedRectSum, steppedRectSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [rectAverage_smul_weight_left (ne_of_gt hc), finsetMass_smul]
    ring
  rw [rectError, rectError, rectSum_smul_weight_left, hstep, mul_sub]

/-- **The raw discrepancy scales with the carrier weight.** -/
theorem rectCutDiscrepancy_smul_weight_left [DecidableEq X] [DecidableEq Y] {c : ℝ}
    (hc : 0 < c) (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A)
    (Q : Finpartition B) :
    rectCutDiscrepancy f (fun x => c * wX x) wY P Q
      = c * rectCutDiscrepancy f wX wY P Q := by
  refine le_antisymm ?_ ?_
  · rw [rectCutDiscrepancy_le_iff]
    intro S hS T hT
    rw [rectError_smul_weight_left hc, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (rectCutDiscrepancy_le_iff.mp le_rfl S hS T hT) hc.le
  · have hdisc : rectCutDiscrepancy f wX wY P Q
        ≤ rectCutDiscrepancy f (fun x => c * wX x) wY P Q / c := by
      rw [rectCutDiscrepancy_le_iff]
      intro S hS T hT
      rw [le_div_iff₀ hc, mul_comm]
      have h := rectCutDiscrepancy_le_iff.mp
        (le_rfl (a := rectCutDiscrepancy f (fun x => c * wX x) wY P Q)) S hS T hT
      rwa [rectError_smul_weight_left hc, abs_mul, abs_of_pos hc] at h
    calc c * rectCutDiscrepancy f wX wY P Q
        ≤ c * (rectCutDiscrepancy f (fun x => c * wX x) wY P Q / c) :=
          mul_le_mul_of_nonneg_left hdisc hc.le
      _ = rectCutDiscrepancy f (fun x => c * wX x) wY P Q := by
          field_simp

/-! ### Tests and adversarial examples -/

section Tests

/-- Nonuniform left weights. -/
private def cL : Fin 2 → ℝ := ![2, 3]

/-- Nonuniform right weights, on a **different** carrier size — the partitions here are
genuinely asymmetric. -/
private def cR : Fin 3 → ℝ := ![1, 2, 3]

private theorem hcL : ∀ x ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ cL x :=
  fun x _ => by fin_cases x <;> norm_num [cL]

private theorem hcR : ∀ y ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ cR y :=
  fun y _ => by fin_cases y <;> norm_num [cR]

-- **Asymmetric partitions**: the two carriers have different sizes and independent
-- partitions, and contraction still costs `1`.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (S : Finset (Fin 2))
    (T : Finset (Fin 3)) {ε : ℝ}
    (hrect : ∀ S' ⊆ (Finset.univ : Finset (Fin 2)),
      ∀ T' ⊆ (Finset.univ : Finset (Fin 3)), |rectSum f cL cR S' T'| ≤ ε) :
    |steppedRectSum f cL cR P Q S T| ≤ ε :=
  abs_steppedRectSum_le P Q S T hcL hcR hrect

-- The triangle step, with its factor `2`.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) {S : Finset (Fin 2)}
    {T : Finset (Fin 3)} (hS : S ⊆ Finset.univ) (hT : T ⊆ Finset.univ) {ε : ℝ}
    (hrect : ∀ S' ⊆ (Finset.univ : Finset (Fin 2)),
      ∀ T' ⊆ (Finset.univ : Finset (Fin 3)), |rectSum f cL cR S' T'| ≤ ε) :
    |rectError f cL cR P Q S T| ≤ 2 * ε :=
  abs_rectError_le_two_mul P Q hS hT hcL hcR hrect

-- **Zero carrier mass**: the error on the full rectangle is `0`, not undefined, and the
-- discrepancy bound is available with no positive-mass hypothesis anywhere.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectError f (fun _ => (0 : ℝ)) cR P Q Finset.univ Finset.univ = 0 :=
  rectError_self P Q (fun _ _ => le_rfl) hcR

-- **Outside the carrier the residual is `f` itself.** `P.part 1 = ∅` because `1 ∉ {0}`, and
-- an empty rectangle has average `0` — the outside-support convention, made concrete.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition ({0} : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (y : Fin 3) :
    rectResidual f cL cR P Q 1 y = f 1 y :=
  rectResidual_of_notMem_left f cL cR P Q (by decide) y

-- **The cell reindexing needs no sign hypothesis.** Signed weights that cancel to zero
-- total mass, where every average-level statement in this file would need nonnegativity.
example (P : Finpartition (Finset.univ : Finset (Fin 2))) (S : Finset (Fin 2))
    (c : Finset (Fin 2) → ℝ) :
    ∑ x ∈ S, c (P.part x) * (if x = 0 then (1 : ℝ) else -1)
      = ∑ C ∈ P.parts, c C * finsetMass (fun x : Fin 2 => if x = 0 then (1 : ℝ) else -1)
          (S ∩ C) :=
  sum_part_mul_weight P S (Finset.subset_univ S) _ c

-- **`op` transport of the discrepancy**, between genuinely different carriers.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectCutDiscrepancy f.op cR cL Q P = rectCutDiscrepancy f cL cR P Q :=
  rectCutDiscrepancy_op f cL cR P Q

-- **Positive rescaling** scales the raw discrepancy by exactly the same factor.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    rectCutDiscrepancy f (fun x => 5 * cL x) cR P Q
      = 5 * rectCutDiscrepancy f cL cR P Q :=
  rectCutDiscrepancy_smul_weight_left (by norm_num) f cL cR P Q

-- The discrepancy is never negative, and the empty rectangle is always a legal test.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    0 ≤ rectCutDiscrepancy f cL cR P Q :=
  rectCutDiscrepancy_nonneg P Q

end Tests

end RegularityLemmata
