/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.RectKernelCut
import RegularityLemmata.Partition.RectKernelEnergy
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Frieze–Kannan weak regularity for rectangular weighted kernels

The energy-increment iteration for `RectKernel`, and the rectangular summit: separate left
and right part-count bounds, with the same-carrier product bound derived through the adapter
of `Partition/RectKernelCut.lean` rather than taken as primitive.

The design freeze is `docs/design/rectangular-kernels.md`. Constants are frozen there:
contraction **1**, triangle **2**, and the call at `ε/2`.

## The quantitative seam

Each round cuts **each carrier once**, so a round costs a factor of **2 per coordinate**,
independently: `#P ≤ #P₀ · 2^t` and `#Q ≤ #Q₀ · 2^t`. The factor **4** appears only when
those two bounds are multiplied against each other by the same-carrier adapter. Keeping them
separate until that point is the reason the rectangular formulation exists; merging them
earlier is exactly where sharpness is lost.

The one-cut refinement itself is carrier-only machinery and lives upstream, in
`Partition/Basic.lean` as `cutRefinePartition`; nothing about it mentions a kernel.

## Provenance

The weak-regularity architecture — weak approximation in cut discrepancy via a greedy energy
increment — is due to A. Frieze and R. Kannan, *Quick approximation to matrices and
applications*, Combinatorica **19** (1999), 175–220. The energy-increment mechanism and the
`ε²`-per-round gain are theirs.

What this file proves is a **step-partition summit**, not the separate cut-matrix
decomposition interface, which remains unimplemented.

The formulation here is this repository's, and differs from the classical source in ways that
are not cosmetic: raw carrier weights on **two heterogeneous carriers** rather than a single
normalized vertex set; **independent** left and right partitions with separately exposed part
counts; guard-free `x / 0 = 0` conventions throughout, so that zero-mass cells and zero-mass
carriers need no side conditions; and the common-refinement adapter that converts the
two-coordinate statement into a same-carrier one.

The internal antecedent is the **Boolean** development in `Graph/FriezeKannan.lean`, which is
unchanged and is not superseded, deprecated, or re-derived here. This file recovers that
theorem's *discrepancy* conclusion through the adapter, not its sharper complexity bound.
-/

namespace RegularityLemmata

variable {X Y : Type*} {A : Finset X} {B : Finset Y}

/-! ### One cut per coordinate

A round of the iteration cuts each carrier by one test set, independently. The two part
bounds are produced and kept **separate** — this file never multiplies them. -/

/-- **A round costs a factor of `2` in each coordinate, separately.** Stated as a pair rather
than as a product: the product is the adapter's business, not the iteration's. -/
theorem card_parts_cut_pair_le [DecidableEq X] [DecidableEq Y] (P : Finpartition A)
    (Q : Finpartition B) (S : Finset X) (T : Finset Y) :
    (cutRefinePartition P S).parts.card ≤ 2 * P.parts.card
      ∧ (cutRefinePartition Q T).parts.card ≤ 2 * Q.parts.card :=
  ⟨card_parts_cutRefinePartition_le P S, card_parts_cutRefinePartition_le Q T⟩

/-! ### Layer 1: the witness error as a mass-weighted sum over selected cells

After cutting, the witness rectangle `S ×ˢ T` is exactly a union of fine cells, so the
rectangle error decomposes into a **mass-weighted sum of the residual's cell averages**. The
coefficients are genuine functions of the cell pair — no parent is mentioned — which is what
makes the Cauchy–Schwarz step a direct application rather than a reindexing argument. Parents
enter only in layer 2. -/

/-- The fine cells selected by the witness set on the left. -/
noncomputable def selectedLeft [DecidableEq X] (P : Finpartition A) (S : Finset X) :
    Finset (Finset X) :=
  (cutRefinePartition P S).parts.filter (· ⊆ S)

/-- …and on the right. -/
noncomputable def selectedRight [DecidableEq Y] (Q : Finpartition B) (T : Finset Y) :
    Finset (Finset Y) :=
  (cutRefinePartition Q T).parts.filter (· ⊆ T)

theorem selectedLeft_subset [DecidableEq X] (P : Finpartition A) (S : Finset X) :
    selectedLeft P S ⊆ (cutRefinePartition P S).parts :=
  Finset.filter_subset _ _

theorem selectedRight_subset [DecidableEq Y] (Q : Finpartition B) (T : Finset Y) :
    selectedRight Q T ⊆ (cutRefinePartition Q T).parts :=
  Finset.filter_subset _ _

/-- **The witness rectangle is the union of the selected cells.** -/
theorem biUnion_selectedLeft [DecidableEq X] (P : Finpartition A) {S : Finset X}
    (hS : S ⊆ A) : (selectedLeft P S).biUnion id = S :=
  biUnion_cutRefinePartition_filter_subset P hS

theorem biUnion_selectedRight [DecidableEq Y] (Q : Finpartition B) {T : Finset Y}
    (hT : T ⊆ B) : (selectedRight Q T).biUnion id = T :=
  biUnion_cutRefinePartition_filter_subset Q hT

/-- **Layer 1, the decomposition.** The rectangle error of `f` against the coarse pair, on the
witness rectangle, is the mass-weighted sum of the residual's averages over the selected cell
pairs.

Pure bookkeeping: the bridge of `Partition/RectKernelCut.lean`, additivity of a rectangle sum
over disjoint unions, and the cancellation gate `rectAverage_mul_mass` — which needs no
positive-mass hypothesis, so neither does this. -/
theorem rectError_eq_sum_selected [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) {S : Finset X}
    {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectError f wX wY P Q S T
      = ∑ p ∈ selectedLeft P S ×ˢ selectedRight Q T,
          rectAverage (rectResidual f wX wY P Q) wX wY p.1 p.2
            * (finsetMass wX p.1 * finsetMass wY p.2) := by
  classical
  have hdisjI : ((selectedLeft P S : Finset (Finset X)) : Set (Finset X)).PairwiseDisjoint id :=
    (cutRefinePartition P S).supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact selectedLeft_subset P S)
  have hdisjJ : ((selectedRight Q T : Finset (Finset Y)) : Set (Finset Y)).PairwiseDisjoint id :=
    (cutRefinePartition Q T).supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact selectedRight_subset Q T)
  have hsplit := rectSum_biUnion (rectResidual f wX wY P Q) wX wY hdisjI hdisjJ
  rw [biUnion_selectedLeft P hS, biUnion_selectedRight Q hT] at hsplit
  rw [← rectSum_rectResidual_eq_rectError f wX wY P Q hS hT, hsplit]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product] at hp
  have hp1 : p.1 ⊆ A := ((cutRefinePartition P S).le (selectedLeft_subset P S hp.1))
  have hp2 : p.2 ⊆ B := ((cutRefinePartition Q T).le (selectedRight_subset Q T hp.2))
  exact (rectAverage_mul_mass (f := rectResidual f wX wY P Q) (A := p.1) (B := p.2)
    (fun x hx => hwX x (hp1 hx)) (fun y hy => hwY y (hp2 hy))).symm

/-- The **selected variance**: the mass-weighted mean square of the residual's averages over
the selected cell pairs. Deliberately phrased through the residual, so that it mentions no
parent and layer 1 needs no reindexing. -/
noncomputable def selectedVariance [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) (S : Finset X)
    (T : Finset Y) : ℝ :=
  ∑ p ∈ selectedLeft P S ×ˢ selectedRight Q T,
    rectAverage (rectResidual f wX wY P Q) wX wY p.1 p.2 ^ 2
      * (finsetMass wX p.1 * finsetMass wY p.2)

theorem selectedVariance_nonneg [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B) (S : Finset X)
    (T : Finset Y) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ selectedVariance f wX wY P Q S T := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact mul_nonneg (sq_nonneg _) (mul_nonneg
    (finsetMass_nonneg fun x hx =>
      hwX x ((cutRefinePartition P S).le (selectedLeft_subset P S hp.1) hx))
    (finsetMass_nonneg fun y hy =>
      hwY y ((cutRefinePartition Q T).le (selectedRight_subset Q T hp.2) hy)))

/-- The selected cell masses sum to the mass of the witness rectangle. -/
theorem sum_selected_mass [DecidableEq X] [DecidableEq Y] (wX : X → ℝ) (wY : Y → ℝ)
    (P : Finpartition A) (Q : Finpartition B) {S : Finset X} {T : Finset Y} (hS : S ⊆ A)
    (hT : T ⊆ B) :
    ∑ p ∈ selectedLeft P S ×ˢ selectedRight Q T, finsetMass wX p.1 * finsetMass wY p.2
      = finsetMass wX S * finsetMass wY T := by
  classical
  have hdisjI : ((selectedLeft P S : Finset (Finset X)) : Set (Finset X)).PairwiseDisjoint id :=
    (cutRefinePartition P S).supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact selectedLeft_subset P S)
  have hdisjJ : ((selectedRight Q T : Finset (Finset Y)) : Set (Finset Y)).PairwiseDisjoint id :=
    (cutRefinePartition Q T).supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact selectedRight_subset Q T)
  rw [Finset.sum_product, ← Finset.sum_mul_sum, ← finsetMass_biUnion wX hdisjI,
    ← finsetMass_biUnion wY hdisjJ, biUnion_selectedLeft P hS, biUnion_selectedRight Q hT]

/-- **Layer 1.** The squared witness error is at most the total rectangle mass times the
selected variance.

Mass-weighted Cauchy–Schwarz, applied to the decomposition above. No positive-mass hypothesis
and no boundedness hypothesis on `f`; nonnegative carrier weights are the only assumption. -/
theorem sq_rectError_le_mul_selectedVariance [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectError f wX wY P Q S T ^ 2
      ≤ (finsetMass wX A * finsetMass wY B) * selectedVariance f wX wY P Q S T := by
  classical
  have hmass : ∀ p ∈ selectedLeft P S ×ˢ selectedRight Q T,
      0 ≤ finsetMass wX p.1 * finsetMass wY p.2 := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact mul_nonneg
      (finsetMass_nonneg fun x hx =>
        hwX x ((cutRefinePartition P S).le (selectedLeft_subset P S hp.1) hx))
      (finsetMass_nonneg fun y hy =>
        hwY y ((cutRefinePartition Q T).le (selectedRight_subset Q T hp.2) hy))
  have hcs := sq_sum_mul_le_sum_mul_sum_sq_mul
    (fun p => rectAverage (rectResidual f wX wY P Q) wX wY p.1 p.2)
    (fun p => finsetMass wX p.1 * finsetMass wY p.2)
    (selectedLeft P S ×ˢ selectedRight Q T) hmass
  rw [← rectError_eq_sum_selected f wX wY P Q hS hT hwX hwY,
    sum_selected_mass wX wY P Q hS hT] at hcs
  refine le_trans hcs (mul_le_mul_of_nonneg_right ?_
    (selectedVariance_nonneg f wX wY P Q S T hwX hwY))
  exact mul_le_mul (finsetMass_mono hwX hS) (finsetMass_mono hwY hT)
    (finsetMass_nonneg fun y hy => hwY y (hT hy))
    (finsetMass_nonneg hwX)

/-! ### Layer 2: the selected variance sits inside the refinement variance

Parents enter here, and only here. The conversion from the residual's averages to
child-minus-parent differences goes through `sq_rectAverage_rectResidual_mul_mass`, which is
stated **only** in mass-multiplied form — the unweighted equality is false on a zero-mass fine
cell. After that the selected cells regroup under their parents and embed termwise into the
full refinement variance. -/

/-- **Layer 2.** The selected variance is at most the full refinement variance of the cut
pair.

Three moves, none of them quantitative: regroup the selected cells under coarse parents
(`sum_product_parts_eq_sum_over_parents_subset`); replace each residual average by the
child-minus-parent difference, mass-multiplied; then extend each inner sum from the selected
cells to all fine cells inside that parent, which is legitimate because every term is
nonnegative. -/
theorem selectedVariance_le_rectRefinementVarianceNum [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (S : Finset X) (T : Finset Y) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    selectedVariance f wX wY P Q S T
      ≤ rectRefinementVarianceNum f wX wY P Q (cutRefinePartition P S)
          (cutRefinePartition Q T) := by
  classical
  set P' := cutRefinePartition P S with hP'def
  set Q' := cutRefinePartition Q T with hQ'def
  have hP : P' ≤ P := cutRefinePartition_le P S
  have hQ : Q' ≤ Q := cutRefinePartition_le Q T
  -- Regroup the selected cells under their coarse parents.
  rw [selectedVariance, ← sum_product_parts_eq_sum_over_parents_subset hP hQ
    (selectedLeft_subset P S) (selectedRight_subset Q T)
    (fun C' D' => rectAverage (rectResidual f wX wY P Q) wX wY C' D' ^ 2
      * (finsetMass wX C' * finsetMass wY D')), rectRefinementVarianceNum]
  refine Finset.sum_le_sum fun pd hpd => ?_
  rw [Finset.mem_product] at hpd
  -- Inside one coarse cell pair: rewrite to child-minus-parent, then extend the index set.
  have hcongr : ∑ p ∈ (selectedLeft P S).filter (· ⊆ pd.1) ×ˢ
        (selectedRight Q T).filter (· ⊆ pd.2),
        rectAverage (rectResidual f wX wY P Q) wX wY p.1 p.2 ^ 2
          * (finsetMass wX p.1 * finsetMass wY p.2)
      = ∑ p ∈ (selectedLeft P S).filter (· ⊆ pd.1) ×ˢ
          (selectedRight Q T).filter (· ⊆ pd.2),
          (rectAverage f wX wY p.1 p.2 - rectAverage f wX wY pd.1 pd.2) ^ 2
            * (finsetMass wX p.1 * finsetMass wY p.2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    exact sq_rectAverage_rectResidual_mul_mass f wX wY hpd.1 hpd.2 hp.1.2 hp.2.2 hwX hwY
  rw [hcongr]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.product_subset_product
      (Finset.filter_subset_filter _ (selectedLeft_subset P S))
      (Finset.filter_subset_filter _ (selectedRight_subset Q T)))
    fun p hp _ => ?_
  rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (finsetMass_nonneg fun x hx => hwX x ((P'.le hp.1.1) hx))
      (finsetMass_nonneg fun y hy => hwY y ((Q'.le hp.2.1) hy)))

/-! ### Layer 3: the raw energy increment

Zero total mass is handled **internally**. Under nonnegative weights a zero-mass carrier
forces every rectangle error to vanish, so a witness of positive error simply cannot exist
there; the public theorem therefore carries no positive-mass hypothesis, and division appears
only after positivity has been established locally. -/

/-- A zero-mass left carrier kills every rectangle error: nonnegative weights summing to zero
are pointwise zero. -/
private theorem rectError_eq_zero_of_left_mass_zero [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (h0 : finsetMass wX A = 0) : rectError f wX wY P Q S T = 0 := by
  classical
  have hzero : ∀ x ∈ A, wX x = 0 := (Finset.sum_eq_zero_iff_of_nonneg hwX).mp h0
  have hsum : rectSum f wX wY S T = 0 := by
    rw [rectSum]
    exact Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ => by
      rw [hzero x (hS hx)]; ring
  have hstep : steppedRectSum f wX wY P Q S T = 0 := by
    rw [steppedRectSum]
    refine Finset.sum_eq_zero fun C _ => Finset.sum_eq_zero fun D _ => ?_
    have : finsetMass wX (S ∩ C) = 0 :=
      Finset.sum_eq_zero fun x hx => hzero x (hS (Finset.mem_of_mem_inter_left hx))
    rw [this, zero_mul, mul_zero]
  rw [rectError, hsum, hstep, sub_zero]

/-- …and symmetrically on the right, transported through `op`. -/
private theorem rectError_eq_zero_of_right_mass_zero [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hT : T ⊆ B) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (h0 : finsetMass wY B = 0) : rectError f wX wY P Q S T = 0 := by
  rw [← rectError_op f wX wY P Q S T]
  exact rectError_eq_zero_of_left_mass_zero f.op wY wX Q P hT hwY h0

/-- **A witness forces positive total mass.** This is what lets the increment theorems below
omit a positive-mass hypothesis: under nonnegative weights a zero-mass carrier makes every
rectangle error vanish, so no witness can exist there.

`ε` is **unconstrained** — no positivity is needed. At zero total mass the threshold
`ε · 0` and the error both vanish for *any* `ε`, so the witness inequality is already
contradictory. The increment theorems still need `0 < ε`, but for the gain, not for this. -/
theorem finsetMass_mul_pos_of_lt_abs_rectError [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ}
    (hwit : ε * (finsetMass wX A * finsetMass wY B) < |rectError f wX wY P Q S T|) :
    0 < finsetMass wX A * finsetMass wY B := by
  rcases eq_or_lt_of_le (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)) with
    h0 | h
  · exfalso
    have hE : rectError f wX wY P Q S T = 0 := by
      rcases mul_eq_zero.mp h0.symm with hA0 | hB0
      · exact rectError_eq_zero_of_left_mass_zero f wX wY P Q hS hwX hA0
      · exact rectError_eq_zero_of_right_mass_zero f wX wY P Q hT hwY hB0
    rw [hE, abs_zero, ← h0, mul_zero] at hwit
    exact lt_irrefl 0 hwit
  · exact h

/-- **Layer 3, the raw energy increment.** A witness rectangle whose error exceeds
`ε · (mass A · mass B)` forces the cut refinement to gain at least `ε²` times the total
rectangle mass in raw energy.

Consumes `rectEnergyNum_eq_add_rectRefinementVarianceNum` — the tranche-4c primitive — so the
refinement bookkeeping is the established one and not a private substitute.

Hypotheses are exactly nonnegative carrier weights and `0 < ε`. There is **no** boundedness
hypothesis on `f`: absolute bounds are owed only by the iteration, to force termination. -/
theorem rectEnergyNum_add_le_of_lt_abs_rectError [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ} (hε : 0 < ε)
    (hwit : ε * (finsetMass wX A * finsetMass wY B) < |rectError f wX wY P Q S T|) :
    rectEnergyNum f wX wY P Q + ε ^ 2 * (finsetMass wX A * finsetMass wY B)
      ≤ rectEnergyNum f wX wY (cutRefinePartition P S) (cutRefinePartition Q T) := by
  classical
  have hmA : 0 ≤ finsetMass wX A := finsetMass_nonneg hwX
  have hmB : 0 ≤ finsetMass wY B := finsetMass_nonneg hwY
  have hm : 0 ≤ finsetMass wX A * finsetMass wY B := mul_nonneg hmA hmB
  have hmpos : 0 < finsetMass wX A * finsetMass wY B :=
    finsetMass_mul_pos_of_lt_abs_rectError f wX wY P Q hS hT hwX hwY hwit
  have hP : cutRefinePartition P S ≤ P := cutRefinePartition_le P S
  have hQ : cutRefinePartition Q T ≤ Q := cutRefinePartition_le Q T
  rw [rectEnergyNum_eq_add_rectRefinementVarianceNum hP hQ hwX hwY]
  -- The witness bound, squared, against the Cauchy–Schwarz chain.
  have hchain : rectError f wX wY P Q S T ^ 2
      ≤ (finsetMass wX A * finsetMass wY B)
        * rectRefinementVarianceNum f wX wY P Q (cutRefinePartition P S)
            (cutRefinePartition Q T) :=
    le_trans (sq_rectError_le_mul_selectedVariance f wX wY P Q hS hT hwX hwY)
      (mul_le_mul_of_nonneg_left
        (selectedVariance_le_rectRefinementVarianceNum f wX wY P Q S T hwX hwY) hm)
  have hsq : (ε * (finsetMass wX A * finsetMass wY B)) ^ 2
      < rectError f wX wY P Q S T ^ 2 := by
    have hnn : 0 ≤ ε * (finsetMass wX A * finsetMass wY B) := mul_nonneg hε.le hm
    have habs : |rectError f wX wY P Q S T| ^ 2 = rectError f wX wY P Q S T ^ 2 := sq_abs _
    nlinarith [abs_nonneg (rectError f wX wY P Q S T)]
  -- Divide out the (now positive) total mass.
  have hexpand : (ε * (finsetMass wX A * finsetMass wY B)) ^ 2
      = (finsetMass wX A * finsetMass wY B)
        * (ε ^ 2 * (finsetMass wX A * finsetMass wY B)) := by ring
  rw [hexpand] at hsq
  have hkey : ε ^ 2 * (finsetMass wX A * finsetMass wY B)
      ≤ rectRefinementVarianceNum f wX wY P Q (cutRefinePartition P S)
          (cutRefinePartition Q T) :=
    le_of_lt (lt_of_mul_lt_mul_left (lt_of_lt_of_le hsq hchain) hm)
  linarith

/-- **The normalized `ε²` increment**, as a corollary. Division and the positivity of the
total mass are confined here; the combinatorial core above is denominator-free.

Still no positive-mass and no boundedness hypothesis: the witness supplies the positivity. -/
theorem rectEnergy_add_le_of_lt_abs_rectError [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ} (hε : 0 < ε)
    (hwit : ε * (finsetMass wX A * finsetMass wY B) < |rectError f wX wY P Q S T|) :
    rectEnergy f wX wY P Q + ε ^ 2
      ≤ rectEnergy f wX wY (cutRefinePartition P S) (cutRefinePartition Q T) := by
  have hmpos : 0 < finsetMass wX A * finsetMass wY B :=
    finsetMass_mul_pos_of_lt_abs_rectError f wX wY P Q hS hT hwX hwY hwit
  have hraw := rectEnergyNum_add_le_of_lt_abs_rectError f wX wY P Q hS hT hwX hwY hε hwit
  rw [rectEnergy, rectEnergy, div_add' _ _ _ (ne_of_gt hmpos), div_le_div_iff_of_pos_right hmpos]
  linarith

/-! ### Steps 4–5: the paired iteration, with separate left and right budgets

The iteration is **genuinely paired**: each round cuts the left carrier by its witness set and
the right carrier by its, and the two part-count bounds are carried side by side and never
multiplied. A round costs `2` on each coordinate independently, so `t` rounds cost `2^t` on
each. The common refinement appears nowhere here — only in the same-carrier adapter below.

Absolute unit boundedness of `f` enters here for the first time, and only to force
termination through `rectEnergy_le_one`. The energy step itself needed no such hypothesis. -/

/-- **Fuel-parametrized rectangular FK iteration.** From energy within `t · ε²` of the
ceiling, `t` rounds reach a *pair* of refinements whose stepped prediction is uniformly
`ε · (mass A · mass B)`-accurate on every test rectangle.

The round-budget arithmetic mirrors `Graph/FriezeKannan.lean`'s `fk_iterate`, including its
strict-increment handling: the `t = 0` case is closed by contradiction against the energy
ceiling, which is what makes `⌈1/ε²⌉₊ + 1` rather than `⌈1/ε²⌉₊` the right fuel. -/
theorem rectFkIterate [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition A) (Q : Finpartition B),
      1 - (t : ℝ) * ε ^ 2 ≤ rectEnergy f wX wY P Q →
      ∃ P' : Finpartition A, ∃ Q' : Finpartition B, P' ≤ P ∧ Q' ≤ Q ∧
        P'.parts.card ≤ P.parts.card * 2 ^ t ∧ Q'.parts.card ≤ Q.parts.card * 2 ^ t ∧
        ∀ S ⊆ A, ∀ T ⊆ B,
          |rectError f wX wY P' Q' S T| ≤ ε * (finsetMass wX A * finsetMass wY B) := by
  intro t
  induction t with
  | zero =>
    intro P Q hbudget
    refine ⟨P, Q, le_rfl, le_rfl, by simp, by simp, ?_⟩
    intro S hS T hT
    by_contra hcon
    rw [not_le] at hcon
    have hinc := rectEnergy_add_le_of_lt_abs_rectError f wX wY P Q hS hT hwX hwY hε hcon
    have h1 : rectEnergy f wX wY (cutRefinePartition P S) (cutRefinePartition Q T) ≤ 1 :=
      rectEnergy_le_one _ _ hwX hwY hf
    have h2 : (1 : ℝ) ≤ rectEnergy f wX wY P Q := by simpa using hbudget
    have hpos : (0 : ℝ) < ε ^ 2 := by positivity
    linarith
  | succ t IH =>
    intro P Q hbudget
    by_cases hreg : ∀ S ⊆ A, ∀ T ⊆ B,
        |rectError f wX wY P Q S T| ≤ ε * (finsetMass wX A * finsetMass wY B)
    · exact ⟨P, Q, le_rfl, le_rfl, Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num)),
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num)), hreg⟩
    · push Not at hreg
      obtain ⟨S, hS, T, hT, hdev⟩ := hreg
      have hinc := rectEnergy_add_le_of_lt_abs_rectError f wX wY P Q hS hT hwX hwY hε hdev
      have hbudget' : 1 - (t : ℝ) * ε ^ 2
          ≤ rectEnergy f wX wY (cutRefinePartition P S) (cutRefinePartition Q T) := by
        push_cast at hbudget
        linarith
      obtain ⟨P', Q', hP', hQ', hPcard, hQcard, hreg'⟩ := IH _ _ hbudget'
      refine ⟨P', Q', hP'.trans (cutRefinePartition_le P S),
        hQ'.trans (cutRefinePartition_le Q T), ?_, ?_, hreg'⟩
      · calc P'.parts.card ≤ (cutRefinePartition P S).parts.card * 2 ^ t := hPcard
          _ ≤ (2 * P.parts.card) * 2 ^ t :=
              Nat.mul_le_mul_right _ (card_parts_cutRefinePartition_le P S)
          _ = P.parts.card * 2 ^ (t + 1) := by ring
      · calc Q'.parts.card ≤ (cutRefinePartition Q T).parts.card * 2 ^ t := hQcard
          _ ≤ (2 * Q.parts.card) * 2 ^ t :=
              Nat.mul_le_mul_right _ (card_parts_cutRefinePartition_le Q T)
          _ = Q.parts.card * 2 ^ (t + 1) := by ring

/-- **The round budget is seed-independent**, exactly as in the Boolean development: the
energy is nonnegative and `⌈1/ε²⌉₊ + 1` rounds already exhaust a budget of `1`. The `+ 1` is
the strict-increment allowance — the last round must still be able to fail. -/
theorem one_sub_rounds_mul_sq_le_rectEnergy [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (P : Finpartition A) (Q : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ} (hε : 0 < ε) :
    1 - ((⌈1 / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) * ε ^ 2 ≤ rectEnergy f wX wY P Q := by
  have h0 : (0 : ℝ) ≤ rectEnergy f wX wY P Q := rectEnergy_nonneg P Q hwX hwY
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) * ε ^ 2 := by
    calc (1 : ℝ) = 1 / ε ^ 2 * ε ^ 2 := by field_simp
      _ ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε2.le
  push_cast
  nlinarith

/-! ### Step 6: the rectangular summit -/

/-- **Seeded rectangular Frieze–Kannan weak regularity.** From arbitrary seeds `P₀`, `Q₀`, a
*pair* of refinements whose stepped prediction is uniformly accurate on every test rectangle,
with **separate** left and right part-count bounds.

The two bounds are exposed individually and are never multiplied here. That is the point of
the rectangular formulation: the product is where sharpness is lost, so it is deferred to the
same-carrier adapter, which is the only place a factor `4` can appear. -/
theorem rect_frieze_kannan_refining [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P₀ : Finpartition A) (Q₀ : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition A, ∃ Q : Finpartition B, P ≤ P₀ ∧ Q ≤ Q₀ ∧
      P.parts.card ≤ P₀.parts.card * 2 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      Q.parts.card ≤ Q₀.parts.card * 2 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      ∀ S ⊆ A, ∀ T ⊆ B,
        |rectError f wX wY P Q S T| ≤ ε * (finsetMass wX A * finsetMass wY B) :=
  rectFkIterate f wX wY hwX hwY hf hε (⌈1 / ε ^ 2⌉₊ + 1) P₀ Q₀
    (one_sub_rounds_mul_sq_le_rectEnergy f wX wY P₀ Q₀ hwX hwY hε)

/-- The summit in cut-discrepancy form. -/
theorem rect_frieze_kannan_cutDiscrepancy [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (P₀ : Finpartition A) (Q₀ : Finpartition B)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finpartition A, ∃ Q : Finpartition B, P ≤ P₀ ∧ Q ≤ Q₀ ∧
      P.parts.card ≤ P₀.parts.card * 2 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      Q.parts.card ≤ Q₀.parts.card * 2 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      rectCutDiscrepancy f wX wY P Q ≤ ε * (finsetMass wX A * finsetMass wY B) := by
  obtain ⟨P, Q, hP, hQ, hPcard, hQcard, hreg⟩ :=
    rect_frieze_kannan_refining f wX wY P₀ Q₀ hwX hwY hf hε
  exact ⟨P, Q, hP, hQ, hPcard, hQcard, rectCutDiscrepancy_le_iff.mpr hreg⟩

/-! ### Step 6, continued: the same-carrier specialization

**Where the factor `4` comes from, and nowhere else.** Running the paired iteration at `ε/2`
costs `2^t` on each coordinate separately; the adapter of `Partition/RectKernelCut.lean` then
multiplies the two, and `2^t · 2^t = 4^t` appears for the first time.

The existing Boolean same-carrier summit in `Graph/FriezeKannan.lean` remains the **sharper
direct result** and is untouched: it obtains `4 ^ (⌈1/ε²⌉₊ + 1)` directly, whereas the route
below pays `⌈4/ε²⌉₊ + 1` rounds because it calls at `ε/2`. This theorem is an adapter, not a
replacement. -/
theorem rect_frieze_kannan_same_carrier [DecidableEq X] (f : RectKernel X X) (w₁ w₂ : X → ℝ)
    (P₀ Q₀ : Finpartition A) (hw₁ : ∀ x ∈ A, 0 ≤ w₁ x) (hw₂ : ∀ x ∈ A, 0 ≤ w₂ x)
    (hf : IsAbsUnitBoundedOnRectangle f A A) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Finpartition A, R ≤ P₀ ∧ R ≤ Q₀ ∧
      R.parts.card
        ≤ (P₀.parts.card * 2 ^ (⌈1 / (ε / 2) ^ 2⌉₊ + 1))
          * (Q₀.parts.card * 2 ^ (⌈1 / (ε / 2) ^ 2⌉₊ + 1)) ∧
      rectCutDiscrepancy f w₁ w₂ R R ≤ ε * (finsetMass w₁ A * finsetMass w₂ A) := by
  obtain ⟨P, Q, hP, hQ, hPcard, hQcard, hdisc⟩ :=
    rect_frieze_kannan_cutDiscrepancy f w₁ w₂ P₀ Q₀ hw₁ hw₂ hf (by linarith : (0:ℝ) < ε / 2)
  have hhalf : rectCutDiscrepancy f w₁ w₂ P Q
      ≤ (ε * (finsetMass w₁ A * finsetMass w₂ A)) / 2 := by
    calc rectCutDiscrepancy f w₁ w₂ P Q
        ≤ ε / 2 * (finsetMass w₁ A * finsetMass w₂ A) := hdisc
      _ = (ε * (finsetMass w₁ A * finsetMass w₂ A)) / 2 := by ring
  obtain ⟨hdisc', hcard'⟩ :=
    rectCutDiscrepancy_inf_self_le_of_le_half f w₁ w₂ P Q hw₁ hw₂ hhalf
  refine ⟨P ⊓ Q, inf_le_left.trans hP, inf_le_right.trans hQ, ?_, hdisc'⟩
  exact hcard'.trans (Nat.mul_le_mul hPcard hQcard)

/-! ### Tests -/

section Tests

private def cF : Fin 2 → ℝ := ![1, 1]

/-- Masses with a **genuine zero**, so the guard-free behaviour is actually exercised. -/
private def cF0 : Fin 2 → ℝ := ![1, 0]

/-- Right-hand weights on a carrier of a **different** size. -/
private def cG : Fin 3 → ℝ := ![1, 2, 3]

private theorem hcF : ∀ x ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ cF x := by
  intro x _
  fin_cases x <;> norm_num [cF]

private theorem hcG : ∀ y ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ cG y := by
  intro y _
  fin_cases y <;> norm_num [cG]

-- Cutting by the empty set, or by the whole carrier, is legal and still costs at most `2`.
example (P : Finpartition (Finset.univ : Finset (Fin 3))) :
    (cutRefinePartition P (∅ : Finset (Fin 3))).parts.card ≤ 2 * P.parts.card :=
  card_parts_cutRefinePartition_le P ∅

-- **Separation** on a genuinely split carrier.
example (P : Finpartition (Finset.univ : Finset (Fin 3))) {C : Finset (Fin 3)}
    (hC : C ∈ (cutRefinePartition P ({0, 1} : Finset (Fin 3))).parts) :
    C ⊆ ({0, 1} : Finset (Fin 3)) ∨ Disjoint C ({0, 1} : Finset (Fin 3)) :=
  cutRefinePartition_part_subset_or_disjoint P _ hC

-- The test set is recovered as a union of cells.
example (P : Finpartition (Finset.univ : Finset (Fin 3))) :
    ((cutRefinePartition P ({0, 1} : Finset (Fin 3))).parts.filter
        (· ⊆ ({0, 1} : Finset (Fin 3)))).biUnion id = ({0, 1} : Finset (Fin 3)) :=
  biUnion_cutRefinePartition_filter_subset P (Finset.subset_univ _)

-- **Both coordinates cut independently**, on carriers of different sizes: the seam that
-- keeps the factor `4` out until the same-carrier adapter multiplies the two bounds.
example (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (S : Finset (Fin 2))
    (T : Finset (Fin 3)) :
    (cutRefinePartition P S).parts.card ≤ 2 * P.parts.card
      ∧ (cutRefinePartition Q T).parts.card ≤ 2 * Q.parts.card :=
  card_parts_cut_pair_le P Q S T

-- **The raw energy increment on asymmetric carriers.** `f` is an arbitrary kernel: there is
-- no boundedness hypothesis anywhere, and no positive-mass hypothesis — the witness supplies
-- the positivity itself.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) {S : Finset (Fin 2)}
    {T : Finset (Fin 3)} (hS : S ⊆ Finset.univ) (hT : T ⊆ Finset.univ) {ε : ℝ} (hε : 0 < ε)
    (hwit : ε * (finsetMass cF Finset.univ * finsetMass cG Finset.univ)
      < |rectError f cF cG P Q S T|) :
    rectEnergyNum f cF cG P Q
        + ε ^ 2 * (finsetMass cF Finset.univ * finsetMass cG Finset.univ)
      ≤ rectEnergyNum f cF cG (cutRefinePartition P S) (cutRefinePartition Q T) :=
  rectEnergyNum_add_le_of_lt_abs_rectError f cF cG P Q hS hT hcF hcG hε hwit

-- …and its normalized form, where the `ε²` gain is stated outright.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) {S : Finset (Fin 2)}
    {T : Finset (Fin 3)} (hS : S ⊆ Finset.univ) (hT : T ⊆ Finset.univ) {ε : ℝ} (hε : 0 < ε)
    (hwit : ε * (finsetMass cF Finset.univ * finsetMass cG Finset.univ)
      < |rectError f cF cG P Q S T|) :
    rectEnergy f cF cG P Q + ε ^ 2
      ≤ rectEnergy f cF cG (cutRefinePartition P S) (cutRefinePartition Q T) :=
  rectEnergy_add_le_of_lt_abs_rectError f cF cG P Q hS hT hcF hcG hε hwit

-- **A witness cannot exist on a zero-mass carrier**, which is why neither theorem above
-- needs a positive-mass hypothesis. Note `ε` is entirely unconstrained here — not even
-- `0 < ε` — since at zero total mass both the threshold and the error vanish outright.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) {S : Finset (Fin 2)}
    {T : Finset (Fin 3)} (hS : S ⊆ Finset.univ) (hT : T ⊆ Finset.univ) {ε : ℝ}
    (hwit : ε * (finsetMass cF Finset.univ * finsetMass cG Finset.univ)
      < |rectError f cF cG P Q S T|) :
    0 < finsetMass cF Finset.univ * finsetMass cG Finset.univ :=
  finsetMass_mul_pos_of_lt_abs_rectError f cF cG P Q hS hT hcF hcG hwit

-- **The seeded rectangular summit**, on carriers of different sizes, with the two part-count
-- bounds arriving **separately**. Nothing here multiplies them.
example (f : RectKernel (Fin 2) (Fin 3)) (P₀ : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q₀ : Finpartition (Finset.univ : Finset (Fin 3)))
    (hf : IsAbsUnitBoundedOnRectangle f Finset.univ Finset.univ) :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 2)),
      ∃ Q : Finpartition (Finset.univ : Finset (Fin 3)), P ≤ P₀ ∧ Q ≤ Q₀ ∧
        P.parts.card ≤ P₀.parts.card * 2 ^ (⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ + 1) ∧
        Q.parts.card ≤ Q₀.parts.card * 2 ^ (⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ + 1) ∧
        ∀ S ⊆ (Finset.univ : Finset (Fin 2)), ∀ T ⊆ (Finset.univ : Finset (Fin 3)),
          |rectError f cF cG P Q S T|
            ≤ (1 / 2 : ℝ) * (finsetMass cF Finset.univ * finsetMass cG Finset.univ) :=
  rect_frieze_kannan_refining f cF cG P₀ Q₀ hcF hcG hf (by norm_num)

-- **The same-carrier adapter is the only place a factor `4` appears**: the two `2^t` bounds
-- are multiplied here and nowhere earlier. Note the round count is at `ε/2`, which is exactly
-- why this is weaker than the Boolean summit it adapts to.
example (f : RectKernel (Fin 2) (Fin 2))
    (P₀ Q₀ : Finpartition (Finset.univ : Finset (Fin 2)))
    (hf : IsAbsUnitBoundedOnRectangle f Finset.univ Finset.univ) :
    ∃ R : Finpartition (Finset.univ : Finset (Fin 2)), R ≤ P₀ ∧ R ≤ Q₀ ∧
      R.parts.card
        ≤ (P₀.parts.card * 2 ^ (⌈1 / ((1 / 2 : ℝ) / 2) ^ 2⌉₊ + 1))
          * (Q₀.parts.card * 2 ^ (⌈1 / ((1 / 2 : ℝ) / 2) ^ 2⌉₊ + 1)) ∧
      rectCutDiscrepancy f cF cF R R
        ≤ (1 / 2 : ℝ) * (finsetMass cF Finset.univ * finsetMass cF Finset.univ) :=
  rect_frieze_kannan_same_carrier f cF cF P₀ Q₀ hcF hcF hf (by norm_num)

-- The round budget is **seed-independent**: it holds for an arbitrary starting pair.
example (f : RectKernel (Fin 2) (Fin 3)) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    1 - ((⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2
      ≤ rectEnergy f cF cG P Q :=
  one_sub_rounds_mul_sq_le_rectEnergy f cF cG P Q hcF hcG (by norm_num)

-- The mass-weighted Cauchy–Schwarz the energy step consumes.
example (a : Fin 2 → ℝ) :
    (∑ i, a i * cF i) ^ 2 ≤ (∑ i, cF i) * ∑ i, a i ^ 2 * cF i :=
  sq_sum_mul_le_sum_mul_sum_sq_mul a cF Finset.univ
    (fun i _ => by fin_cases i <;> norm_num [cF])

-- …with **no** positive-mass hypothesis. Masses `[1, 0]`, so the zero-mass index is real and
-- drops from both sides unaided. This is the branch the energy step will rely on.
example (a : Fin 2 → ℝ) :
    (∑ i, a i * cF0 i) ^ 2 ≤ (∑ i, cF0 i) * ∑ i, a i ^ 2 * cF0 i :=
  sq_sum_mul_le_sum_mul_sum_sq_mul a cF0 Finset.univ
    (fun i _ => by fin_cases i <;> norm_num [cF0])

-- …and the zero-mass index really is inert: both sides collapse to the surviving term.
example (a : Fin 2 → ℝ) :
    (∑ i, a i * cF0 i) ^ 2 = (a 0) ^ 2 ∧ (∑ i, cF0 i) * ∑ i, a i ^ 2 * cF0 i = (a 0) ^ 2 := by
  constructor <;> simp [Fin.sum_univ_two, cF0]

-- **Every mass zero**: the inequality degenerates to `0 ≤ 0` rather than dividing by zero.
example (a : Fin 2 → ℝ) :
    (∑ i, a i * (0 : ℝ)) ^ 2 ≤ (∑ _i : Fin 2, (0 : ℝ)) * ∑ i, a i ^ 2 * (0 : ℝ) :=
  sq_sum_mul_le_sum_mul_sum_sq_mul a (fun _ => 0) Finset.univ (fun _ _ => le_rfl)

end Tests

end RegularityLemmata
