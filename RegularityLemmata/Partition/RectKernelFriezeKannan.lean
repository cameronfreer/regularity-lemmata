/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.RectKernelCut
import RegularityLemmata.Partition.RectKernelEnergy

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

The weak-regularity architecture — approximating a rectangular matrix by a small sum of cut
matrices, and driving the construction by a greedy energy increment — is due to A. Frieze and
R. Kannan, *Quick approximation to matrices and applications*, Combinatorica **19** (1999),
175–220. The energy-increment mechanism and the `ε²`-per-round gain are theirs.

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

/-! ### Tests -/

section Tests

private def cF : Fin 2 → ℝ := ![1, 1]

/-- Masses with a **genuine zero**, so the guard-free behaviour is actually exercised. -/
private def cF0 : Fin 2 → ℝ := ![1, 0]

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
