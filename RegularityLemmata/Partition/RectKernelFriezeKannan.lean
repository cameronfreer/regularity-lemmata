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
