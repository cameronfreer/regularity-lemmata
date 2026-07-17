/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.BadMass
import RegularityLemmata.Graph.RegularDegree

/-!
# Phase 11 unit 3: diagonal-inclusive bad mass and regularity

The diagonal-inclusive strengthening of `Graph/BadMass.lean`, a **parallel additive
layer** (Phase 11 design freeze in `ARCHITECTURE.md`): the frozen off-diagonal
`IsBadPair`/`IsRegularPartition` surface is unchanged, because the mathlib uniformity
bridge (`Graph/Bridge.lean`) cannot deliver diagonal control and the Phase 10 counting
charges select `IsBadPair` by frozen design.

An ordered pair of parts — **including a part paired with itself** — is `ε`-bad when it
fails `ε`-uniformity (`IsBadPairDiag`, no distinctness conjunct). `badMassDiagNum` is
the raw mass over these pairs, `badMassDiag` its normalization, `IsRegularPartitionDiag`
the resulting regularity notion. Bridges: diagonal-inclusive regularity implies the
off-diagonal notion; the diagonal-inclusive bad mass decomposes exactly into the
off-diagonal bad mass plus the bad diagonal blocks; and the layer transports along
ordered reversal (`swapRel`).

Removal-grade counting needs exactly this: copies with two or three vertices in one
cell are counted on pairs `(C, C)`, about which off-diagonal regularity says nothing
(see the tests, the dual of the frozen distinction test in
`Relational/StrongCountingLifting.lean`).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

/-- An ordered pair of parts failing `ε`-uniformity — diagonal pairs included. -/
def IsBadPairDiag (C D : Finset α) : Prop :=
  ¬ IsUniformPair R C D ε

omit [DecidableEq α] in
/-- An off-diagonal bad pair is a diagonal-inclusive bad pair. -/
theorem IsBadPair.isBadPairDiag {C D : Finset α} (h : IsBadPair R ε C D) :
    IsBadPairDiag R ε C D :=
  h.2

open Classical in
/-- Raw diagonal-inclusive bad mass: `Σ |C| · |D|` over all `ε`-bad ordered pairs of
parts, diagonal pairs included. -/
noncomputable def badMassDiagNum (P : Finpartition s) : ℝ :=
  ∑ uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPairDiag R ε uv.1 uv.2),
    (uv.1.card : ℝ) * uv.2.card

/-- Normalized diagonal-inclusive bad mass, in `[0, 1]`; `0` on the empty ground set. -/
noncomputable def badMassDiag (P : Finpartition s) : ℝ :=
  badMassDiagNum R ε P / (s.card : ℝ) ^ 2

/-- Diagonal-inclusive `ε`-regularity of a partition. -/
def IsRegularPartitionDiag (P : Finpartition s) : Prop :=
  badMassDiag R ε P ≤ ε

variable {P : Finpartition s}

theorem badMassDiagNum_nonneg : 0 ≤ badMassDiagNum R ε P :=
  Finset.sum_nonneg fun uv _ => by positivity

theorem badMassDiag_nonneg : 0 ≤ badMassDiag R ε P :=
  div_nonneg (badMassDiagNum_nonneg R ε) (by positivity)

theorem badMassDiagNum_le_sq : badMassDiagNum R ε P ≤ (s.card : ℝ) ^ 2 := by
  classical
  calc badMassDiagNum R ε P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, (uv.1.card : ℝ) * uv.2.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun uv _ _ => by positivity
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

theorem badMassDiag_le_one : badMassDiag R ε P ≤ 1 := by
  unfold badMassDiag
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact badMassDiagNum_le_sq R ε

/-- Diagonal-inclusive bad mass is antitone in the tolerance. -/
theorem badMassDiagNum_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassDiagNum R ε' P ≤ badMassDiagNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  exact ⟨huv.1, fun hunif => huv.2 (hunif.mono hεε)⟩

theorem badMassDiag_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassDiag R ε' P ≤ badMassDiag R ε P :=
  div_le_div_of_nonneg_right (badMassDiagNum_anti R hεε) (by positivity) |>.trans_eq rfl

/-- Diagonal-inclusive regularity is monotone in the tolerance. -/
theorem IsRegularPartitionDiag.mono {ε ε' : ℝ} (hεε : ε ≤ ε')
    (h : IsRegularPartitionDiag R ε P) : IsRegularPartitionDiag R ε' P :=
  le_trans (badMassDiag_anti R hεε) (le_trans h hεε)

/-- Everything is diagonal-inclusively `1`-regular. -/
theorem isRegularPartitionDiag_one : IsRegularPartitionDiag R 1 P :=
  badMassDiag_le_one R 1

/-- **Raw conversion**: a diagonal-inclusively regular partition has raw
diagonal-inclusive bad mass at most `ε·|s|²`. -/
theorem badMassDiagNum_le_of_isRegularPartitionDiag
    (h : IsRegularPartitionDiag R ε P) :
    badMassDiagNum R ε P ≤ ε * (s.card : ℝ) ^ 2 := by
  rcases eq_or_ne ((s.card : ℝ)) 0 with h0 | h0
  · have hle : badMassDiagNum R ε P ≤ (s.card : ℝ) ^ 2 := badMassDiagNum_le_sq R ε
    rw [h0] at hle ⊢
    simpa using hle
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (s.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
      positivity
    rw [IsRegularPartitionDiag, badMassDiag, div_le_iff₀ hpos] at h
    linarith [h]

/-! ### Bridges to the off-diagonal layer -/

/-- The off-diagonal bad mass is dominated by the diagonal-inclusive one. -/
theorem badMassNum_le_badMassDiagNum : badMassNum R ε P ≤ badMassDiagNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  exact ⟨huv.1, huv.2.isBadPairDiag⟩

theorem badMass_le_badMassDiag : badMass R ε P ≤ badMassDiag R ε P :=
  div_le_div_of_nonneg_right (badMassNum_le_badMassDiagNum R ε) (by positivity)
    |>.trans_eq rfl

/-- **Diagonal-inclusive regularity implies the frozen off-diagonal notion** — every
Phase 9/10 consumer applies unchanged through this bridge. -/
theorem IsRegularPartitionDiag.isRegularPartition
    (h : IsRegularPartitionDiag R ε P) : IsRegularPartition R ε P :=
  le_trans (badMass_le_badMassDiag R ε) h

open Classical in
/-- **Exact decomposition**: the diagonal-inclusive bad mass is the off-diagonal bad
mass plus the mass `|C|²` of the parts whose diagonal pair fails uniformity. -/
theorem badMassDiagNum_eq_badMassNum_add :
    badMassDiagNum R ε P = badMassNum R ε P
      + ∑ C ∈ P.parts.filter (fun C => ¬ IsUniformPair R C C ε), (C.card : ℝ) ^ 2 := by
  rw [badMassDiagNum,
    ← Finset.sum_filter_add_sum_filter_not
      ((P.parts ×ˢ P.parts).filter fun uv => IsBadPairDiag R ε uv.1 uv.2)
      (fun uv => uv.1 ≠ uv.2)]
  congr 1
  · rw [badMassNum, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun uv _ => ?_) fun _ _ => rfl
    show IsBadPairDiag R ε uv.1 uv.2 ∧ uv.1 ≠ uv.2 ↔ IsBadPair R ε uv.1 uv.2
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · rw [Finset.filter_filter]
    refine Finset.sum_nbij' (fun uv => uv.1) (fun C => (C, C)) ?_ ?_ ?_ ?_ ?_
    · intro uv huv
      rw [Finset.mem_filter, Finset.mem_product] at huv
      rw [Finset.mem_filter]
      have heq : uv.1 = uv.2 := not_ne_iff.mp huv.2.2
      exact ⟨huv.1.1, heq ▸ huv.2.1⟩
    · intro C hC
      rw [Finset.mem_filter] at hC
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hC.1, hC.1⟩, hC.2, not_ne_iff.mpr rfl⟩
    · intro uv huv
      rw [Finset.mem_filter] at huv
      exact Prod.ext rfl (not_ne_iff.mp huv.2.2)
    · intro C _
      rfl
    · intro uv huv
      rw [Finset.mem_filter] at huv
      have heq : uv.1 = uv.2 := not_ne_iff.mp huv.2.2
      rw [← heq, sq]

/-! ### Ordered-reversal transport -/

omit [DecidableEq α] in
/-- Diagonal-inclusive badness transports along ordered reversal. -/
theorem isBadPairDiag_swapRel_iff {C D : Finset α} :
    IsBadPairDiag (swapRel R) ε C D ↔ IsBadPairDiag R ε D C :=
  not_congr (isUniformPair_swapRel_iff R)

open Classical in
/-- Diagonal-inclusive bad mass is reversal-invariant. -/
theorem badMassDiagNum_swapRel : badMassDiagNum (swapRel R) ε P = badMassDiagNum R ε P := by
  rw [badMassDiagNum, badMassDiagNum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro uv huv
    rw [Finset.mem_filter, Finset.mem_product] at huv ⊢
    exact ⟨⟨huv.1.2, huv.1.1⟩, (isBadPairDiag_swapRel_iff R ε).mp huv.2⟩
  · intro uv huv
    rw [Finset.mem_filter, Finset.mem_product] at huv ⊢
    exact ⟨⟨huv.1.2, huv.1.1⟩, (isBadPairDiag_swapRel_iff R ε).mpr huv.2⟩
  · intro uv _
    rfl
  · intro uv _
    rfl
  · intro uv _
    rw [mul_comm]
    rfl

theorem badMassDiag_swapRel : badMassDiag (swapRel R) ε P = badMassDiag R ε P := by
  rw [badMassDiag, badMassDiag, badMassDiagNum_swapRel]

theorem isRegularPartitionDiag_swapRel_iff :
    IsRegularPartitionDiag (swapRel R) ε P ↔ IsRegularPartitionDiag R ε P := by
  rw [IsRegularPartitionDiag, IsRegularPartitionDiag, badMassDiag_swapRel]

/-! ### Tests and adversarial examples -/

-- The single-cell (indiscrete) partition of the two-point ground set, and the equality
-- relation supported inside that one cell.
private abbrev onePart : Finpartition (Finset.univ : Finset (Fin 2)) :=
  Finpartition.indiscrete (by decide)

-- The full diagonal pair fails `1/4`-uniformity: the sub-blocks `{0}` and `{1}` deviate
-- from the block density `1/2` by `1/2`.
private theorem eqDiag_bad :
    IsBadPairDiag (fun a b : Fin 2 => a = b) (1 / 4)
      (Finset.univ : Finset (Fin 2)) Finset.univ := by
  intro h
  have hd1 : pairDensity (fun a b : Fin 2 => a = b) {0} {1} = 0 := by
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 2 => a = b) {0} {1} = 0 from by decide]; simp
  have hd2 : pairDensity (fun a b : Fin 2 => a = b) Finset.univ
      (Finset.univ : Finset (Fin 2)) = 1 / 2 := by
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 2 => a = b) Finset.univ
        (Finset.univ : Finset (Fin 2)) = 2 from by decide,
      show (Finset.univ : Finset (Fin 2)).card = 2 from by decide]
    norm_num
  have hdev := h (Finset.subset_univ {0}) (Finset.subset_univ {1})
    (by rw [show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
      show ({0} : Finset (Fin 2)).card = 1 from by decide]; norm_num)
    (by rw [show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
      show ({1} : Finset (Fin 2)).card = 1 from by decide]; norm_num)
  rw [hd1, hd2, abs_le] at hdev
  linarith [hdev.1]

-- **Off-diagonal regularity says nothing about a relation supported inside one cell**
-- (the dual of the frozen distinction test in `Relational/StrongCountingLifting.lean`).
-- On the single-cell partition the off-diagonal bad mass is vacuously `0`, so the
-- partition is off-diagonally regular at EVERY nonnegative tolerance…
example {ε : ℝ} (hε : 0 ≤ ε) :
    IsRegularPartition (fun a b : Fin 2 => a = b) ε onePart := by
  classical
  have h0 : badMassNum (fun a b : Fin 2 => a = b) ε onePart = 0 := by
    rw [badMassNum]
    refine Finset.sum_eq_zero fun uv huv => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finpartition.indiscrete_parts,
      Finset.mem_singleton] at huv
    exact absurd (huv.1.1.trans huv.1.2.symm) huv.2.1
  rw [IsRegularPartition, badMass, h0, zero_div]
  exact hε

-- …while the SAME partition is diagonal-inclusively bad at `1/4`: its one diagonal
-- pair carries the whole mass.
example : ¬ IsRegularPartitionDiag (fun a b : Fin 2 => a = b) (1 / 4) onePart := by
  classical
  intro h
  have hcardN : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
  have hcard : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by rw [hcardN]; norm_num
  have h4 : (4 : ℝ) ≤ badMassDiagNum (fun a b : Fin 2 => a = b) (1 / 4) onePart := by
    rw [badMassDiagNum]
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun uv : Finset (Fin 2) × Finset (Fin 2) =>
        (uv.1.card : ℝ) * uv.2.card) (fun uv _ => by positivity)
        (a := (Finset.univ, Finset.univ)) ?_)
    · rw [hcard]
      norm_num
    · rw [Finset.mem_filter, Finset.mem_product, Finpartition.indiscrete_parts,
        Finset.mem_singleton]
      exact ⟨⟨rfl, rfl⟩, eqDiag_bad⟩
  rw [IsRegularPartitionDiag, badMassDiag, hcard] at h
  norm_num at h
  linarith

-- Every off-diagonal bad pair is a diagonal-inclusive bad pair, statement-level.
example {C D : Finset (Fin 4)} {R : Fin 4 → Fin 4 → Prop} [DecidableRel R] {ε : ℝ}
    (h : IsBadPair R ε C D) : IsBadPairDiag R ε C D :=
  h.isBadPairDiag

-- On the empty ground set every partition is diagonal-inclusively regular at every
-- nonnegative tolerance.
example (P : Finpartition (∅ : Finset (Fin 3))) {ε : ℝ} (hε : 0 ≤ ε) :
    IsRegularPartitionDiag (fun a b : Fin 3 => a < b) ε P := by
  have h0 : badMassDiag (fun a b : Fin 3 => a < b) ε P = 0 := by
    rw [badMassDiag]
    simp
  rw [IsRegularPartitionDiag, h0]
  exact hε

end RegularityLemmata
