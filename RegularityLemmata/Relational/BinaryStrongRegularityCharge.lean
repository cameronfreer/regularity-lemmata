/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.StrongCountingLifting

/-!
# Strong transversal counting: the regularity charge

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), first half of the summit. This file holds
the **common-index expansions** — rewriting both the actual transversal induced count
(`transversalInducedCount`) and its fine step estimate (`fineInducedEstimate`) as a single double
sum over the shared fine refinement index — and the **regularity charge**: the actual count is
within `10·τ·|s|³` of the fine estimate, where `τ` is the fine partition's regularity parameter.

The charge decomposes as `7·τ` (the exact three-vertex count on uniform fine triples, via
`abs_inducedEmbeddingCountOn_three_sub_le`) plus `3·τ` (the `IsBadPair` lifting on nonuniform
triples, via `selectedRefinementPairTripleMass_*_le`, `sum_refinement_isBadPair_mass_eq`, and
`badMassNum_le_of_isRegularPartition`), built on the nested selected-pair lifting in
`Relational/StrongCountingLifting.lean`.

The density-shift charge (`3·η + 3·δ/η²`) and the assembled summit live in
`Relational/BinaryStrongCounting.lean`, which imports this file.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### The bad-pair refinement-mass reindex -/

open Classical in
/-- Every fine bad pair refines a unique coarse pair, so the coarse-nested `IsBadPair` fine
pairs are exactly the bad pairs of `Q`. -/
theorem selectedFinePairs_isBadPair_eq {Q Pc : Finpartition s} (hQP : Q ≤ Pc)
    (R : V → V → Prop) [DecidableRel R] (τ : ℝ) :
    selectedFinePairs Q Pc (fun _ p => IsBadPair R τ p.1 p.2)
      = (Q.parts ×ˢ Q.parts).filter (fun p => IsBadPair R τ p.1 p.2) := by
  ext p
  rw [Finset.mem_filter]
  constructor
  · intro hp
    have hsub := selectedFinePairs_subset hp
    rw [selectedFinePairs, Finset.mem_biUnion] at hp
    obtain ⟨pd, _, hp⟩ := hp
    rw [Finset.mem_filter] at hp
    exact ⟨hsub, hp.2⟩
  · rintro ⟨hpq, hbad⟩
    rw [Finset.mem_product] at hpq
    obtain ⟨X, hX, hAX⟩ := hQP hpq.1
    obtain ⟨Y, hY, hBY⟩ := hQP hpq.2
    rw [selectedFinePairs, Finset.mem_biUnion]
    exact ⟨(X, Y), Finset.mem_product.mpr ⟨hX, hY⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpq.1, hAX⟩, Finset.mem_filter.mpr ⟨hpq.2, hBY⟩⟩, hbad⟩⟩

open Classical in
/-- **Bad-pair refinement-mass reindex.** The coarse-nested `IsBadPair` fine-pair mass is the
raw bad mass of `Q` — this is what lets `badMassNum_le_of_isRegularPartition` charge the
nonuniform occurrences. -/
theorem sum_refinement_isBadPair_mass_eq {Q Pc : Finpartition s} (hQP : Q ≤ Pc)
    (R : V → V → Prop) [DecidableRel R] {τ : ℝ} :
    (∑ pd ∈ Pc.parts ×ˢ Pc.parts,
        ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter
            (fun p => IsBadPair R τ p.1 p.2),
          ((p.1.card : ℝ) * p.2.card))
      = badMassNum R τ Q := by
  rw [← sum_selectedFinePairs_mass (sel := fun _ p => IsBadPair R τ p.1 p.2),
    selectedFinePairs_isBadPair_eq hQP R τ, badMassNum]

/-! ### Common-index expansions -/

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L]

/-- The product of the three required palette densities on a box. -/
noncomputable def requiredPaletteProduct (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (T : Fin 3 → Finset V) : ℝ :=
  pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1) *
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2) *
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)

/-- The box volume. -/
def cellTripleVolume (T : Fin 3 → Finset V) : ℝ :=
  (T 0).card * (T 1).card * (T 2).card

omit [DecidableEq V] in
theorem cellTripleVolume_nonneg (T : Fin 3 → Finset V) : 0 ≤ cellTripleVolume T := by
  rw [cellTripleVolume]; positivity

omit [DecidableEq V] in
theorem requiredPaletteProduct_nonneg (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (T : Fin 3 → Finset V) : 0 ≤ requiredPaletteProduct P M T := by
  rw [requiredPaletteProduct]
  have h1 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 0 1))
    (A := T 0) (B := T 1)
  have h2 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 0 2))
    (A := T 0) (B := T 2)
  have h3 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 1 2))
    (A := T 1) (B := T 2)
  positivity

omit [DecidableEq V] in
theorem requiredPaletteProduct_le_one (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (T : Fin 3 → Finset V) : requiredPaletteProduct P M T ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ pairDensity_le_one pairDensity_nonneg pairDensity_le_one)
    pairDensity_nonneg pairDensity_le_one

/-- The fine step estimate: the actual estimate expanded over the fine refinement, using the
**fine** cells' palette densities. -/
noncomputable def fineInducedEstimate (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q Pc : Finpartition s) : ℝ :=
  ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M),
    ∑ W ∈ refinementTriples Q T, requiredPaletteProduct P M W * cellTripleVolume W

variable {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {Q Pc : Finpartition s}

/-- **Actual count over the common fine index.** -/
theorem transversalInducedCount_eq_sum_refinement_of_profiled [AtMostBinary L]
    (hQP : Q ≤ Pc) (hprofile : Pc ≤ binaryProfilePartition M s) :
    (transversalInducedCount P M Pc : ℝ)
      = ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M),
          ∑ W ∈ refinementTriples Q T, (inducedEmbeddingCountOn P M W : ℝ) := by
  rw [transversalInducedCount, Nat.cast_sum,
    ← Finset.sum_filter_add_sum_filter_not (transversalCellTriples Pc) (MatchesThreeProfiles P M)
      (fun T => (inducedEmbeddingCountOn P M T : ℝ))]
  have hzero : ∑ T ∈ (transversalCellTriples Pc).filter (fun T => ¬ MatchesThreeProfiles P M T),
      (inducedEmbeddingCountOn P M T : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [Finset.mem_filter] at hT
    rw [inducedEmbeddingCountOn_eq_zero_of_not_matchesThreeProfiles hprofile
      (fun i => transversalCellTriples_cell_mem hT.1 i) hT.2, Nat.cast_zero]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_filter] at hT
  rw [inducedEmbeddingCountOn_refinement_three hQP
    (fun i => transversalCellTriples_cell_mem hT.1 i), Nat.cast_sum]

/-- **Coarse estimate over the common fine index** (using the coarse density on each box). -/
theorem coarseInducedEstimate_eq_sum_refinement (hQP : Q ≤ Pc) :
    coarseInducedEstimate P M Pc
      = ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M),
          ∑ W ∈ refinementTriples Q T, requiredPaletteProduct P M T * cellTripleVolume W := by
  rw [coarseInducedEstimate]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_filter] at hT
  have hvol : ∑ W ∈ refinementTriples Q T, cellTripleVolume W = cellTripleVolume T :=
    sum_refinement_volume_eq hQP (fun i => transversalCellTriples_cell_mem hT.1 i)
  rw [← Finset.mul_sum, hvol, requiredPaletteProduct, cellTripleVolume]
  ring

/-! ### The regularity charge -/

/-- Crude box bound: an induced count never exceeds the box volume. -/
theorem inducedEmbeddingCountOn_le_cellTripleVolume (P : FiniteRelModel L (Fin 3))
    (M : FiniteRelModel L V) (W : Fin 3 → Finset V) :
    (inducedEmbeddingCountOn P M W : ℝ) ≤ cellTripleVolume W := by
  rw [inducedEmbeddingCountOn, cellTripleVolume]
  have hle : ((Fintype.piFinset W).filter
      (fun f => Function.Injective f ∧ PreservesAndReflects P M f)).card
      ≤ (W 0).card * (W 1).card * (W 2).card :=
    (Finset.card_filter_le _ _).trans_eq (by rw [Fintype.card_piFinset, Fin.prod_univ_three])
  exact_mod_cast hle

/-- The total fine volume over profile-matching coarse triples is at most `|s|³`. -/
theorem sum_matching_refinement_volume_le_cube (hQP : Q ≤ Pc) :
    ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M),
        ∑ W ∈ refinementTriples Q T, cellTripleVolume W
      ≤ (s.card : ℝ) ^ 3 :=
  calc ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M),
          ∑ W ∈ refinementTriples Q T, cellTripleVolume W
      = ∑ T ∈ (transversalCellTriples Pc).filter (MatchesThreeProfiles P M), cellTripleVolume T :=
        Finset.sum_congr rfl fun _ hT =>
          sum_refinement_volume_eq hQP
            (fun i => transversalCellTriples_cell_mem (Finset.mem_filter.mp hT).1 i)
    _ ≤ ∑ T ∈ transversalCellTriples Pc, cellTripleVolume T :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun T _ _ => cellTripleVolume_nonneg T)
    _ ≤ (s.card : ℝ) ^ 3 := sum_transversal_volume_le Pc

/-- **The regularity charge.** The transversal induced count is within `10·τ·|s|³` of the
fine estimate, where `τ = E w.coarse.parts.card`: `7·τ` from the exact three-vertex count on
uniform fine triples, and `3·τ` from the three `IsBadPair` liftings on nonuniform ones. -/
theorem BinaryPaletteStrongWitness.abs_transversalInducedCount_sub_fineEstimate_le
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) :
    |(transversalInducedCount P M w.coarse : ℝ) - fineInducedEstimate P M w.fine w.coarse|
      ≤ 10 * E w.coarse.parts.card * (s.card : ℝ) ^ 3 := by
  classical
  set τ := E w.coarse.parts.card with hτdef
  have hτ0 : 0 ≤ τ := (E.pos _).le
  set S := (transversalCellTriples w.coarse).filter (MatchesThreeProfiles P M) with hSdef
  -- the three IsBadPair predicates on a fine triple
  set bad : Fin 3 → Fin 3 → BinaryPairPalette L → (Fin 3 → Finset V) → Prop :=
    fun i j c W => IsBadPair (HasBinaryPairPalette M c) τ (W i) (W j) with hbaddef
  -- pointwise bound
  have hpw : ∀ T ∈ S, ∀ W ∈ refinementTriples w.fine T,
      |(inducedEmbeddingCountOn P M W : ℝ) - requiredPaletteProduct P M W * cellTripleVolume W|
        ≤ 7 * τ * cellTripleVolume W
          + (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
          + (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
          + (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0) := by
    intro T hT W hW
    rw [hSdef, Finset.mem_filter] at hT
    have hWtrans : W ∈ transversalCellTriples w.fine :=
      refinementTriples_subset_transversal hT.1 hW
    have hsub : ∀ i, W i ⊆ T i := by
      intro i
      have := (Fintype.mem_piFinset.mp hW) i
      rw [refinementFiber, Finset.mem_filter] at this
      exact this.2
    have hprofW : MatchesThreeProfiles P M W := hT.2.mono hsub
    have hvolnn : 0 ≤ cellTripleVolume W := cellTripleVolume_nonneg W
    have hicle : (inducedEmbeddingCountOn P M W : ℝ) ≤ cellTripleVolume W :=
      inducedEmbeddingCountOn_le_cellTripleVolume P M W
    have hicnn : 0 ≤ (inducedEmbeddingCountOn P M W : ℝ) := Nat.cast_nonneg _
    have hrp0 : 0 ≤ requiredPaletteProduct P M W := requiredPaletteProduct_nonneg P M W
    have hrp1 : requiredPaletteProduct P M W ≤ 1 := requiredPaletteProduct_le_one P M W
    have hcrude : |(inducedEmbeddingCountOn P M W : ℝ)
        - requiredPaletteProduct P M W * cellTripleVolume W| ≤ cellTripleVolume W := by
      rw [abs_le]; constructor <;> nlinarith
    have hi01 : 0 ≤ (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0) := by
      split_ifs <;> [exact hvolnn; exact le_rfl]
    have hi02 : 0 ≤ (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0) := by
      split_ifs <;> [exact hvolnn; exact le_rfl]
    have hi12 : 0 ≤ (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0) := by
      split_ifs <;> [exact hvolnn; exact le_rfl]
    by_cases hb : bad 0 1 (binaryPairPalette P 0 1) W ∨ bad 0 2 (binaryPairPalette P 0 2) W
      ∨ bad 1 2 (binaryPairPalette P 1 2) W
    · have hge : cellTripleVolume W
          ≤ (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
            + (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
            + (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0) := by
        rcases hb with h | h | h
        · rw [if_pos h]; linarith
        · rw [if_pos h]; linarith
        · rw [if_pos h]; linarith
      linarith [hcrude, hge,
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 7) hτ0) hvolnn]
    · rw [not_or, not_or] at hb
      obtain ⟨hn01, hn02, hn12⟩ := hb
      have hne : ∀ {i j : Fin 3}, i ≠ j → W i ≠ W j := fun hij => transversalCellTriples_ne hWtrans hij
      have hu : ∀ {i j : Fin 3} {c}, ¬ bad i j c W → i ≠ j →
          IsUniformPair (HasBinaryPairPalette M c) (W i) (W j) τ := by
        intro i j c hnb hij
        by_contra hcon
        exact hnb ⟨hne hij, hcon⟩
      rw [if_neg hn01, if_neg hn02, if_neg hn12, add_zero, add_zero, add_zero]
      have hWeq : (![W 0, W 1, W 2] : Fin 3 → Finset V) = W := by funext i; fin_cases i <;> rfl
      have hbound := abs_inducedEmbeddingCountOn_three_sub_le (P := P) (M := M)
        hnull (hprofW 0) (hprofW 1) (hprofW 2)
        (transversalCellTriples_disjoint hWtrans (by decide))
        (transversalCellTriples_disjoint hWtrans (by decide))
        (transversalCellTriples_disjoint hWtrans (by decide)) hτ0 hτ1
        (hu hn01 (by decide)) (hu hn02 (by decide)) (hu hn12 (by decide))
      rw [hWeq] at hbound
      have heq1 : requiredPaletteProduct P M W * cellTripleVolume W
          = pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
              * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
              * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
              * (W 0).card * (W 1).card * (W 2).card := by
        rw [requiredPaletteProduct, cellTripleVolume]; ring
      have heq2 : (7 : ℝ) * τ * cellTripleVolume W
          = 7 * τ * (W 0).card * (W 1).card * (W 2).card := by rw [cellTripleVolume]; ring
      rw [heq1, heq2]
      exact hbound
  -- assemble
  rw [transversalInducedCount_eq_sum_refinement_of_profiled w.fine_le w.coarse_profile,
    fineInducedEstimate, ← hSdef]
  -- the volume charge and the three IsBadPair charges
  have hvol : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, cellTripleVolume W ≤ (s.card : ℝ) ^ 3 := by
    rw [hSdef]; exact sum_matching_refinement_volume_le_cube w.fine_le
  have hI01 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
      ≤ τ * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 0 1 (binaryPairPalette P 0 1) W), cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 0 1 (binaryPairPalette P 0 1) W), cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) τ p.1 p.2),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_zero_one_le
            (sel := fun _ p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) τ p.1 p.2)
      _ = badMassNum (HasBinaryPairPalette M (binaryPairPalette P 0 1)) τ w.fine * s.card := by
          rw [sum_refinement_isBadPair_mass_eq w.fine_le
            (HasBinaryPairPalette M (binaryPairPalette P 0 1))]
      _ ≤ τ * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right
            (badMassNum_le_of_isRegularPartition (HasBinaryPairPalette M (binaryPairPalette P 0 1)) τ
              (w.fine_regular (binaryPairPalette P 0 1)))
            (Nat.cast_nonneg _)
      _ = τ * (s.card : ℝ) ^ 3 := by ring
  have hI02 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
      ≤ τ * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 0 2 (binaryPairPalette P 0 2) W), cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 0 2 (binaryPairPalette P 0 2) W), cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) τ p.1 p.2),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_zero_two_le
            (sel := fun _ p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) τ p.1 p.2)
      _ = badMassNum (HasBinaryPairPalette M (binaryPairPalette P 0 2)) τ w.fine * s.card := by
          rw [sum_refinement_isBadPair_mass_eq w.fine_le
            (HasBinaryPairPalette M (binaryPairPalette P 0 2))]
      _ ≤ τ * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right
            (badMassNum_le_of_isRegularPartition (HasBinaryPairPalette M (binaryPairPalette P 0 2)) τ
              (w.fine_regular (binaryPairPalette P 0 2)))
            (Nat.cast_nonneg _)
      _ = τ * (s.card : ℝ) ^ 3 := by ring
  have hI12 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0)
      ≤ τ * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 1 2 (binaryPairPalette P 1 2) W), cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => bad 1 2 (binaryPairPalette P 1 2) W), cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) τ p.1 p.2),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_one_two_le
            (sel := fun _ p => IsBadPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) τ p.1 p.2)
      _ = badMassNum (HasBinaryPairPalette M (binaryPairPalette P 1 2)) τ w.fine * s.card := by
          rw [sum_refinement_isBadPair_mass_eq w.fine_le
            (HasBinaryPairPalette M (binaryPairPalette P 1 2))]
      _ ≤ τ * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right
            (badMassNum_le_of_isRegularPartition (HasBinaryPairPalette M (binaryPairPalette P 1 2)) τ
              (w.fine_regular (binaryPairPalette P 1 2)))
            (Nat.cast_nonneg _)
      _ = τ * (s.card : ℝ) ^ 3 := by ring
  calc |∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, (inducedEmbeddingCountOn P M W : ℝ)
          - ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
              requiredPaletteProduct P M W * cellTripleVolume W|
      = |∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          ((inducedEmbeddingCountOn P M W : ℝ) - requiredPaletteProduct P M W * cellTripleVolume W)| := by
        rw [← Finset.sum_sub_distrib]
        exact congrArg abs (Finset.sum_congr rfl fun _ _ => (Finset.sum_sub_distrib _ _).symm)
    _ ≤ ∑ T ∈ S, |∑ W ∈ refinementTriples w.fine T,
          ((inducedEmbeddingCountOn P M W : ℝ) - requiredPaletteProduct P M W * cellTripleVolume W)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          |(inducedEmbeddingCountOn P M W : ℝ) - requiredPaletteProduct P M W * cellTripleVolume W| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          (7 * τ * cellTripleVolume W
            + (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
            + (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
            + (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0)) :=
        Finset.sum_le_sum fun T hT => Finset.sum_le_sum fun W hW => hpw T hT W hW
    _ ≤ 10 * τ * (s.card : ℝ) ^ 3 := by
        have hsum : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
              (7 * τ * cellTripleVolume W
                + (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0)
                + (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0)
                + (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0))
            = (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 7 * τ * cellTripleVolume W)
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if bad 0 1 (binaryPairPalette P 0 1) W then cellTripleVolume W else 0))
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if bad 0 2 (binaryPairPalette P 0 2) W then cellTripleVolume W else 0))
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if bad 1 2 (binaryPairPalette P 1 2) W then cellTripleVolume W else 0)) := by
          simp only [Finset.sum_add_distrib]
        rw [hsum]
        have h7 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 7 * τ * cellTripleVolume W
            ≤ 7 * τ * (s.card : ℝ) ^ 3 := by
          have hmul : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 7 * τ * cellTripleVolume W
              = 7 * τ * ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, cellTripleVolume W := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
          rw [hmul]
          exact mul_le_mul_of_nonneg_left hvol (by positivity)
        linarith [h7, hI01, hI02, hI12]

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- **No sum over palette colors.** Unlike the palette *energy* and *regularity* layer — which
-- sums a quantity over all `BinaryPairPalette` colors — the strong count compares against
-- `fineInducedEstimate`, whose summand `requiredPaletteProduct` is definitionally the product
-- of exactly the three densities named by the pattern `P`: one required color per vertex pair,
-- never a sum over the palette index. The regularity charge is therefore `10·τ`, with no factor
-- counting the number of palette colors.
example {V : Type*} [DecidableEq V] {L : FirstOrder.Language} [FiniteRelational L]
    (M : FiniteRelModel L V) (P : FiniteRelModel L (Fin 3)) (T : Fin 3 → Finset V) :
    requiredPaletteProduct P M T
      = pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) :=
  rfl

-- **Repeated required palette colors.** Nothing forces the three required colors to be
-- distinct: if the pattern demands the same palette on pairs `(0,1)` and `(0,2)`, the
-- corresponding two density factors of `requiredPaletteProduct` coincide — the estimate still
-- has three factors, one per vertex pair.
example {V : Type*} [DecidableEq V] {L : FirstOrder.Language} [FiniteRelational L]
    (M : FiniteRelModel L V) (P : FiniteRelModel L (Fin 3)) (T : Fin 3 → Finset V)
    (h : binaryPairPalette P 0 1 = binaryPairPalette P 0 2) :
    requiredPaletteProduct P M T
      = pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 2)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) := by
  rw [requiredPaletteProduct, h]

-- **Empty host language.** For the relation-free language `Language.empty` there are no nullary
-- relations, so null-compatibility is automatic and the strong-count bound specializes to any
-- strong witness whose coarse error at the working scale is `≤ 1`.
example {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ}
    {M : FiniteRelModel FirstOrder.Language.empty V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀)
    (P : FiniteRelModel FirstOrder.Language.empty (Fin 3)) (hτ1 : E w.coarse.parts.card ≤ 1) :
    |(transversalInducedCount P M w.coarse : ℝ) - fineInducedEstimate P M w.fine w.coarse|
      ≤ 10 * E w.coarse.parts.card * (s.card : ℝ) ^ 3 :=
  w.abs_transversalInducedCount_sub_fineEstimate_le P (fun R => isEmptyElim R) hτ1

-- **Statement-level, two binary symbols.** For a language with two binary symbols
-- (`coloredRelLang 2 2`) the strong-count bound holds verbatim: the transversal induced count
-- is within `10·τ·|s|³` of the fine estimate for any strong witness at a working scale where
-- the coarse error is `≤ 1`.
example {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ}
    {M : FiniteRelModel (coloredRelLang 2 2) V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel (coloredRelLang 2 2) (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) :
    |(transversalInducedCount P M w.coarse : ℝ) - fineInducedEstimate P M w.fine w.coarse|
      ≤ 10 * E w.coarse.parts.card * (s.card : ℝ) ^ 3 :=
  w.abs_transversalInducedCount_sub_fineEstimate_le P hnull hτ1

end Tests

end RegularityLemmata
