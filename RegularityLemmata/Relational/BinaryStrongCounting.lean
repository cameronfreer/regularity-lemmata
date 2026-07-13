/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrongRegularityCharge

/-!
# Strong transversal counting: the density-shift charge and the summit

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), second half of the summit, built on the
common-index expansions and the regularity charge in `Relational/BinaryStrongRegularityCharge.lean`.

The **density-shift charge** compares the fine step estimate (`fineInducedEstimate`, using each
fine cell's own palette densities) with the coarse step estimate (`coarseInducedEstimate`, using
the coarse-parent densities): the two differ by at most `(3·η + 3·δ/η²)·|s|³`. The `3·η` comes from
the three-factor perturbation bound `abs_mul_mul_sub_mul_mul_le` on boxes whose fine and coarse
densities agree to within `η` on all three pairs; the `3·δ/η²` charges the deviant boxes through
the nested selected-pair lifting and the witness's `deviant_mass_le`. Deviance is `η < |…|`, so
equality at `η` belongs to the good case.

The **summit** `abs_transversalInducedCount_sub_coarseInducedEstimate_le` then adds the two named
charges through the triangle inequality: the actual transversal induced count is within
`(10·τ + 3·η + 3·δ/η²)·|s|³` of the coarse step estimate.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {s : Finset V}

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L]

omit [DecidableEq V] in
/-- Pair densities lie in `[0,1]`, so their absolute value is at most one. -/
private theorem pairDensity_abs_le_one {R : V → V → Prop} [DecidableRel R] (A B : Finset V) :
    |pairDensity R A B| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num) pairDensity_nonneg, pairDensity_le_one⟩

/-! ### The density-shift charge -/

/-- **The density-shift charge.** The fine step estimate is within `(3·η + 3·δ/η²)·|s|³` of the
coarse step estimate: `3·η` from the three-factor perturbation on boxes whose fine and coarse
palette densities agree to within `η`, and `3·δ/η²` from the three deviant-mass liftings. -/
theorem BinaryPaletteStrongWitness.abs_fineInducedEstimate_sub_coarseInducedEstimate_le
    {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel L (Fin 3))
    {η : ℝ} (hη : 0 < η) :
    |fineInducedEstimate P M w.fine w.coarse - coarseInducedEstimate P M w.coarse|
      ≤ (3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 := by
  set S := (transversalCellTriples w.coarse).filter (MatchesThreeProfiles P M) with hSdef
  have hvol : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, cellTripleVolume W ≤ (s.card : ℝ) ^ 3 := by
    rw [hSdef]; exact sum_matching_refinement_volume_le_cube w.fine_le
  -- pointwise density-shift bound
  have hpw : ∀ T ∈ S, ∀ W ∈ refinementTriples w.fine T,
      |requiredPaletteProduct P M W * cellTripleVolume W
          - requiredPaletteProduct P M T * cellTripleVolume W|
        ≤ 3 * η * cellTripleVolume W
          + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
              then cellTripleVolume W else 0)
          + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
              then cellTripleVolume W else 0)
          + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
              then cellTripleVolume W else 0) := by
    intro T _ W _
    have hvolnn : 0 ≤ cellTripleVolume W := cellTripleVolume_nonneg W
    have hi01 : 0 ≤ (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
        then cellTripleVolume W else 0) := by split_ifs <;> [exact hvolnn; exact le_rfl]
    have hi02 : 0 ≤ (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
        then cellTripleVolume W else 0) := by split_ifs <;> [exact hvolnn; exact le_rfl]
    have hi12 : 0 ≤ (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
        then cellTripleVolume W else 0) := by split_ifs <;> [exact hvolnn; exact le_rfl]
    have hfactor : requiredPaletteProduct P M W * cellTripleVolume W
        - requiredPaletteProduct P M T * cellTripleVolume W
        = (requiredPaletteProduct P M W - requiredPaletteProduct P M T) * cellTripleVolume W := by
      ring
    rw [hfactor, abs_mul, abs_of_nonneg hvolnn]
    by_cases hd : (η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
          - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|)
        ∨ (η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
          - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|)
        ∨ (η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
          - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|)
    · -- some pair is deviant: the crude `[0,1]` product bound suffices
      have h1W : requiredPaletteProduct P M W ≤ 1 := requiredPaletteProduct_le_one P M W
      have h0W : 0 ≤ requiredPaletteProduct P M W := requiredPaletteProduct_nonneg P M W
      have h1T : requiredPaletteProduct P M T ≤ 1 := requiredPaletteProduct_le_one P M T
      have h0T : 0 ≤ requiredPaletteProduct P M T := requiredPaletteProduct_nonneg P M T
      have habs1 : |requiredPaletteProduct P M W - requiredPaletteProduct P M T| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hge : cellTripleVolume W
          ≤ (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
              then cellTripleVolume W else 0)
            + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
              then cellTripleVolume W else 0)
            + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
              then cellTripleVolume W else 0) := by
        rcases hd with h | h | h
        · rw [if_pos h]; linarith
        · rw [if_pos h]; linarith
        · rw [if_pos h]; linarith
      linarith [mul_le_mul_of_nonneg_right habs1 hvolnn, hge,
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hη.le) hvolnn]
    · -- no pair deviant: the three-factor perturbation gives `3η`
      rw [not_or, not_or] at hd
      obtain ⟨hn01, hn02, hn12⟩ := hd
      rw [if_neg hn01, if_neg hn02, if_neg hn12, add_zero, add_zero, add_zero]
      have hbound : |requiredPaletteProduct P M W - requiredPaletteProduct P M T| ≤ 3 * η := by
        simp only [requiredPaletteProduct]
        refine le_trans (abs_mul_mul_sub_mul_mul_le (pairDensity_abs_le_one _ _)
          (pairDensity_abs_le_one _ _) (pairDensity_abs_le_one _ _) (pairDensity_abs_le_one _ _)) ?_
        linarith [not_lt.mp hn01, not_lt.mp hn02, not_lt.mp hn12]
      exact mul_le_mul_of_nonneg_right hbound hvolnn
  -- the three deviance charges, each ≤ δ/η²·|s|³
  have hD01 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
            - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
          then cellTripleVolume W else 0)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
              then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|),
            cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|),
            cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) p.1 p.2
                    - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) pd.1 pd.2|),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_zero_one_le
            (sel := fun pd p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) p.1 p.2
              - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) pd.1 pd.2|)
      _ ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right (w.deviant_mass_le (binaryPairPalette P 0 1) hη)
            (Nat.cast_nonneg _)
      _ = δ / η ^ 2 * (s.card : ℝ) ^ 3 := by ring
  have hD02 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
            - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
          then cellTripleVolume W else 0)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
              then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|),
            cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|),
            cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) p.1 p.2
                    - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) pd.1 pd.2|),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_zero_two_le
            (sel := fun pd p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) p.1 p.2
              - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) pd.1 pd.2|)
      _ ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right (w.deviant_mass_le (binaryPairPalette P 0 2) hη)
            (Nat.cast_nonneg _)
      _ = δ / η ^ 2 * (s.card : ℝ) ^ 3 := by ring
  have hD12 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
        (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
            - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
          then cellTripleVolume W else 0)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 3 :=
    calc ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
            (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
              then cellTripleVolume W else 0)
        = ∑ T ∈ S, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|),
            cellTripleVolume W :=
          Finset.sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ T ∈ transversalCellTriples w.coarse, ∑ W ∈ (refinementTriples w.fine T).filter
              (fun W => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|),
            cellTripleVolume W := by
          rw [hSdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun T _ _ => Finset.sum_nonneg fun W _ => cellTripleVolume_nonneg W
      _ ≤ (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
              ∑ p ∈ (refinementFiber w.fine pd.1 ×ˢ refinementFiber w.fine pd.2).filter
                  (fun p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) p.1 p.2
                    - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) pd.1 pd.2|),
                ((p.1.card : ℝ) * p.2.card)) * s.card :=
          selectedRefinementPairTripleMass_one_two_le
            (sel := fun pd p => η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) p.1 p.2
              - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) pd.1 pd.2|)
      _ ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 * s.card :=
          mul_le_mul_of_nonneg_right (w.deviant_mass_le (binaryPairPalette P 1 2) hη)
            (Nat.cast_nonneg _)
      _ = δ / η ^ 2 * (s.card : ℝ) ^ 3 := by ring
  -- assemble
  rw [fineInducedEstimate, coarseInducedEstimate_eq_sum_refinement w.fine_le, ← hSdef]
  calc |∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, requiredPaletteProduct P M W * cellTripleVolume W
          - ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, requiredPaletteProduct P M T * cellTripleVolume W|
      = |∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          (requiredPaletteProduct P M W * cellTripleVolume W
            - requiredPaletteProduct P M T * cellTripleVolume W)| := by
        rw [← Finset.sum_sub_distrib]
        exact congrArg abs (Finset.sum_congr rfl fun _ _ => (Finset.sum_sub_distrib _ _).symm)
    _ ≤ ∑ T ∈ S, |∑ W ∈ refinementTriples w.fine T,
          (requiredPaletteProduct P M W * cellTripleVolume W
            - requiredPaletteProduct P M T * cellTripleVolume W)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          |requiredPaletteProduct P M W * cellTripleVolume W
            - requiredPaletteProduct P M T * cellTripleVolume W| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
          (3 * η * cellTripleVolume W
            + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                  - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
                then cellTripleVolume W else 0)
            + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                  - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
                then cellTripleVolume W else 0)
            + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                  - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
                then cellTripleVolume W else 0)) :=
        Finset.sum_le_sum fun T hT => Finset.sum_le_sum fun W hW => hpw T hT W hW
    _ ≤ (3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 := by
        have hsum : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
              (3 * η * cellTripleVolume W
                + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
                    then cellTripleVolume W else 0)
                + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
                    then cellTripleVolume W else 0)
                + (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
                    then cellTripleVolume W else 0))
            = (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 3 * η * cellTripleVolume W)
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (W 0) (W 1)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)|
                    then cellTripleVolume W else 0))
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (W 0) (W 2)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)|
                    then cellTripleVolume W else 0))
              + (∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T,
                  (if η < |pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (W 1) (W 2)
                      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)|
                    then cellTripleVolume W else 0)) := by
          simp only [Finset.sum_add_distrib]
        rw [hsum]
        have h3 : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 3 * η * cellTripleVolume W
            ≤ 3 * η * (s.card : ℝ) ^ 3 := by
          have hmul : ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, 3 * η * cellTripleVolume W
              = 3 * η * ∑ T ∈ S, ∑ W ∈ refinementTriples w.fine T, cellTripleVolume W := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
          rw [hmul]
          exact mul_le_mul_of_nonneg_left hvol (by positivity)
        have htarget : (3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
            = 3 * η * (s.card : ℝ) ^ 3
              + (δ / η ^ 2 * (s.card : ℝ) ^ 3 + δ / η ^ 2 * (s.card : ℝ) ^ 3
                + δ / η ^ 2 * (s.card : ℝ) ^ 3) := by ring
        rw [htarget]
        linarith [h3, hD01, hD02, hD12]

/-! ### The summit -/

/-- **Strong three-vertex counting.** For a binary-palette strong witness, the actual number of
induced pattern embeddings landing in distinct coarse cells is within
`(10·τ + 3·η + 3·δ/η²)·|s|³` of the coarse step estimate, where `τ = E w.coarse.parts.card`. The
bound is the triangle-inequality sum of the regularity charge (`10·τ`) and the density-shift
charge (`3·η + 3·δ/η²`). -/
theorem BinaryPaletteStrongWitness.abs_transversalInducedCount_sub_coarseInducedEstimate_le
    [AtMostBinary L] {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 := by
  have h1 := w.abs_transversalInducedCount_sub_fineEstimate_le P hnull hτ1
  have h2 := w.abs_fineInducedEstimate_sub_coarseInducedEstimate_le P hη
  calc |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ |(transversalInducedCount P M w.coarse : ℝ) - fineInducedEstimate P M w.fine w.coarse|
          + |fineInducedEstimate P M w.fine w.coarse - coarseInducedEstimate P M w.coarse| :=
        abs_sub_le _ _ _
    _ ≤ 10 * E w.coarse.parts.card * (s.card : ℝ) ^ 3
          + (3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 := add_le_add h1 h2
    _ = (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 := by ring

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- **No palette-cardinality factor.** The summit error carries exactly three `η` charges and
-- three `δ/η²` charges — one per vertex pair `(0,1)`, `(0,2)`, `(1,2)` — never a factor counting
-- the number of `BinaryPairPalette` colors. Repeating a required color (below) does not merge two
-- coordinate charges into one.

-- **Equality at `η` is not deviant.** Deviance is the strict `η < |…|`; a box whose fine and
-- coarse densities differ by exactly `η` belongs to the good (perturbation) case.
example {d d' η : ℝ} (h : |d - d'| = η) : ¬ η < |d - d'| := by rw [h]; exact lt_irrefl η

-- **Empty host language.** For the relation-free language the summit specializes: no nullary
-- relations, so null-compatibility is automatic.
example {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ}
    {M : FiniteRelModel FirstOrder.Language.empty V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀)
    (P : FiniteRelModel FirstOrder.Language.empty (Fin 3)) (hτ1 : E w.coarse.parts.card ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 :=
  w.abs_transversalInducedCount_sub_coarseInducedEstimate_le P (fun R => isEmptyElim R) hτ1 hη

-- **Statement-level, two binary symbols.** For `coloredRelLang 2 2` the summit holds verbatim.
example {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ}
    {M : FiniteRelModel (coloredRelLang 2 2) V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel (coloredRelLang 2 2) (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 :=
  w.abs_transversalInducedCount_sub_coarseInducedEstimate_le P hnull hτ1 hη

-- **Repeated required palette colors, three charges intact.** Even when the pattern demands the
-- same palette on pairs `(0,1)` and `(0,2)`, the summit bound is unchanged — the three `η` and
-- three `δ/η²` charges are indexed by vertex pair, not by distinct color, so a coincidence of
-- required colors incurs no reduction.
example {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ}
    {M : FiniteRelModel (coloredRelLang 2 2) V} {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (P : FiniteRelModel (coloredRelLang 2 2) (Fin 3))
    (hnull : NullaryCompatible P M) (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η)
    (_hrep : binaryPairPalette P 0 1 = binaryPairPalette P 0 2) :
    |(transversalInducedCount P M w.coarse : ℝ) - coarseInducedEstimate P M w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3 :=
  w.abs_transversalInducedCount_sub_coarseInducedEstimate_le P hnull hτ1 hη

end Tests

end RegularityLemmata
