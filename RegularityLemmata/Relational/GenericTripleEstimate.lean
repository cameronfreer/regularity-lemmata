/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.WeakenedCountingGate

/-!
# Route (b) ladder step 2: the generic triple estimate

`ARCHITECTURE.md` route (b) ladder step 2. The weakened-counting gate produced the two inputs
the count needs: a `7 * ε` estimate on triples all of whose coordinate pairs are uniform, and
a crude volume bound on the rest. This file combines them, **generically in a bad-pair set
`D`** — no proxy, no palette-union, no selection appears.

**This is the estimate, not step 5.** No selection is performed and no summit is assembled.

## The statement

`abs_transversalInducedCount_sub_coarseInducedEstimate_le` : if the pairs failing any of the
three required palette-uniformity conditions all lie in `D`, and `D` carries pair mass at
most `β * #s ^ 2`, then

`|transversalInducedCount - coarseInducedEstimate| ≤ (7 * ε + 3 * β) * #s ^ 3`.

## Which hypothesis does which job

The four ingredients stay separate, and each is used exactly once:

* **`D` covers uniformity failures** (`hD01`, `hD02`, `hD12`) — one per coordinate pair, at
  that pair's own palette. This is all `D` is asked to do.
* **Profile matching** comes from the triple lying in `MatchesThreeProfiles`, which is where
  `coarseInducedEstimate` already sums; non-matching triples contribute nothing to either
  side (`transversalInducedCount_eq_sum_matching`, generic profile-elimination infrastructure
  living with the rest of the counting substrate). It is NOT read off `D`.
* **Transversality** supplies pairwise disjointness (`transversalCellTriples_disjoint`).
* **Good triples** consume `abs_inducedEmbeddingCountOn_three_sub_le` — the `7 * ε` estimate.
* **Bad triples** consume only the crude bound: both the count and the density product lie in
  `[0, volume]`, so their difference is at most the volume in absolute value, and
  `badTripleVolume_le` sums those volumes to `3 * β * #s ^ 3`. No density estimate is used on
  a bad triple.

## Not done here

Specializing `D` to `selectedPaletteNonuniformPairs` and combining with the deviation charge.
That is the next step; **step 5 stays closed**.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] [AtMostBinary L]
  {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}

/-! ### The crude bound on a single triple -/

omit [AtMostBinary L] in
/-- On ANY triple both the count and the density product lie in `[0, volume]`, so their
difference is at most the volume. This is the only estimate a bad triple receives. -/
theorem abs_count_sub_densityProduct_le_volume (T : Fin 3 → Finset V) :
    |(inducedEmbeddingCountOn P M T : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
            * (T 0).card * (T 1).card * (T 2).card|
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
  have hcount0 : (0 : ℝ) ≤ (inducedEmbeddingCountOn P M T : ℝ) := by positivity
  have hcountv : (inducedEmbeddingCountOn P M T : ℝ)
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
    inducedEmbeddingCountOn_le_cellTripleVolume P M T
  have hd : pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ pairDensity_le_one pairDensity_nonneg pairDensity_le_one)
      pairDensity_nonneg pairDensity_le_one
  have hd0 : (0 : ℝ) ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) :=
    mul_nonneg (mul_nonneg pairDensity_nonneg pairDensity_nonneg) pairDensity_nonneg
  have hv : (0 : ℝ) ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith [hcount0, hcountv, hd, hd0, hv]

/-! ### The generic estimate -/

open Classical in
/-- **The generic triple estimate.** With `D` covering every failure of the three required
palette-uniformity conditions and carrying pair mass at most `β * #s ^ 2`, the transversal
induced count differs from the coarse density estimate by at most `(7 * ε + 3 * β) * #s ^ 3`.
Generic in `D`: no proxy, palette-union or selection appears. -/
theorem abs_transversalInducedCount_sub_coarseInducedEstimate_le
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε → (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε → (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε → (A, B) ∈ D) :
    |(transversalInducedCount P M Q : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 := by
  classical
  set S := (transversalCellTriples Q).filter (MatchesThreeProfiles P M) with hS
  set bad : (Fin 3 → Finset V) → Prop := fun T =>
    (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D with hbad
  set f : (Fin 3 → Finset V) → ℝ := fun T =>
    (inducedEmbeddingCountOn P M T : ℝ)
      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
          * (T 0).card * (T 1).card * (T 2).card with hf
  have hdiff : (transversalInducedCount P M Q : ℝ) - coarseInducedEstimate P M Q
      = ∑ T ∈ S, f T := by
    rw [transversalInducedCount_eq_sum_matching hQ, coarseInducedEstimate, hS, hf,
      ← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← Finset.sum_filter_add_sum_filter_not S bad (fun T => |f T|)]
  have hs3 : (0 : ℝ) ≤ (s.card : ℝ) ^ 3 := by positivity
  -- Bad triples: the crude volume bound only.
  have hbadsum : ∑ T ∈ S.filter bad, |f T| ≤ 3 * β * (s.card : ℝ) ^ 3 := by
    refine le_trans (Finset.sum_le_sum fun T _ => abs_count_sub_densityProduct_le_volume T) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
      (fun T _ _ => by positivity)) (badTripleVolume_le hD hmass)
    rw [Finset.mem_filter] at hT ⊢
    rw [hS, Finset.mem_filter] at hT
    exact ⟨hT.1.1, hT.2⟩
  -- Good triples: the `7 * ε` estimate.
  have hgoodsum : ∑ T ∈ S.filter (fun T => ¬ bad T), |f T| ≤ 7 * ε * (s.card : ℝ) ^ 3 := by
    have hstep : ∀ T ∈ S.filter (fun T => ¬ bad T),
        |f T| ≤ 7 * ε * ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
      intro T hT
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hT
      obtain ⟨⟨hTtrans, hTmatch⟩, hTgood⟩ := hT
      rw [hbad] at hTgood
      push Not at hTgood
      have hmem : ∀ i, T i ∈ Q.parts := transversalCellTriples_cell_mem hTtrans
      have heta : ![T 0, T 1, T 2] = T := by funext i; fin_cases i <;> rfl
      have h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1))
          (T 0) (T 1) ε := by
        by_contra hcon
        exact hTgood.1 (hD01 _ (hmem 0) _ (hmem 1) hcon)
      have h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2))
          (T 0) (T 2) ε := by
        by_contra hcon
        exact hTgood.2.1 (hD02 _ (hmem 0) _ (hmem 2) hcon)
      have h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2))
          (T 1) (T 2) ε := by
        by_contra hcon
        exact hTgood.2.2 (hD12 _ (hmem 1) _ (hmem 2) hcon)
      have hmain := abs_inducedEmbeddingCountOn_three_sub_le (A := T 0) (B := T 1) (C := T 2)
        hnull (hTmatch 0) (hTmatch 1) (hTmatch 2)
        (transversalCellTriples_disjoint hTtrans (by decide : (0 : Fin 3) ≠ 1))
        (transversalCellTriples_disjoint hTtrans (by decide : (0 : Fin 3) ≠ 2))
        (transversalCellTriples_disjoint hTtrans (by decide : (1 : Fin 3) ≠ 2))
        hε0 hε1 h01 h02 h12
      rw [heta] at hmain
      simp only [hf]
      linarith [hmain]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hvol : ∑ T ∈ S.filter (fun T => ¬ bad T),
        ((T 0).card * (T 1).card * (T 2).card : ℝ) ≤ (s.card : ℝ) ^ 3 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
        (fun T _ _ => by positivity)) (sum_transversal_volume_le Q)
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hT
      exact hT.1.1
    nlinarith [hvol, hε0]
  linarith [hbadsum, hgoodsum]

/-! ### Tests -/

section Tests

-- The crude bound holds on every triple, with no uniformity hypothesis at all — which is
-- what makes it the right estimate for a bad triple.
example (T : Fin 3 → Finset V) :
    |(inducedEmbeddingCountOn P M T : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
            * (T 0).card * (T 1).card * (T 2).card|
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
  abs_count_sub_densityProduct_le_volume T

-- With an empty bad-pair set the estimate degenerates to the pure `7 * ε` bound: `β = 0`
-- contributes nothing, so the two error sources really are separate.
example (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε)
    (hu02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε)
    (hu12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε) :
    |(transversalInducedCount P M Q : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * 0) * (s.card : ℝ) ^ 3 :=
  abs_transversalInducedCount_sub_coarseInducedEstimate_le hQ hnull
    (D := ∅) (Finset.empty_subset _) hε0 hε1 (by simp)
    (fun A hA B hB h => absurd (hu01 A hA B hB) h)
    (fun A hA B hB h => absurd (hu02 A hA B hB) h)
    (fun A hA B hB h => absurd (hu12 A hA B hB) h)

end Tests

end RegularityLemmata
