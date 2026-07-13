/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.StrongCountingLifting

/-!
# Strong transversal induced counting

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), the summit: comparing the actual number
of induced three-vertex pattern embeddings whose images lie in distinct coarse cells
(`transversalInducedCount`) against the coarse step estimate (`coarseInducedEstimate`) for a
`BinaryPaletteStrongWitness`, with a `10·τ + 3·η + 3·δ/η²` error bound.

Assembled on the nested selected-pair lifting in `Relational/StrongCountingLifting.lean`: the
common-index expansions align the actual and coarse sums over one fine index, and the final
approximation is proved through two named intermediate error bounds — a regularity charge
(`10·τ`, via the exact three-vertex count on uniform fine triples and `IsBadPair` lifting on
nonuniform ones) and a density-shift charge (`3·η + 3·δ/η²`, via three-factor perturbation and
the witness's deviant-mass bound).
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

end RegularityLemmata
