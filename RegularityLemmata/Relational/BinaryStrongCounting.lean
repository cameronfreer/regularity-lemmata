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

end RegularityLemmata
