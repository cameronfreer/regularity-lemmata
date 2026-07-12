/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrong
import RegularityLemmata.Relational.ThreeVertexCounting

/-!
# Transversal induced-count substrate

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), substrate layer: the definitions and
mass identities for comparing the actual number of induced three-vertex pattern embeddings
whose three images lie in **distinct** coarse cells against the step-model estimate from the
three required coarse palette densities.

`transversalCellTriples Q` enumerates the ordered triples of *distinct* cells of a partition
`Q` (injectivity of `Fin 3 → Q.parts`); partition disjointness then supplies the box
disjointness that the exact three-vertex bridge (`inducedEmbeddingCountOn_three`) needs.
`transversalInducedCount` sums the induced count over these boxes; `coarseInducedEstimate`
is the real-valued step estimate, restricted (via `MatchesThreeProfiles`) to triples whose
cells carry the pattern's required vertex profiles — a cell may have a well-defined palette
density yet the wrong unary/loop profile for a coordinate.

The mass identity `sum_transversal_volume_le` bounds the total box volume by `|s|³`, the
normalization for the error terms in the strong-counting theorem.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- Ordered triples of **distinct** cells of `Q` (the box disjointness for transversal
induced counting comes from partition disjointness of distinct cells). -/
def transversalCellTriples (Q : Finpartition s) : Finset (Fin 3 → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter Function.Injective

/-- The three cells of a transversal triple carry the pattern's required vertex profiles. -/
def MatchesThreeProfiles (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (T : Fin 3 → Finset V) : Prop :=
  ∀ i, ∀ v ∈ T i, binaryVertexProfile M v = binaryVertexProfile P i

instance (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V) :
    DecidablePred (MatchesThreeProfiles P M) :=
  fun T => inferInstanceAs
    (Decidable (∀ i, ∀ v ∈ T i, binaryVertexProfile M v = binaryVertexProfile P i))

/-- The actual number of induced pattern embeddings whose images lie in distinct cells. -/
def transversalInducedCount (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℕ :=
  ∑ T ∈ transversalCellTriples Q, inducedEmbeddingCountOn P M T

/-- The coarse step-model estimate: the product of the three required palette densities
times the box volume, over profile-matching transversal triples. -/
noncomputable def coarseInducedEstimate (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℝ :=
  ∑ T ∈ (transversalCellTriples Q).filter (MatchesThreeProfiles P M),
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1) *
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2) *
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) *
      (T 0).card * (T 1).card * (T 2).card

/-! ### Mass identities -/

/-- **Total transversal box volume is at most `|s|³`.** -/
theorem sum_transversal_volume_le (Q : Finpartition s) :
    ∑ T ∈ transversalCellTriples Q, ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ (s.card : ℝ) ^ 3 := by
  have hsub : transversalCellTriples Q ⊆ Fintype.piFinset fun _ => Q.parts :=
    Finset.filter_subset _ _
  calc ∑ T ∈ transversalCellTriples Q, ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ Fintype.piFinset fun _ => Q.parts, ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ T ∈ Fintype.piFinset fun _ => Q.parts, ∏ i, ((T i).card : ℝ) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Fin.prod_univ_three]
    _ = ∏ _i : Fin 3, ∑ A ∈ Q.parts, (A.card : ℝ) :=
        Finset.sum_prod_piFinset Q.parts fun _ A => (A.card : ℝ)
    _ = (s.card : ℝ) ^ 3 := by
        rw [sum_card_parts_cast Q, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Tests and adversarial examples -/

section Tests

-- Empty host: no cells, so the transversal triples are empty and both counts vanish.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3))
    (M : FiniteRelModel (singleRelLang 2) (Fin 2)) :
    transversalInducedCount P M (⊥ : Finpartition (∅ : Finset (Fin 2))) = 0 := by
  rw [transversalInducedCount, transversalCellTriples]
  simp

end Tests

end RegularityLemmata
