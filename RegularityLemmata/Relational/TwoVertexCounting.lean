/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPattern
import RegularityLemmata.Finite.PairDensity

/-!
# Exact two-vertex palette counting

Phase 10 unit 2 (design freeze in `ARCHITECTURE.md`): the base case, checking that the
two-way palette really captures induced binary structure. For a two-vertex pattern
`P` and disjoint profile-matching host cells `A`, `B`, the induced embedding count is
**exactly** the palette pair count of the pattern's required color
(`inducedEmbeddingCountOn_two`).
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}
  [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- On a profile-matching pair of vertices, preservation-and-reflection reduces to
carrying the pattern's required palette color. -/
theorem preservesAndReflects_two_iff [AtMostBinary L]
    {P : FiniteRelModel L (Fin 2)} {M : FiniteRelModel L V}
    (hnull : NullaryCompatible P M) {f : Fin 2 → V}
    (h0 : binaryVertexProfile M (f 0) = binaryVertexProfile P 0)
    (h1 : binaryVertexProfile M (f 1) = binaryVertexProfile P 1) :
    PreservesAndReflects P M f
      ↔ HasBinaryPairPalette M (binaryPairPalette P 0 1) (f 0) (f 1) := by
  rw [preservesAndReflects_iff_profiles_palettes]
  constructor
  · rintro ⟨_, _, hpal⟩
    exact (hpal 0 1 (by decide)).symm
  · intro hHas
    refine ⟨hnull, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hHas.symm
      · show binaryPairPalette P 1 0 = binaryPairPalette M (f 1) (f 0)
        rw [binaryPairPalette_swap P 0 1, binaryPairPalette_swap M (f 0) (f 1), hHas]
      · exact absurd rfl hij

omit [Fintype V] in
/-- **Exact two-vertex count.** The induced count over disjoint profile-matching cells
equals the palette pair count of the pattern's required color. -/
theorem inducedEmbeddingCountOn_two [AtMostBinary L]
    {P : FiniteRelModel L (Fin 2)} {M : FiniteRelModel L V} {A B : Finset V}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hdisj : Disjoint A B) :
    inducedEmbeddingCountOn P M ![A, B]
      = pairCount (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B := by
  classical
  rw [inducedEmbeddingCountOn_of_disjoint P M (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (show Disjoint (![A, B] 0) (![A, B] 1); exact hdisj)
      | (show Disjoint (![A, B] 1) (![A, B] 0); exact hdisj.symm))]
  rw [pairCount]
  refine Finset.card_bij' (fun f _ => (f 0, f 1)) (fun p _ => ![p.1, p.2])
    (fun f hf => ?_) (fun p hp => ?_) (fun f _ => by funext i; fin_cases i <;> rfl)
    (fun p _ => rfl)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    have hf0 : f 0 ∈ A := hf.1 0
    have hf1 : f 1 ∈ B := hf.1 1
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hf0, hf1⟩,
      (preservesAndReflects_two_iff hnull (hA _ hf0) (hB _ hf1)).mp hf.2⟩
  · rw [Finset.mem_filter, Finset.mem_product] at hp
    have hp1 : p.1 ∈ A := hp.1.1
    have hp2 : p.2 ∈ B := hp.1.2
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact hp1
      · exact hp2
    · refine (preservesAndReflects_two_iff hnull ?_ ?_).mpr ?_
      · exact hA _ hp1
      · exact hB _ hp2
      · exact hp.2

omit [Fintype V] in
/-- The density form. -/
theorem inducedEmbeddingDensityOn_two [AtMostBinary L]
    {P : FiniteRelModel L (Fin 2)} {M : FiniteRelModel L V} {A B : Finset V}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hdisj : Disjoint A B) :
    (inducedEmbeddingCountOn P M ![A, B] : ℝ)
      = pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B
          * (A.card * B.card) := by
  rw [inducedEmbeddingCountOn_two hnull hA hB hdisj, pairCount_eq_pairDensity_mul]

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level: the two-vertex count is a palette pair count.
example (P : FiniteRelModel (singleRelLang 2) (Fin 2))
    (M : FiniteRelModel (singleRelLang 2) (Fin 5)) (A B : Finset (Fin 5))
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hdisj : Disjoint A B) :
    inducedEmbeddingCountOn P M ![A, B]
      = pairCount (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B :=
  inducedEmbeddingCountOn_two hnull hA hB hdisj

end Tests

end RegularityLemmata
