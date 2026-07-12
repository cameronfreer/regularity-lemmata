/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPattern
import RegularityLemmata.Graph.PathCounting
import RegularityLemmata.Graph.TriangleCounting

/-!
# Induced three-vertex relational counting

Phase 10 unit 6 (design freeze in `ARCHITECTURE.md`): lifting the directed graph path and
triangle counts (Units 4–5) to induced relational patterns via the palette machinery.

The palette wrappers (`abs_binaryPalettePathDensity_sub_le`,
`abs_binaryPaletteTriangleCount_sub_le`) make the colored path/triangle deliverable visible
in the relational namespace — palette-color relations `HasBinaryPairPalette M c` are just
`DecidableRel` relations, so these are direct wrappers, not new proofs.

The logical core is `preservesAndReflects_three_iff`: under nullary compatibility and
vertex-profile matching, an induced embedding of a three-vertex pattern `P` is exactly a
directed triangle in the three **forward** palette-color relations
`binaryPairPalette P {01, 02, 12}` (each palette already carries both orientations, so
`binaryPairPalette_swap` handles the reverse pairs; injectivity is not needed). The exact
box-count bridge `inducedEmbeddingCountOn_three` is then a filter congruence — both sides
count functions in the same `piFinset` — and `abs_inducedEmbeddingCountOn_three_sub_le`
combines it with the `7·ε` triangle bound.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]

/-! ### Palette path and triangle wrappers -/

/-- The colored directed-path deliverable: two palette colors feed the `6·ε` path bound. -/
theorem abs_binaryPalettePathDensity_sub_le (M : FiniteRelModel L V)
    (c₀₁ c₁₂ : BinaryPairPalette L) {A B C : Finset V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M c₀₁) A B ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M c₁₂) B C ε) :
    |directedPathDensity (HasBinaryPairPalette M c₀₁) (HasBinaryPairPalette M c₁₂) A B C
        - pairDensity (HasBinaryPairPalette M c₀₁) A B
            * pairDensity (HasBinaryPairPalette M c₁₂) B C| ≤ 6 * ε :=
  abs_directedPathDensity_sub_le _ _ hε0 hε1 h01 h12

/-- The colored directed-triangle deliverable: three palette colors feed the `7·ε` bound. -/
theorem abs_binaryPaletteTriangleCount_sub_le (M : FiniteRelModel L V)
    (c₀₁ c₀₂ c₁₂ : BinaryPairPalette L) {A B C : Finset V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M c₀₁) A B ε)
    (h02 : IsUniformPair (HasBinaryPairPalette M c₀₂) A C ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M c₁₂) B C ε) :
    |(directedTriangleCount (HasBinaryPairPalette M c₀₁) (HasBinaryPairPalette M c₀₂)
          (HasBinaryPairPalette M c₁₂) A B C : ℝ)
        - pairDensity (HasBinaryPairPalette M c₀₁) A B
            * pairDensity (HasBinaryPairPalette M c₀₂) A C
            * pairDensity (HasBinaryPairPalette M c₁₂) B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card :=
  abs_directedTriangleCount_sub_le _ _ _ hε0 hε1 h01 h02 h12

/-! ### The three-vertex logical reduction -/

omit [DecidableEq V] in
/-- **The three-vertex reduction.** Under profile matching, an induced embedding of a
three-vertex pattern is exactly a directed triangle in the three forward palette colors.
Injectivity is not needed. -/
theorem preservesAndReflects_three_iff [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (hnull : NullaryCompatible P M) {f : Fin 3 → V}
    (h0 : binaryVertexProfile M (f 0) = binaryVertexProfile P 0)
    (h1 : binaryVertexProfile M (f 1) = binaryVertexProfile P 1)
    (h2 : binaryVertexProfile M (f 2) = binaryVertexProfile P 2) :
    PreservesAndReflects P M f ↔
      directedTriangleObs
        (HasBinaryPairPalette M (binaryPairPalette P 0 1))
        (HasBinaryPairPalette M (binaryPairPalette P 0 2))
        (HasBinaryPairPalette M (binaryPairPalette P 1 2)) f := by
  rw [preservesAndReflects_iff_profiles_palettes, directedTriangleObs]
  constructor
  · rintro ⟨_, _, hpal⟩
    exact ⟨(hpal 0 1 (by decide)).symm, (hpal 0 2 (by decide)).symm, (hpal 1 2 (by decide)).symm⟩
  · rintro ⟨hp01, hp02, hp12⟩
    refine ⟨hnull, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hp01.symm
      · exact hp02.symm
      · show binaryPairPalette P 1 0 = binaryPairPalette M (f 1) (f 0)
        rw [binaryPairPalette_swap P 0 1, binaryPairPalette_swap M (f 0) (f 1), hp01]
      · exact absurd rfl hij
      · exact hp12.symm
      · show binaryPairPalette P 2 0 = binaryPairPalette M (f 2) (f 0)
        rw [binaryPairPalette_swap P 0 2, binaryPairPalette_swap M (f 0) (f 2), hp02]
      · show binaryPairPalette P 2 1 = binaryPairPalette M (f 2) (f 1)
        rw [binaryPairPalette_swap P 1 2, binaryPairPalette_swap M (f 1) (f 2), hp12]
      · exact absurd rfl hij

/-! ### The exact box-count bridge -/

/-- **Exact three-vertex count.** On disjoint profile-matching cells, the induced count
equals the directed triangle count of the three required palette colors. -/
theorem inducedEmbeddingCountOn_three [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A B C : Finset V}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    inducedEmbeddingCountOn P M ![A, B, C]
      = directedTriangleCount
          (HasBinaryPairPalette M (binaryPairPalette P 0 1))
          (HasBinaryPairPalette M (binaryPairPalette P 0 2))
          (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B C := by
  rw [inducedEmbeddingCountOn_of_disjoint P M (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (show Disjoint A B; exact hAB)
      | (show Disjoint A C; exact hAC)
      | (show Disjoint B A; exact hAB.symm)
      | (show Disjoint B C; exact hBC)
      | (show Disjoint C A; exact hAC.symm)
      | (show Disjoint C B; exact hBC.symm)),
    directedTriangleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f hf => ?_)
  rw [Fintype.mem_piFinset] at hf
  exact preservesAndReflects_three_iff hnull (hA _ (hf 0)) (hB _ (hf 1)) (hC _ (hf 2))

/-! ### The induced three-vertex counting theorem -/

/-- **Induced three-vertex approximation.** On disjoint profile-matching cells with all
three required palette colors `ε`-uniform, the induced count is within `7·ε·|A||B||C|` of
the product of the three palette densities times the box volume. -/
theorem abs_inducedEmbeddingCountOn_three_sub_le [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A B C : Finset V} {ε : ℝ}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε)
    (h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C ε) :
    |(inducedEmbeddingCountOn P M ![A, B, C] : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card := by
  rw [inducedEmbeddingCountOn_three hnull hA hB hC hAB hAC hBC]
  exact abs_binaryPaletteTriangleCount_sub_le M _ _ _ hε0 hε1 h01 h02 h12

/-! ### Tests and adversarial examples -/

section Tests

/-- The unique model of the empty language (no relations to interpret). -/
private def emptyModel (V : Type*) : FiniteRelModel FirstOrder.Language.empty V :=
  ⟨fun {_} R _ => R.elim⟩

/-- A directed one-binary-symbol test model on `Fin 3`. -/
private def dModel (p : Fin 3 → Fin 3 → Bool) : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  ⟨fun {n} _ x => if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- Nullary incompatibility forces the induced three-vertex count to zero.
example [AtMostBinary L] {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    {A B C : Finset V} (h : ¬ NullaryCompatible P M) :
    inducedEmbeddingCountOn P M ![A, B, C] = 0 :=
  inducedEmbeddingCountOn_eq_zero_of_not_nullaryCompatible h

-- A profile mismatch on the middle cell forces the induced count to zero.
example [AtMostBinary L] {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    {A B C : Finset V}
    (h : ∀ v ∈ B, binaryVertexProfile P 1 ≠ binaryVertexProfile M v) :
    inducedEmbeddingCountOn P M ![A, B, C] = 0 :=
  inducedEmbeddingCountOn_eq_zero_of_profile_mismatch (i := 1) h

-- **Disjointness is genuinely necessary** — same pattern, model, and palette relations.
-- In the empty language (whose unique palette is automatically realized) with `A = B = C =
-- {0}` in `Fin 1`, the three required palette relations give triangle count `1` (the
-- diagonal triple `(0, 0, 0)`), yet the induced embedding count is `0`, because the only
-- candidate map `Fin 3 → {0}` is not injective. So `inducedEmbeddingCountOn_three` genuinely
-- requires the disjointness hypotheses.
example :
    inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 1)) ![{0}, {0}, {0}] = 0
      ∧ directedTriangleCount
          (HasBinaryPairPalette (emptyModel (Fin 1)) (binaryPairPalette (emptyModel (Fin 3)) 0 1))
          (HasBinaryPairPalette (emptyModel (Fin 1)) (binaryPairPalette (emptyModel (Fin 3)) 0 2))
          (HasBinaryPairPalette (emptyModel (Fin 1)) (binaryPairPalette (emptyModel (Fin 3)) 1 2))
          {0} {0} {0} = 1 := by
  refine ⟨?_, by decide⟩
  rw [inducedEmbeddingCountOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro f _ ⟨hinj, _⟩
  exact absurd (hinj (Subsingleton.elim (f 0) (f 1))) (by decide)

-- A concrete nonzero exact induced count: on disjoint singletons in the empty language, the
-- single injective map `0 ↦ 0, 1 ↦ 1, 2 ↦ 2` is the only induced embedding.
example :
    inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3)) ![{0}, {1}, {2}] = 1 := by
  rw [inducedEmbeddingCountOn_three (P := emptyModel (Fin 3)) (M := emptyModel (Fin 3))
    (fun R => isEmptyElim R) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (by decide) (by decide) (by decide)]
  decide

-- **Orientation matters.** For a directed one-symbol model (`a < b`), the required forward
-- palette on `(0, 1)` is realized at `(0, 1)` but not at the reversed pair `(1, 0)`, so
-- reversing a required palette color changes which pairs — hence which triangles — match.
example :
    HasBinaryPairPalette (dModel fun a b => decide ((a : ℕ) < b))
        (binaryPairPalette (dModel fun a b => decide ((a : ℕ) < b)) 0 1) 0 1
      ∧ ¬ HasBinaryPairPalette (dModel fun a b => decide ((a : ℕ) < b))
        (binaryPairPalette (dModel fun a b => decide ((a : ℕ) < b)) 0 1) 1 0 :=
  ⟨rfl, by decide⟩

-- The three-vertex reduction, as a statement-level instance.
example [AtMostBinary L] {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (hnull : NullaryCompatible P M) {f : Fin 3 → V}
    (h0 : binaryVertexProfile M (f 0) = binaryVertexProfile P 0)
    (h1 : binaryVertexProfile M (f 1) = binaryVertexProfile P 1)
    (h2 : binaryVertexProfile M (f 2) = binaryVertexProfile P 2) :
    PreservesAndReflects P M f ↔
      directedTriangleObs
        (HasBinaryPairPalette M (binaryPairPalette P 0 1))
        (HasBinaryPairPalette M (binaryPairPalette P 0 2))
        (HasBinaryPairPalette M (binaryPairPalette P 1 2)) f :=
  preservesAndReflects_three_iff hnull h0 h1 h2

-- **Joint palettes, not symbolwise marginals.** For a language with two binary symbols
-- (`coloredRelLang 2 2`), the theorem is stated in terms of `binaryPairPalette`, which
-- records both symbols' orientations jointly — a statement-level confirmation.
example {W : Type*} [Fintype W] [DecidableEq W]
    (P : FiniteRelModel (coloredRelLang 2 2) (Fin 3)) (M : FiniteRelModel (coloredRelLang 2 2) W)
    {A B C : Finset W} {ε : ℝ}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε)
    (h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C ε) :
    |(inducedEmbeddingCountOn P M ![A, B, C] : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card :=
  abs_inducedEmbeddingCountOn_three_sub_le hnull hA hB hC hAB hAC hBC hε0 hε1 h01 h02 h12

end Tests

end RegularityLemmata
