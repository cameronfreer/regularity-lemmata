/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPalette
import RegularityLemmata.Partition.Energy
import RegularityLemmata.Graph.BadMass

/-!
# Palette energy and the regularity surface

Phase 9 unit 3 (design freeze in `ARCHITECTURE.md`): the mass-weighted energy summed
over the two-way palette, and simultaneous palette regularity.

`binaryPaletteEnergy M P = ∑_c energy (HasBinaryPairPalette M c) P` is nonnegative,
refinement-monotone, and — the load-bearing fact — bounded by `1`, **not** by the
number of palette colors (`binaryPaletteEnergy_le_one`): on each block the palette
densities form a probability vector, so `∑_c d_c² ≤ ∑_c d_c ≤ 1`, and mass-weighting
then summing over blocks keeps the total at most `1`. This is why the iteration fuel
stays `⌈1/ε⁵⌉`, independent of the palette count.

`IsBinaryPaletteRegular M ε P` asks every palette color to be `ε`-regular
simultaneously — strictly stronger than per-symbol regularity, and the correct
surface for induced binary patterns. It is monotone in `ε`, holds at `ε = 1`, and its
failure yields an actual bad palette color
(`exists_bad_of_not_isBinaryPaletteRegular`).
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {ε : ℝ}

/-! ### The block-level probability-vector bound -/

omit [DecidableEq V] in
/-- The palette densities on a rectangle sum to at most `1` (exactly `1` on a
nonempty rectangle; `0` if a side is empty). -/
theorem sum_pairDensity_le_one (M : FiniteRelModel L V) (A B : Finset V) :
    ∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B ≤ 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun c _ => ?_)) zero_le_one
    rw [pairDensity, Finset.empty_product, densityOn_empty]
  rcases B.eq_empty_or_nonempty with rfl | hB
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun c _ => ?_)) zero_le_one
    rw [pairDensity, Finset.product_empty, densityOn_empty]
  · exact le_of_eq (sum_pairDensity_hasBinaryPairPalette M A B hA hB)

omit [DecidableEq V] in
/-- The squared palette densities on a rectangle sum to at most `1`. -/
theorem sum_sq_pairDensity_le_one (M : FiniteRelModel L V) (A B : Finset V) :
    ∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) (sum_pairDensity_le_one M A B)
  have h0 : (0 : ℝ) ≤ pairDensity (HasBinaryPairPalette M c) A B := pairDensity_nonneg
  have h1 : pairDensity (HasBinaryPairPalette M c) A B ≤ 1 := pairDensity_le_one
  nlinarith

omit [DecidableEq V] in
/-- The palette block energies on a rectangle sum to at most `|A|·|B|`. -/
theorem sum_blockEnergy_le (M : FiniteRelModel L V) (A B : Finset V) :
    ∑ c : BinaryPairPalette L, blockEnergy (HasBinaryPairPalette M c) A B
      ≤ (A.card : ℝ) * B.card := by
  have h1 : ∑ c : BinaryPairPalette L, blockEnergy (HasBinaryPairPalette M c) A B
      = (∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B ^ 2)
        * ((A.card : ℝ) * B.card) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by rw [blockEnergy]; ring
  rw [h1]
  calc (∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B ^ 2)
        * ((A.card : ℝ) * B.card)
      ≤ 1 * ((A.card : ℝ) * B.card) :=
        mul_le_mul_of_nonneg_right (sum_sq_pairDensity_le_one M A B) (by positivity)
    _ = (A.card : ℝ) * B.card := one_mul _

/-! ### Palette energy -/

/-- The mass-weighted energy summed over the two-way palette. -/
noncomputable def binaryPaletteEnergy (M : FiniteRelModel L V) (P : Finpartition s) : ℝ :=
  ∑ c : BinaryPairPalette L, energy (HasBinaryPairPalette M c) P

theorem binaryPaletteEnergy_nonneg (M : FiniteRelModel L V) (P : Finpartition s) :
    0 ≤ binaryPaletteEnergy M P :=
  Finset.sum_nonneg fun _ _ => energy_nonneg _

/-- The palette energy numerators sum to at most `|s|²`. -/
theorem sum_energyNum_le (M : FiniteRelModel L V) (P : Finpartition s) :
    ∑ c : BinaryPairPalette L, energyNum (HasBinaryPairPalette M c) P
      ≤ (s.card : ℝ) ^ 2 := by
  have hswap : ∑ c : BinaryPairPalette L, energyNum (HasBinaryPairPalette M c) P
      = ∑ AB ∈ P.parts ×ˢ P.parts,
          ∑ c : BinaryPairPalette L, blockEnergy (HasBinaryPairPalette M c) AB.1 AB.2 :=
    Finset.sum_comm
  rw [hswap]
  calc ∑ AB ∈ P.parts ×ˢ P.parts,
          ∑ c : BinaryPairPalette L, blockEnergy (HasBinaryPairPalette M c) AB.1 AB.2
      ≤ ∑ AB ∈ P.parts ×ˢ P.parts, ((AB.1.card : ℝ) * AB.2.card) :=
        Finset.sum_le_sum fun AB _ => sum_blockEnergy_le M AB.1 AB.2
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

/-- **Energy `≤ 1`, not `≤ #colors`** — the fuel-independence bound. -/
theorem binaryPaletteEnergy_le_one (M : FiniteRelModel L V) (P : Finpartition s) :
    binaryPaletteEnergy M P ≤ 1 := by
  have hrw : binaryPaletteEnergy M P
      = (∑ c : BinaryPairPalette L, energyNum (HasBinaryPairPalette M c) P)
        / (s.card : ℝ) ^ 2 := by
    rw [binaryPaletteEnergy, Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hrw]
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · rw [div_le_one (by positivity)]
    exact sum_energyNum_le M P

/-- Refinement monotonicity: refining raises the palette energy. -/
theorem binaryPaletteEnergy_mono (M : FiniteRelModel L V) {P Q : Finpartition s}
    (hQ : Q ≤ P) : binaryPaletteEnergy M P ≤ binaryPaletteEnergy M Q :=
  Finset.sum_le_sum fun _ _ => energy_mono _ hQ

/-! ### Simultaneous palette regularity -/

/-- Simultaneous `ε`-regularity of every palette color. -/
def IsBinaryPaletteRegular (M : FiniteRelModel L V) (ε : ℝ) (P : Finpartition s) :
    Prop :=
  ∀ c : BinaryPairPalette L, IsRegularPartition (HasBinaryPairPalette M c) ε P

/-- Monotone in the tolerance. -/
theorem IsBinaryPaletteRegular.mono {M : FiniteRelModel L V} {P : Finpartition s}
    {ε ε' : ℝ} (hεε : ε ≤ ε') (h : IsBinaryPaletteRegular M ε P) :
    IsBinaryPaletteRegular M ε' P :=
  fun c => IsRegularPartition.mono (R := HasBinaryPairPalette M c) hεε (h c)

/-- Every partition is palette-regular at tolerance `1`. -/
theorem isBinaryPaletteRegular_one (M : FiniteRelModel L V) (P : Finpartition s) :
    IsBinaryPaletteRegular M 1 P :=
  fun _ => isRegularPartition_one _

/-- **Failure yields a bad palette color.** -/
theorem exists_bad_of_not_isBinaryPaletteRegular {M : FiniteRelModel L V}
    {P : Finpartition s} (h : ¬IsBinaryPaletteRegular M ε P) :
    ∃ c : BinaryPairPalette L, ε < badMass (HasBinaryPairPalette M c) ε P := by
  rw [IsBinaryPaletteRegular] at h
  push Not at h
  obtain ⟨c, hc⟩ := h
  rw [IsRegularPartition, not_le] at hc
  exact ⟨c, hc⟩

/-! ### Tests and adversarial examples -/

section Tests

/-- A one-binary-symbol test model. -/
private def loopModel {V : Type*} [DecidableEq V] (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- Statement-level bounds and regularity at concrete types.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (P : Finpartition (Finset.univ : Finset (Fin 4))) :
    0 ≤ binaryPaletteEnergy M P ∧ binaryPaletteEnergy M P ≤ 1 :=
  ⟨binaryPaletteEnergy_nonneg M P, binaryPaletteEnergy_le_one M P⟩

example (M : FiniteRelModel (singleRelLang 2) (Fin 4))
    (P : Finpartition (Finset.univ : Finset (Fin 4))) :
    IsBinaryPaletteRegular M 1 P :=
  isBinaryPaletteRegular_one M P

-- **Two realized two-way colors** (nontrivial palette content). On `Fin 2` the
-- adjacency `a < b` realizes the ordered palette `(true, false)` on `(0, 1)` and
-- `(false, true)` on `(1, 0)` — distinct two-way colors that a one-way coloring
-- would merge, so the palette energy genuinely spreads across colors.
example :
    (0 < pairCount (HasBinaryPairPalette
        (loopModel (V := Fin 2) fun a b => decide ((a : ℕ) < b))
        fun _ => (true, false)) Finset.univ Finset.univ)
      ∧ (0 < pairCount (HasBinaryPairPalette
        (loopModel (V := Fin 2) fun a b => decide ((a : ℕ) < b))
        fun _ => (false, true)) Finset.univ Finset.univ) := by decide

end Tests

end RegularityLemmata
