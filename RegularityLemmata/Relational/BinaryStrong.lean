/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryRegularity
import RegularityLemmata.Graph.Strong

/-!
# Strong binary-palette witnesses

Phase 9 unit 6 (design freeze in `ARCHITECTURE.md`): the strong (energy-gap)
regularity witness at the palette level, reusing the existing `ErrorSchedule` and the
graph strong-regularity stopping architecture.

A `BinaryPaletteStrongWitness` carries a coarse partition refining the
vertex-profile partition, a fine refinement of it that is simultaneously
palette-regular at the schedule's tolerance for the coarse complexity, and an
aggregate palette-energy gap of at most `δ`. Its existence
(`exists_binaryPaletteStrongWitness`) ports the energy-gap stopping argument with
`binaryPaletteEnergy` (which lives in `[0, 1]`), starting from a profile-refined
partition.

The crucial handoff is per-color: `BinaryPaletteStrongWitness.toStrongWitness c` is
an ordinary `StrongWitness` for `HasBinaryPairPalette M c` — the per-color energy gap
follows because every palette-energy increment is nonnegative and bounded by the
aggregate gap — so the existing `StrongWitness.deviant_mass_le` re-exports for every
palette color (`BinaryPaletteStrongWitness.deviant_mass_le`).
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {δ : ℝ}

/-- A strong palette witness against a starting partition `P₀`. -/
structure BinaryPaletteStrongWitness (M : FiniteRelModel L V) (E : ErrorSchedule)
    (δ : ℝ) (P₀ : Finpartition s) where
  /-- The coarse partition. -/
  coarse : Finpartition s
  /-- The fine partition. -/
  fine : Finpartition s
  coarse_le : coarse ≤ P₀
  fine_le : fine ≤ coarse
  /-- The coarse partition refines the vertex-profile partition. -/
  coarse_profile : coarse ≤ binaryProfilePartition M s
  /-- The fine partition is simultaneously palette-regular at the tolerance chosen
  against the coarse complexity. -/
  fine_regular : IsBinaryPaletteRegular M (E coarse.parts.card) fine
  /-- The fine refinement gains at most `δ` of aggregate palette energy. -/
  energy_gap : binaryPaletteEnergy M fine ≤ binaryPaletteEnergy M coarse + δ

/-- The fine partition refines the vertex-profile partition too. -/
theorem BinaryPaletteStrongWitness.fine_profile {M : FiniteRelModel L V}
    {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) :
    w.fine ≤ binaryProfilePartition M s :=
  w.fine_le.trans w.coarse_profile

/-! ### Existence by energy-gap stopping -/

/-- Fuel-parametrized palette strong iteration. -/
theorem binaryPalette_strong_iterate (M : FiniteRelModel L V) (E : ErrorSchedule)
    (hδ : 0 < δ) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * δ ≤ binaryPaletteEnergy M P →
      ∃ coarse fine : Finpartition s, coarse ≤ P ∧ fine ≤ coarse ∧
        IsBinaryPaletteRegular M (E coarse.parts.card) fine ∧
        binaryPaletteEnergy M fine ≤ binaryPaletteEnergy M coarse + δ ∧
        coarse.parts.card ≤ (monoStepBound E)^[t] P.parts.card ∧
        fine.parts.card ≤ (monoStepBound E)^[t + 1] P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_binaryPalette_regular_refinement_of_profiled M P (E.pos P.parts.card)
    have hgap : binaryPaletteEnergy M Q ≤ binaryPaletteEnergy M P + δ := by
      have h1 : binaryPaletteEnergy M Q ≤ 1 := binaryPaletteEnergy_le_one M Q
      have h2 : (1 : ℝ) ≤ binaryPaletteEnergy M P := by simpa using hbudget
      linarith
    refine ⟨P, Q, le_rfl, hQP, hQreg, hgap, by simp, ?_⟩
    calc Q.parts.card
        ≤ regularityBound ⌈1 / (E P.parts.card) ^ 5⌉₊ P.parts.card := hQcard
      _ ≤ monoStepBound E P.parts.card := stepBound_le_monoStepBound E _
      _ = (monoStepBound E)^[0 + 1] P.parts.card := by simp
  | succ t IH =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_binaryPalette_regular_refinement_of_profiled M P (E.pos P.parts.card)
    have hQmono : Q.parts.card ≤ monoStepBound E P.parts.card :=
      le_trans hQcard (stepBound_le_monoStepBound E _)
    by_cases hgap : binaryPaletteEnergy M Q ≤ binaryPaletteEnergy M P + δ
    · refine ⟨P, Q, le_rfl, hQP, hQreg, hgap, le_monoStepBound_iterate E _ _, ?_⟩
      calc Q.parts.card ≤ monoStepBound E P.parts.card := hQmono
        _ = (monoStepBound E)^[1] P.parts.card := rfl
        _ ≤ (monoStepBound E)^[t + 1 + 1] P.parts.card :=
            monoStepBound_iterate_le_iterate E (by omega) _
    · rw [not_le] at hgap
      have hbudget' : 1 - (t : ℝ) * δ ≤ binaryPaletteEnergy M Q := by
        push_cast at hbudget
        nlinarith [hgap, hbudget]
      obtain ⟨coarse, fine, hcP, hfc, hfreg, hfgap, hcc, hfcard⟩ := IH Q hbudget'
      refine ⟨coarse, fine, hcP.trans hQP, hfc, hfreg, hfgap, ?_, ?_⟩
      · calc coarse.parts.card ≤ (monoStepBound E)^[t] Q.parts.card := hcc
          _ ≤ (monoStepBound E)^[t] (monoStepBound E P.parts.card) :=
              monoStepBound_iterate_mono E t hQmono
          _ = (monoStepBound E)^[t + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm
      · calc fine.parts.card ≤ (monoStepBound E)^[t + 1] Q.parts.card := hfcard
          _ ≤ (monoStepBound E)^[t + 1] (monoStepBound E P.parts.card) :=
              monoStepBound_iterate_mono E _ hQmono
          _ = (monoStepBound E)^[t + 1 + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm

/-- **Strong palette regularity.** Every starting partition admits a strong palette
witness for any positive error schedule and gap, refining the vertex-profile
partition, with host-independent part-count bounds. -/
theorem exists_binaryPaletteStrongWitness (M : FiniteRelModel L V) (E : ErrorSchedule)
    (hδ : 0 < δ) (P₀ : Finpartition s) :
    ∃ w : BinaryPaletteStrongWitness M E δ P₀,
      w.coarse.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊] (refineByBinaryProfile M P₀).parts.card ∧
      w.fine.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊ + 1] (refineByBinaryProfile M P₀).parts.card := by
  obtain ⟨coarse, fine, hcP, hfc, hfreg, hfgap, hcc, hfcard⟩ :=
    binaryPalette_strong_iterate M E hδ ⌈1 / δ⌉₊ (refineByBinaryProfile M P₀) (by
      have h0 : (0 : ℝ) ≤ binaryPaletteEnergy M (refineByBinaryProfile M P₀) :=
        binaryPaletteEnergy_nonneg M _
      have ht : (1 : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
        calc (1 : ℝ) = 1 / δ * δ := by field_simp
          _ ≤ (⌈1 / δ⌉₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le
      linarith)
  exact ⟨⟨coarse, fine, hcP.trans (refineByBinaryProfile_le M P₀), hfc,
    hcP.trans (refineByBinaryProfile_le_profile M P₀), hfreg, hfgap⟩, hcc, hfcard⟩

/-! ### The per-color handoff -/

/-- The aggregate palette-energy gap bounds every single color's gap (each per-color
increment is nonnegative under refinement). -/
theorem energy_le_of_binaryPaletteEnergy_gap (M : FiniteRelModel L V)
    {fine coarse : Finpartition s} (hfc : fine ≤ coarse)
    (hgap : binaryPaletteEnergy M fine ≤ binaryPaletteEnergy M coarse + δ)
    (c : BinaryPairPalette L) :
    energy (HasBinaryPairPalette M c) fine
      ≤ energy (HasBinaryPairPalette M c) coarse + δ := by
  have hnn : ∀ c' ∈ (Finset.univ : Finset (BinaryPairPalette L)),
      0 ≤ energy (HasBinaryPairPalette M c') fine
        - energy (HasBinaryPairPalette M c') coarse :=
    fun c' _ => sub_nonneg.mpr (energy_mono _ hfc)
  have hsingle : energy (HasBinaryPairPalette M c) fine
        - energy (HasBinaryPairPalette M c) coarse
      ≤ ∑ c' : BinaryPairPalette L,
          (energy (HasBinaryPairPalette M c') fine
            - energy (HasBinaryPairPalette M c') coarse) :=
    Finset.single_le_sum hnn (Finset.mem_univ c)
  have hsum : binaryPaletteEnergy M fine - binaryPaletteEnergy M coarse
      = ∑ c' : BinaryPairPalette L,
          (energy (HasBinaryPairPalette M c') fine
            - energy (HasBinaryPairPalette M c') coarse) := by
    rw [binaryPaletteEnergy, binaryPaletteEnergy, ← Finset.sum_sub_distrib]
  linarith

/-- **The per-color handoff.** Each palette color yields an ordinary strong
witness. -/
def BinaryPaletteStrongWitness.toStrongWitness {M : FiniteRelModel L V}
    {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (c : BinaryPairPalette L) :
    StrongWitness (HasBinaryPairPalette M c) E δ P₀ where
  coarse := w.coarse
  fine := w.fine
  coarse_le := w.coarse_le
  fine_le := w.fine_le
  fine_regular := w.fine_regular c
  energy_gap := energy_le_of_binaryPaletteEnergy_gap M w.fine_le w.energy_gap c

/-- **Per-color deviant-mass bound**, re-exported from the existing
`StrongWitness.deviant_mass_le`. -/
theorem BinaryPaletteStrongWitness.deviant_mass_le {M : FiniteRelModel L V}
    {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness M E δ P₀) (c : BinaryPairPalette L)
    {η : ℝ} (hη : 0 < η) :
    ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ
          (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
            - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
  StrongWitness.deviant_mass_le (R := HasBinaryPairPalette M c) (w.toStrongWitness c) hη

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level: the strong palette witness exists at concrete types.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (E : ErrorSchedule) {δ : ℝ}
    (hδ : 0 < δ) (P₀ : Finpartition (Finset.univ : Finset (Fin 4))) :
    ∃ w : BinaryPaletteStrongWitness M E δ P₀,
      w.coarse.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊] (refineByBinaryProfile M P₀).parts.card ∧
      w.fine.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊ + 1] (refineByBinaryProfile M P₀).parts.card :=
  exists_binaryPaletteStrongWitness M E hδ P₀

-- The fine partition refines both the coarse partition and the vertex-profile
-- partition.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition (Finset.univ : Finset (Fin 4)))
    (w : BinaryPaletteStrongWitness M E δ P₀) :
    w.fine ≤ binaryProfilePartition M Finset.univ :=
  w.fine_profile

end Tests

end RegularityLemmata
