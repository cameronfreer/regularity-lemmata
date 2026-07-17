/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryDiagRegularity
import RegularityLemmata.Relational.BinaryStrong

/-!
# Phase 11 unit 5b: the strong diagonal-inclusive palette witness

The diagonal-inclusive twin of `Relational/BinaryStrong.lean` (Phase 11 design freeze
in `ARCHITECTURE.md`): the same seven data/proof fields, with `fine_regular`
strengthened to `fine_diagRegular : IsBinaryPaletteDiagRegular`.

Three reviewer-gated guarantees of this file:

* **Projection to the frozen witness** (`toBinaryPaletteStrongWitness`): the shared
  fields transport directly, and `fine_regular` is obtained through the
  diagonal-to-off-diagonal bridge — the projection is deliberately NOT definitional on
  that field, and every Phase 9/10 consumer applies unchanged through it.
* **Identical host-independent bounds** (`exists_binaryPaletteStrongDiagWitness`): the
  same `monoStepBound` iterates over the same fuel `⌈1/δ⌉` as the frozen existence
  theorem, because the diagonal-inclusive per-step summit reuses `regularityBound`.
* **Per-color diagonal-inclusive `deviant_mass_le`**: the re-exported deviant-mass
  bound sums over ALL ordered coarse pairs — diagonal coarse pairs and diagonal fine
  sub-pairs included — exactly as the removal route's representative selection
  (Unit 7) consumes it; and the per-color fine regularity is available in its
  diagonal-inclusive form directly (`fine_diagRegular c`).
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {δ : ℝ}

/-- A strong diagonal-inclusive palette witness against a starting partition `P₀`. -/
structure BinaryPaletteStrongDiagWitness (M : FiniteRelModel L V) (E : ErrorSchedule)
    (δ : ℝ) (P₀ : Finpartition s) where
  /-- The coarse partition. -/
  coarse : Finpartition s
  /-- The fine partition. -/
  fine : Finpartition s
  coarse_le : coarse ≤ P₀
  fine_le : fine ≤ coarse
  /-- The coarse partition refines the vertex-profile partition. -/
  coarse_profile : coarse ≤ binaryProfilePartition M s
  /-- The fine partition is simultaneously **diagonal-inclusively** palette-regular at
  the tolerance chosen against the coarse complexity. -/
  fine_diagRegular : IsBinaryPaletteDiagRegular M (E coarse.parts.card) fine
  /-- The fine refinement gains at most `δ` of aggregate palette energy. -/
  energy_gap : binaryPaletteEnergy M fine ≤ binaryPaletteEnergy M coarse + δ

namespace BinaryPaletteStrongDiagWitness

variable {M : FiniteRelModel L V} {E : ErrorSchedule} {P₀ : Finpartition s}

/-- The fine partition refines the vertex-profile partition too. -/
theorem fine_profile (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    w.fine ≤ binaryProfilePartition M s :=
  w.fine_le.trans w.coarse_profile

/-- The fine partition is palette-regular in the frozen off-diagonal sense. -/
theorem fine_regular (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    IsBinaryPaletteRegular M (E w.coarse.parts.card) w.fine :=
  w.fine_diagRegular.isBinaryPaletteRegular

/-- **Projection to the frozen witness.** The shared fields transport directly;
`fine_regular` is obtained through the diagonal-to-off-diagonal bridge (so this is
deliberately NOT definitional on that field). Every Phase 9/10 consumer applies
unchanged through this projection. -/
def toBinaryPaletteStrongWitness (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    BinaryPaletteStrongWitness M E δ P₀ where
  coarse := w.coarse
  fine := w.fine
  coarse_le := w.coarse_le
  fine_le := w.fine_le
  coarse_profile := w.coarse_profile
  fine_regular := w.fine_regular
  energy_gap := w.energy_gap

@[simp] theorem toBinaryPaletteStrongWitness_coarse
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    w.toBinaryPaletteStrongWitness.coarse = w.coarse := rfl

@[simp] theorem toBinaryPaletteStrongWitness_fine
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    w.toBinaryPaletteStrongWitness.fine = w.fine := rfl

/-- **The per-color handoff**, through the projection: each palette color yields an
ordinary strong witness for `HasBinaryPairPalette M c`. -/
def toStrongWitness (w : BinaryPaletteStrongDiagWitness M E δ P₀)
    (c : BinaryPairPalette L) : StrongWitness (HasBinaryPairPalette M c) E δ P₀ :=
  w.toBinaryPaletteStrongWitness.toStrongWitness c

/-- **Per-color deviant-mass bound, diagonal-inclusive by construction**: the sum
ranges over ALL ordered coarse pairs (diagonal coarse pairs included) and all fine
sub-pairs (diagonal fine pairs included) — exactly the form the representative
selection consumes. -/
theorem deviant_mass_le (w : BinaryPaletteStrongDiagWitness M E δ P₀)
    (c : BinaryPairPalette L) {η : ℝ} (hη : 0 < η) :
    ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ
          (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
            - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
  w.toBinaryPaletteStrongWitness.deviant_mass_le c hη

end BinaryPaletteStrongDiagWitness

/-! ### Existence by energy-gap stopping -/

/-- Fuel-parametrized diagonal-inclusive strong iteration — the port of the frozen
`binaryPalette_strong_iterate` over the diagonal-inclusive per-step summit, with the
SAME `monoStepBound` bookkeeping (the diag ladder reuses `regularityBound`). -/
theorem binaryPaletteDiag_strong_iterate (M : FiniteRelModel L V) (E : ErrorSchedule)
    (hδ : 0 < δ) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * δ ≤ binaryPaletteEnergy M P →
      ∃ coarse fine : Finpartition s, coarse ≤ P ∧ fine ≤ coarse ∧
        IsBinaryPaletteDiagRegular M (E coarse.parts.card) fine ∧
        binaryPaletteEnergy M fine ≤ binaryPaletteEnergy M coarse + δ ∧
        coarse.parts.card ≤ (monoStepBound E)^[t] P.parts.card ∧
        fine.parts.card ≤ (monoStepBound E)^[t + 1] P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_binaryPaletteDiagRegular_refinement_of_profiled M P (E.pos P.parts.card)
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
      exists_binaryPaletteDiagRegular_refinement_of_profiled M P (E.pos P.parts.card)
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

/-- **Strong diagonal-inclusive palette regularity** — the SAME host-independent
bounds (`monoStepBound` iterates over fuel `⌈1/δ⌉` from the profile-refined start) as
the frozen `exists_binaryPaletteStrongWitness`. -/
theorem exists_binaryPaletteStrongDiagWitness (M : FiniteRelModel L V)
    (E : ErrorSchedule) (hδ : 0 < δ) (P₀ : Finpartition s) :
    ∃ w : BinaryPaletteStrongDiagWitness M E δ P₀,
      w.coarse.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊] (refineByBinaryProfile M P₀).parts.card ∧
      w.fine.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊ + 1] (refineByBinaryProfile M P₀).parts.card := by
  obtain ⟨coarse, fine, hcP, hfc, hfreg, hfgap, hcc, hfcard⟩ :=
    binaryPaletteDiag_strong_iterate M E hδ ⌈1 / δ⌉₊ (refineByBinaryProfile M P₀) (by
      have h0 : (0 : ℝ) ≤ binaryPaletteEnergy M (refineByBinaryProfile M P₀) :=
        binaryPaletteEnergy_nonneg M _
      have ht : (1 : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
        calc (1 : ℝ) = 1 / δ * δ := by field_simp
          _ ≤ (⌈1 / δ⌉₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le
      linarith)
  exact ⟨⟨coarse, fine, hcP.trans (refineByBinaryProfile_le M P₀), hfc,
    hcP.trans (refineByBinaryProfile_le_profile M P₀), hfreg, hfgap⟩, hcc, hfcard⟩

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level: the strong diagonal-inclusive witness exists at concrete types,
-- with the frozen bounds.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (E : ErrorSchedule) {δ : ℝ}
    (hδ : 0 < δ) (P₀ : Finpartition (Finset.univ : Finset (Fin 4))) :
    ∃ w : BinaryPaletteStrongDiagWitness M E δ P₀,
      w.coarse.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊] (refineByBinaryProfile M P₀).parts.card ∧
      w.fine.parts.card
        ≤ (monoStepBound E)^[⌈1 / δ⌉₊ + 1] (refineByBinaryProfile M P₀).parts.card :=
  exists_binaryPaletteStrongDiagWitness M E hδ P₀

-- The projection preserves the partitions on the nose and delivers a frozen witness.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition (Finset.univ : Finset (Fin 4)))
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) :
    w.toBinaryPaletteStrongWitness.fine = w.fine ∧
      w.toBinaryPaletteStrongWitness.coarse = w.coarse :=
  ⟨rfl, rfl⟩

-- Per-color diagonal-inclusive fine regularity is available directly.
example (M : FiniteRelModel (singleRelLang 2) (Fin 4)) (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition (Finset.univ : Finset (Fin 4)))
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) (c : BinaryPairPalette (singleRelLang 2)) :
    IsRegularPartitionDiag (HasBinaryPairPalette M c) (E w.coarse.parts.card) w.fine :=
  w.fine_diagRegular c

end Tests

end RegularityLemmata
