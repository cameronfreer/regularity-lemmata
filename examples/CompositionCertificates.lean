/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrong
import RegularityLemmata.Relational.DiagonalGate
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Composition certificates: existence of a strong witness, then counting

Two compiled checks that the strong-witness existence theorem and the three-vertex counting
theorem fit together, using proved results only (no placeholders). They certify different
things and are kept apart:

1. **Compatibility check.** Obtain the witness from `exists_binaryPaletteStrongWitness`, discharge
   every hypothesis of the counting theorem
   `BinaryPaletteStrongWitness.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le`, and
   read off the estimate with the trivial cell ceiling `m = |s|`. The diagonal charge is then
   `3·|s|³`, so the estimate is uninformative; this certifies that carriers, nullary condition,
   schedule, and error units agree, nothing more.
2. **Endpoint with a prescribed error.** Seed with an equipartition of `p` parts so that the
   `…_of_equipartition` form gives the cell ceiling `|s|/p + 1`, take a constant schedule and choose
   `η`, `δ`, `p` from the target `ε₀` in a visible, non-circular order; under the explicit host-size
   condition `24/ε₀ ≤ |s|` the induced count of any three-vertex pattern is within `ε₀·|s|³` of the
   coarse estimate. Nothing in the library composes these two theorems; the choices below are the
   consumer's.

Direct module imports are advertised entry points; the facades do not bundle this stack.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {L : FirstOrder.Language} [FiniteRelational L] [AtMostBinary L] {V : Type*}
  [DecidableEq V] {s : Finset V}

/-- The constant error schedule at tolerance `τ > 0`. -/
def constSchedule {τ : ℝ} (hτ : 0 < τ) : ErrorSchedule := ⟨fun _ => τ, fun _ => hτ⟩

/-- **Compatibility check.** From the existence theorem to the counting theorem with the trivial
cell ceiling `m = |s|`: the hypotheses line up and the conclusion has the counting theorem's shape,
with the uninformative diagonal charge `3·|s|³`. -/
theorem compatibility (M : FiniteRelModel L V) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) {τ δ η : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (hη : 0 < η) (P₀ : Finpartition s) :
    ∃ Q : Finpartition s,
      |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M Q|
        ≤ (10 * τ + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
          + 3 * (s.card : ℝ) * (s.card : ℝ) ^ 2 := by
  obtain ⟨w, -, -⟩ := exists_binaryPaletteStrongWitness M (constSchedule hτ) hδ P₀
  refine ⟨w.coarse, ?_⟩
  have hm : ∀ C ∈ w.coarse.parts, C.card ≤ s.card := fun C hC =>
    Finset.card_le_card (w.coarse.le hC)
  have h := w.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le P hnull
    (by simpa [constSchedule] using hτ1) hη hm
  simpa [constSchedule] using h

/-- **Endpoint with a prescribed error.** Parameter order: the target `ε₀` is given; the schedule
is the constant `ε₀/40`, `η = ε₀/12`, `δ = η²·ε₀/12`, and the seed is an equipartition with
`p = ⌈24/ε₀⌉₊` parts, which exists because `24/ε₀ ≤ |s|`; the four error terms are each at most
`ε₀/4·|s|³`. -/
theorem prescribed_error (M : FiniteRelModel L V) (P : FiniteRelModel L (Fin 3))
    (hnull : NullaryCompatible P M) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ ≤ 1)
    (hs : 24 / ε₀ ≤ (s.card : ℝ)) :
    ∃ Q : Finpartition s,
      |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M Q|
        ≤ ε₀ * (s.card : ℝ) ^ 3 := by
  -- The seed: an equipartition with `p = ⌈24/ε₀⌉₊` parts.
  set p : ℕ := ⌈24 / ε₀⌉₊ with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity))
  have hps : p ≤ s.card := by
    rw [hp]; exact Nat.ceil_le.mpr hs
  obtain ⟨P₀, hP₀, hP₀card⟩ := Finpartition.exists_equipartition_card_eq s hp0 hps
  -- The schedule and the analytic parameters.
  have hτ : (0 : ℝ) < ε₀ / 40 := by positivity
  have hη : (0 : ℝ) < ε₀ / 12 := by positivity
  have hδ : (0 : ℝ) < (ε₀ / 12) ^ 2 * ε₀ / 12 := by positivity
  obtain ⟨w, -, -⟩ := exists_binaryPaletteStrongWitness M (constSchedule hτ) hδ P₀
  refine ⟨w.coarse, ?_⟩
  have h := w.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le_of_equipartition hP₀ P
    hnull (by simp only [constSchedule]; linarith) hη
  simp only [constSchedule] at h
  refine h.trans ?_
  -- Each of the four terms is at most `ε₀/4 · |s|³`.
  have hn : (24 / ε₀ : ℝ) ≤ s.card := hs
  have hn0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hcell : ((s.card / P₀.parts.card + 1 : ℕ) : ℝ) ≤ (s.card : ℝ) * ε₀ / 24 + 1 := by
    push_cast
    have h1 : ((s.card / p : ℕ) : ℝ) ≤ (s.card : ℝ) / p := Nat.cast_div_le
    have h2 : (24 / ε₀ : ℝ) ≤ p := by rw [hp]; exact Nat.le_ceil _
    have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
    have h3 : (s.card : ℝ) / p ≤ (s.card : ℝ) * ε₀ / 24 := by
      rw [div_le_iff₀ hp']
      have : (s.card : ℝ) * (24 / ε₀) ≤ (s.card : ℝ) * p := mul_le_mul_of_nonneg_left h2 hn0
      calc (s.card : ℝ) = (s.card : ℝ) * (24 / ε₀) * (ε₀ / 24) := by field_simp
        _ ≤ (s.card : ℝ) * p * (ε₀ / 24) := by
          apply mul_le_mul_of_nonneg_right this; positivity
        _ = (s.card : ℝ) * ε₀ / 24 * p := by ring
    rw [hP₀card]
    linarith
  have hδη : 3 * ((ε₀ / 12) ^ 2 * ε₀ / 12 / (ε₀ / 12) ^ 2) = ε₀ / 4 := by
    field_simp; ring
  rw [hδη]
  have hs3 : (0 : ℝ) ≤ (s.card : ℝ) ^ 3 := by positivity
  have hs2 : (0 : ℝ) ≤ (s.card : ℝ) ^ 2 := by positivity
  -- `3·(|s|ε₀/24 + 1)·|s|² ≤ ε₀/4 · |s|³` uses `1 ≤ ε₀|s|/24`, i.e. the host-size condition.
  have hone : (1 : ℝ) ≤ (s.card : ℝ) * ε₀ / 24 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 24)]
    calc (1 : ℝ) * 24 = 24 := by ring
      _ = (24 / ε₀) * ε₀ := by field_simp
      _ ≤ (s.card : ℝ) * ε₀ := mul_le_mul_of_nonneg_right hn hε₀.le
  have hdiag : 3 * ((s.card / P₀.parts.card + 1 : ℕ) : ℝ) * (s.card : ℝ) ^ 2
      ≤ ε₀ / 4 * (s.card : ℝ) ^ 3 := by
    calc 3 * ((s.card / P₀.parts.card + 1 : ℕ) : ℝ) * (s.card : ℝ) ^ 2
        ≤ 3 * ((s.card : ℝ) * ε₀ / 24 + 1) * (s.card : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hs2
          exact mul_le_mul_of_nonneg_left hcell (by norm_num)
      _ ≤ 3 * ((s.card : ℝ) * ε₀ / 24 + (s.card : ℝ) * ε₀ / 24) * (s.card : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hs2
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith
      _ = ε₀ / 4 * (s.card : ℝ) ^ 3 := by ring
  nlinarith [hdiag, hs3]

end RegularityLemmataExamples
