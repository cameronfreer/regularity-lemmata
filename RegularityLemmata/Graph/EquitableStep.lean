/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.EquitableChunkApprox
import RegularityLemmata.Graph.Regularity

/-!
# Equitable-supplier ladder, step 4: the one-step theorem

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence step 4.
Step 3 delivered the equitabilised refinement (`Graph/EquitableChunk.lean`) and its loss
calculus (`Graph/EquitableChunkApprox.lean`) with every constant left open. This file
closes the numerics, in the order the constants actually depend on each other:

1. **The threshold is fixed**: `familyChunkThreshold = 100`. Combining the
   remainder-to-cell inequality `r · 4^(n·2^(2n)) ≤ |C|` with the transported numerical
   bridge `le_pow_mul_of_familyInitialBound_le` gives, at every part count at or above
   the initial floor, `100 · r ≤ ε⁵ · |C|` (`chunkThreshold_mul_chunkWitnessRemainder_le`).
   That is the whole content of the chunk condition: the remainder is smaller than every
   cell by a factor `ε⁵/100`.
2. **The density error is fixed**: `familyChunkDensityError ε = ε/2`, and the retained
   fraction `familyRetainedFraction = 1/5` is proved uniform — independent of the
   relation, the partition, the cells, the host, and `ε` itself. Both drop out of one
   elementary numerical lemma (`chunk_gain_numerics`), which discharges all four
   hypotheses of `blockEnergy_equitableIncrement_gain_of_retained` at once.
3. **The per-pair gain is summed**: `energy_equitableIncrement_increment` — on a
   partition whose bad mass exceeds `ε`, the equitabilised refinement of the offending
   relation raises that relation's normalized energy by `(1/5)·ε⁵`. This is step 3's
   `c·ε⁴` per bad pair pushed through the `ε`-free global increment
   `energy_increment_of_pairwise_gain` (`Graph/Regularity.lean`), which the exact
   refinement now shares.
4. **The component gain is lifted** to the family sum by
   `familyEnergy_add_le_of_component`: resolving ONE relation cannot decrease the other
   `K − 1` summands, because the increment refines `P`.
5. **The one-step theorem** `exists_familyEnergy_increment_equitable` packages the
   construction with its exact new part count `familyStepBound #P.parts`, its
   equipartition property, and the two structural requirements (`familyStepBound #P.parts
   ≤ #s` for the host, `familyInitialBound 100 ε l ≤ #P.parts` for the numerics).

Deliberately NOT here: the fuel `⌈K/(c·ε⁵)⌉` and the final part-count bound. Those are
step 5, and they are exactly what the now-proved `c = 1/5` unblocks.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] {ε : ℝ}
variable {P : Finpartition s}

/-! ### The frozen constants -/

/-- **The chunk threshold**, fixed here: the constant the ε-dependent initial floor must
beat, in mathlib's `100`. It is what `familyInitialBound` is instantiated at from now on.
-/
def familyChunkThreshold : ℝ := 100

/-- **The chunk density error**: the tolerance lost when a witness side is replaced by the
chunks it contains. Half of `ε`, with a wide margin — see `chunk_gain_numerics`. -/
noncomputable def familyChunkDensityError (ε : ℝ) : ℝ := ε / 2

/-- **The retained fraction** `c` of the exact refinement's `ε⁴` one-pair gain that
survives equitabilisation. Uniform: independent of the relation, the partition, the cells,
the host size, and `ε`. -/
noncomputable def familyRetainedFraction : ℝ := 1 / 5

theorem familyRetainedFraction_pos : 0 < familyRetainedFraction := by
  rw [familyRetainedFraction]; norm_num

theorem familyRetainedFraction_lt_one : familyRetainedFraction < 1 := by
  rw [familyRetainedFraction]; norm_num

/-! ### Step 1: the chunk condition -/

/-- **The chunk condition, fixed.** At every part count at or above the initial floor for
the threshold `100`, the witness-side remainder is smaller than every cell by `ε⁵/100`.

This is the conversion the loss calculus was left waiting for: the remainder-to-cell
inequality supplies the factor `4^(n·2^(2n))`, and the transported numerical bridge
`le_pow_mul_of_familyInitialBound_le` says the floor makes that factor beat `100/ε⁵`. -/
theorem chunkThreshold_mul_chunkWitnessRemainder_le (hP : P.IsEquipartition) (hε : 0 < ε)
    {l : ℕ} (hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card)
    {C : Finset α} (hC : C ∈ P.parts) :
    familyChunkThreshold * (chunkWitnessRemainder P : ℝ) ≤ ε ^ 5 * (C.card : ℝ) := by
  have hn : P.parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) :=
    Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  have hthr : familyChunkThreshold
      ≤ 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card)) * ε ^ 5 :=
    le_pow_mul_of_familyInitialBound_le hε (l := l) (hfloor.trans hn)
  have hrem := chunkWitnessRemainder_mul_pow_le_card_part_cast hP hC
  have hr0 : (0 : ℝ) ≤ (chunkWitnessRemainder P : ℝ) := Nat.cast_nonneg _
  have hε5 : (0 : ℝ) ≤ ε ^ 5 := by positivity
  calc familyChunkThreshold * (chunkWitnessRemainder P : ℝ)
      ≤ 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card)) * ε ^ 5
          * (chunkWitnessRemainder P : ℝ) := mul_le_mul_of_nonneg_right hthr hr0
    _ = ε ^ 5 * ((chunkWitnessRemainder P : ℝ)
          * 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card))) := by ring
    _ ≤ ε ^ 5 * (C.card : ℝ) := mul_le_mul_of_nonneg_left hrem hε5

/-! ### Step 2: the density error and the retained fraction -/

/-- **The numerical core of the step.** From `100·r ≤ ε⁵·a` and `100·r ≤ ε⁵·b` on the two
(nonempty) cells, with `0 < ε ≤ 1`, all four hypotheses of
`blockEnergy_equitableIncrement_gain_of_retained` hold for `δ = ε/2` and `c = 1/5`:
the remainder is dominated by both witness lower bounds; the discarded mass is within
`δ` of the recovered rectangle; and the degraded product still retains a fifth of the raw
gain. Every margin is wide — `9801/40000 ≥ 1/5` for the last — so the constants are
robust, not tuned. -/
private theorem chunk_gain_numerics {a b r ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (_hr0 : 0 ≤ r)
    (hra : 100 * r ≤ ε ^ 5 * a) (hrb : 100 * r ≤ ε ^ 5 * b) :
    r < ε * a ∧ r < ε * b
      ∧ r * b + a * r ≤ ε / 2 * ((ε * a - r) * (ε * b - r))
      ∧ 1 / 5 * (ε ^ 4 * a * b) ≤ (ε * a - r) * (ε * b - r) * (ε - ε / 2) ^ 2 := by
  have hεa : 0 < ε * a := mul_pos hε ha
  have hεb : 0 < ε * b := mul_pos hε hb
  have hab : 0 < a * b := mul_pos ha hb
  have hε4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε.le hε1
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  -- The chunk condition, weakened from `ε⁵` to `ε`.
  have hra' : 100 * r ≤ ε * a := le_trans hra (by nlinarith)
  have hrb' : 100 * r ≤ ε * b := le_trans hrb (by nlinarith)
  -- Both recovered sides keep 99% of the witness lower bound.
  have hA : 99 * (ε * a) / 100 ≤ ε * a - r := by linarith
  have hB : 99 * (ε * b) / 100 ≤ ε * b - r := by linarith
  have hApos : 0 < ε * a - r := by linarith
  have hAB : 99 * (ε * a) / 100 * (99 * (ε * b) / 100) ≤ (ε * a - r) * (ε * b - r) :=
    mul_le_mul hA hB (by positivity) (le_of_lt hApos)
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · -- The discarded mass is within `δ = ε/2` of the recovered rectangle.
    have h1 : r * b ≤ ε ^ 5 * a / 100 * b := mul_le_mul_of_nonneg_right (by linarith) hb.le
    have h2 : a * r ≤ a * (ε ^ 5 * b / 100) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    have hlhs : r * b + a * r ≤ ε ^ 5 * (a * b) / 50 := by nlinarith
    have hX : 0 < ε ^ 3 * (a * b) := by positivity
    have hkey : ε ^ 2 * (ε ^ 3 * (a * b)) ≤ 1 * (ε ^ 3 * (a * b)) :=
      mul_le_mul_of_nonneg_right hε2 hX.le
    have hmid : ε ^ 5 * (a * b) / 50
        ≤ ε / 2 * (99 * (ε * a) / 100 * (99 * (ε * b) / 100)) := by nlinarith
    have hrhs : ε / 2 * (99 * (ε * a) / 100 * (99 * (ε * b) / 100))
        ≤ ε / 2 * ((ε * a - r) * (ε * b - r)) :=
      mul_le_mul_of_nonneg_left hAB (by positivity)
    linarith
  · -- A fifth of the raw gain survives.
    have hY : (0 : ℝ) ≤ ε ^ 4 * (a * b) := by positivity
    have h1 : 99 * (ε * a) / 100 * (99 * (ε * b) / 100) * (ε - ε / 2) ^ 2
        ≤ (ε * a - r) * (ε * b - r) * (ε - ε / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hAB (by positivity)
    have h2 : 1 / 5 * (ε ^ 4 * a * b)
        ≤ 99 * (ε * a) / 100 * (99 * (ε * b) / 100) * (ε - ε / 2) ^ 2 := by nlinarith
    linarith

/-! ### Step 3: the per-pair gain, summed -/

/-- **The per-pair gain with the constants fixed**: a bad ordered pair contributes
`(1/5)·ε⁴·|C||D|` across the equitabilised refinement. All four numerical hypotheses of
step 3's loss theorem are discharged from the chunk condition alone. -/
theorem blockEnergy_equitableIncrement_retained (hP : P.IsEquipartition) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {l : ℕ}
    (hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card)
    {C D : Finset α} (hC : C ∈ P.parts) (hD : D ∈ P.parts) (hbad : IsBadPair R ε C D) :
    blockEnergy R C D
        + familyRetainedFraction * ε ^ 4 * ((C.card : ℝ) * (D.card : ℝ))
      ≤ ∑ C' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ C),
          ∑ D' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ D), blockEnergy R C' D' := by
  have hCpos : (0 : ℝ) < (C.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (P.nonempty_of_mem_parts hC)
  have hDpos : (0 : ℝ) < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (P.nonempty_of_mem_parts hD)
  have hrC := chunkThreshold_mul_chunkWitnessRemainder_le hP hε hfloor hC
  have hrD := chunkThreshold_mul_chunkWitnessRemainder_le hP hε hfloor hD
  rw [familyChunkThreshold] at hrC hrD
  obtain ⟨h1, h2, h3, h4⟩ := chunk_gain_numerics hε hε1 hCpos hDpos
    (Nat.cast_nonneg (chunkWitnessRemainder P)) hrC hrD
  have hmain := blockEnergy_equitableIncrement_gain_of_retained R ε hP hC hD hbad
    (δ := ε / 2) (by linarith) (by linarith) h1 h2 (by linarith [h3])
    (c := familyRetainedFraction) (by rw [familyRetainedFraction]; linarith [h4])
  have hrw : familyRetainedFraction * (ε ^ 4 * (C.card : ℝ) * (D.card : ℝ))
      = familyRetainedFraction * ε ^ 4 * ((C.card : ℝ) * (D.card : ℝ)) := by ring
  rwa [hrw] at hmain

/-- **The selected relation's normalized increment.** On a partition whose bad mass
exceeds `ε`, the equitabilised refinement raises that relation's normalized energy by
`(1/5)·ε⁵` — the exact refinement's `ε⁵` degraded by the uniform retained fraction, and
nothing else. -/
theorem energy_equitableIncrement_increment (hP : P.IsEquipartition) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {l : ℕ}
    (hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card)
    (hbm : ε < badMass R ε P) :
    energy R P + familyRetainedFraction * ε ^ 5
      ≤ energy R (equitableIncrement R ε hP) := by
  have h := energy_increment_of_pairwise_gain R (equitableIncrement_le R ε hP) hε
    (g := familyRetainedFraction * ε ^ 4)
    (by rw [familyRetainedFraction]; positivity)
    (fun C hC D hD hbad =>
      blockEnergy_equitableIncrement_retained R hP hε hε1 hfloor hC hD hbad) hbm
  have hrw : familyRetainedFraction * ε ^ 4 * ε = familyRetainedFraction * ε ^ 5 := by ring
  rwa [hrw] at h

/-! ### Steps 4 and 5: the family lift and the one-step theorem -/

section Family

variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]

/-- **The family lift.** Resolving ONE relation lifts its component gain to the family
sum: the other `K − 1` summands cannot decrease, because the equitabilised increment
refines `P`. -/
theorem familyEnergy_equitableIncrement_increment (hP : P.IsEquipartition) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {l : ℕ}
    (hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card) (k : Fin K)
    (hbm : ε < badMass (Rk k) ε P) :
    familyEnergy Rk P + familyRetainedFraction * ε ^ 5
      ≤ familyEnergy Rk (equitableIncrement (Rk k) ε hP) :=
  familyEnergy_add_le_of_component (equitableIncrement_le (Rk k) ε hP) k
    (energy_equitableIncrement_increment (Rk k) hP hε hε1 hfloor hbm)

/-- **The one-step theorem.** A non-family-regular equipartition, on a host large enough
to carry the step's part count and at a part count at or above the initial floor, admits a
refinement that is again an equipartition, has EXACTLY `familyStepBound #P.parts` parts,
and gains `(1/5)·ε⁵` of family energy.

Everything the iteration needs is here and nothing more: no fuel, and no final
part-count bound. -/
theorem exists_familyEnergy_increment_equitable (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (hP : P.IsEquipartition) (hε : 0 < ε) (hε1 : ε ≤ 1) {l : ℕ}
    (hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card)
    (hs : familyStepBound P.parts.card ≤ s.card)
    (hreg : ¬ IsFamilyRegular Rk ε P) :
    ∃ Q : Finpartition s, Q ≤ P ∧ Q.IsEquipartition
      ∧ Q.parts.card = familyStepBound P.parts.card
      ∧ familyEnergy Rk P + familyRetainedFraction * ε ^ 5 ≤ familyEnergy Rk Q := by
  rw [IsFamilyRegular] at hreg
  push Not at hreg
  obtain ⟨k, hk⟩ := hreg
  have hbm : ε < badMass (Rk k) ε P := lt_of_not_ge hk
  refine ⟨equitableIncrement (Rk k) ε hP, equitableIncrement_le (Rk k) ε hP,
    equitableIncrement_isEquipartition (Rk k) ε hP,
    card_equitableIncrement_parts (Rk k) ε hP hs,
    familyEnergy_equitableIncrement_increment hP hε hε1 hfloor k hbm⟩

end Family

/-! ### Tests and adversarial examples -/

section Tests

-- The frozen constants, concretely: the threshold is mathlib's `100`, the density error
-- is half the tolerance, and the retained fraction is a fifth — strictly between `0` and
-- `1`, so the step is a genuine but incomplete retention of the exact gain.
example : familyChunkThreshold = 100 := rfl

example (ε : ℝ) : familyChunkDensityError ε = ε / 2 := rfl

example : 0 < familyRetainedFraction ∧ familyRetainedFraction < 1 :=
  ⟨familyRetainedFraction_pos, familyRetainedFraction_lt_one⟩

-- The retained fraction is genuinely uniform: it mentions no relation, partition, host,
-- or tolerance. (A `c` depending on the output complexity is exactly the circularity the
-- route decision rejected, so this is a permanent guard.)
example : familyRetainedFraction = 1 / 5 := rfl

-- The numerical margin is not tight: `9801/40000` is what the proof delivers, and it
-- exceeds the claimed `1/5` by more than a fifth of itself.
example : (1 : ℝ) / 5 ≤ 9801 / 40000 := by norm_num

-- The chunk condition at the frozen threshold is exactly mathlib's `100 ≤ 4^N·ε⁵` shape.
example {N : ℕ} (hN : familyInitialBound familyChunkThreshold (1 / 2) 3 ≤ N) :
    familyChunkThreshold ≤ 4 ^ N * (1 / 2 : ℝ) ^ 5 :=
  le_pow_mul_of_familyInitialBound_le (by norm_num) hN

-- The `K = 0` endpoint survives: the empty family is regular at every tolerance, so the
-- one-step theorem's non-regularity hypothesis is unsatisfiable there — the step is never
-- invoked, rather than invoked vacuously.
example (P : Finpartition (Finset.univ : Finset (Fin 3))) (ε : ℝ) :
    ¬ ¬ IsFamilyRegular (fun _ : Fin 0 => fun _ _ : Fin 3 => True) ε P :=
  not_not_intro (isFamilyRegular_zero _)

end Tests

end RegularityLemmata
