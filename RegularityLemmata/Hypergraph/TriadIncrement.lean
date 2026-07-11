/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Triad
import RegularityLemmata.Hypergraph.PolyadWitness
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The global energy increment

Phase 7 unit 4/5 capstone (design freeze in `ARCHITECTURE.md`): when the bad keys of
a pair coloring carry more than a `δ` fraction of the triple mass, one simultaneous
cut round strictly gains more than `δ⁴` of normalized energy
(`polyadEnergy_cutRefine_gain`).

The witness family is the **chosen simultaneous witness family**
(`badWitnessFamily`): an actual `DiscWitness` on each bad key, selected by
`Classical.choice` from `exists_discWitness`, and the empty face family on good keys — the cut budget of `cutBound 2 K = K·2^(3K³)` safely counts all possible
tests even though the good keys' cuts are constant. The proof composes the exact
refinement-variance identity (`polyadEnergyNum_comp_variance`, through the merge
identity `cutRefineProj_comp`) with the strict local gain
`δ³·|block| < variance` at every bad key (`local_variance_gain`), summed over the
(nonempty) bad-key set, then normalizes: the gain exceeds
`δ³ · badTriadMass > δ⁴`. This is the index-increment step of the iteration toward
the weak regularization summit, following V. Rödl, M. Schacht, *Regular partitions
of hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007).
-/

namespace RegularityLemmata

open UniformHypergraph

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- The chosen simultaneous witness family: an actual witness on each bad key
(classical choice), the empty face family elsewhere. -/
noncomputable def badWitnessFamily (H : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (δ : ℝ) :
    (Fin 3 → Fin K) → Fin 3 → Finset (RSet 2 α) := by
  classical
  exact fun key =>
    if h : IsBadTriad H κ δ key then (exists_discWitness h).some.faces
    else fun _ => ∅

/-- On a bad key, the chosen family is an actual witness's face system. -/
theorem badWitnessFamily_spec {H : UniformHypergraph 3 α} {κ : RSet 2 α → Fin K}
    {δ : ℝ} {key : Fin 3 → Fin K} (h : IsBadTriad H κ δ key) :
    ∃ w : DiscWitness κ (triadObs H) key δ,
      badWitnessFamily H κ δ key = w.faces := by
  classical
  refine ⟨(exists_discWitness h).some, ?_⟩
  rw [badWitnessFamily]
  simp only [dif_pos h]

/-- **The global increment**: if the bad keys carry more than a `δ` fraction of the
triple mass, one simultaneous cut round strictly gains more than `δ⁴` of normalized
energy. -/
theorem polyadEnergy_cutRefine_gain {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} (hδ : 0 < δ)
    (hbad : δ < badTriadMass H κ δ) :
    δ ^ 4 < polyadEnergy (cutRefine κ (badWitnessFamily H κ δ)) (triadObs H)
        - polyadEnergy κ (triadObs H) := by
  classical
  set W := badWitnessFamily H κ δ with hWdef
  -- The host is nonempty (otherwise the bad mass is 0 and `δ < 0`).
  have hV : (0 : ℝ) < (Fintype.card α : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
    · exfalso
      rw [badTriadMass, h0] at hbad
      norm_num at hbad
      linarith
    · positivity
  -- The exact variance identity, with the merge rewritten back to `κ`.
  have hvar := polyadEnergyNum_comp_variance (cutRefineProj (j := 2) (K := K))
    (cutRefine κ W) (triadObs H)
  rw [cutRefineProj_comp κ W] at hvar
  -- The bad keys alone force the variance above `δ³ · badTriadMassNum`.
  have hne : (Finset.univ.filter fun key : Fin 3 → Fin K =>
      IsBadTriad H κ δ key).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [badTriadMass, badTriadMassNum, hempty, Finset.sum_empty, zero_div] at hbad
    linarith
  have hstep : δ ^ 3 * badTriadMassNum H κ δ
      < ∑ P : Fin 3 → Fin K,
          ∑ Q ∈ Finset.univ.filter fun Q : Fin 3 → Fin (cutBound 2 K) =>
            (fun i => cutRefineProj (Q i)) = P,
            ((polyadBlock (cutRefine κ W) Q).card : ℝ)
              * (densityOn (polyadBlock (cutRefine κ W) Q) (triadObs H)
                  - densityOn (polyadBlock κ P) (triadObs H)) ^ 2 := by
    rw [badTriadMassNum, Finset.mul_sum]
    refine lt_of_lt_of_le (Finset.sum_lt_sum_of_nonempty hne fun P hP => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun P _ _ => Finset.sum_nonneg fun Q _ =>
          mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rw [Finset.mem_filter] at hP
    obtain ⟨w, hw⟩ := badWitnessFamily_spec hP.2
    exact local_variance_gain hδ W w hw
  have h1 : δ ^ 3 * badTriadMassNum H κ δ
      < polyadEnergyNum (cutRefine κ W) (triadObs H)
        - polyadEnergyNum κ (triadObs H) := by
    rw [hvar]
    exact hstep
  -- Normalize.
  have h2 : δ ^ 4 < (δ ^ 3 * badTriadMassNum H κ δ) / (Fintype.card α : ℝ) ^ 3 := by
    rw [mul_div_assoc, show δ ^ 4 = δ ^ 3 * δ from by ring]
    refine mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [badTriadMass] at hbad
    exact hbad
  calc δ ^ 4
      < (δ ^ 3 * badTriadMassNum H κ δ) / (Fintype.card α : ℝ) ^ 3 := h2
    _ ≤ (polyadEnergyNum (cutRefine κ W) (triadObs H)
          - polyadEnergyNum κ (triadObs H)) / (Fintype.card α : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right h1.le hV.le
    _ = polyadEnergy (cutRefine κ W) (triadObs H) - polyadEnergy κ (triadObs H) := by
        rw [polyadEnergy, polyadEnergy, sub_div]

/-! ### Bounded iteration and the weak summit -/

/-- The color budget of `t` rounds of simultaneous cutting starting from `K`
colors: the exact frozen recurrence, iterating `cutBound 2`. -/
def triadRegularityBound : ℕ → ℕ → ℕ
  | 0, K => K
  | t + 1, K => triadRegularityBound t (cutBound 2 K)

theorem le_triadRegularityBound (t K : ℕ) : K ≤ triadRegularityBound t K := by
  induction t generalizing K with
  | zero => exact le_refl K
  | succ t ih =>
    refine le_trans ?_ (ih (cutBound 2 K))
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * 2 ^ (K ^ 3 * 3) := Nat.mul_le_mul_left K (Nat.one_le_two_pow)

/-- **The existential fuel theorem**: once the remaining energy budget is below
`t · δ⁴`, some coloring with at most `triadRegularityBound t K` colors has bad mass
at most `δ`. Each failing round strictly gains `δ⁴` of energy and multiplies the
colors by at most one `cutBound 2` step. -/
theorem exists_goodColoring_of_fuel {H : UniformHypergraph 3 α} {δ : ℝ} (hδ : 0 < δ)
    (t : ℕ) (K : ℕ) (κ : RSet 2 α → Fin K)
    (hbudget : 1 - polyadEnergy κ (triadObs H) ≤ (t : ℝ) * δ ^ 4) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadRegularityBound t K ∧ badTriadMass H κ' δ ≤ δ := by
  induction t generalizing K κ with
  | zero =>
    refine ⟨K, κ, le_refl _, ?_⟩
    by_contra hbad
    rw [not_le] at hbad
    have hgain := polyadEnergy_cutRefine_gain hδ hbad
    have hle := polyadEnergy_le_one
      (cutRefine κ (badWitnessFamily H κ δ)) (triadObs H)
    have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
    rw [Nat.cast_zero, zero_mul] at hbudget
    linarith
  | succ t ih =>
    by_cases hgood : badTriadMass H κ δ ≤ δ
    · exact ⟨K, κ, le_triadRegularityBound (t + 1) K, hgood⟩
    · rw [not_le] at hgood
      have hgain := polyadEnergy_cutRefine_gain hδ hgood
      refine ih (cutBound 2 K) (cutRefine κ (badWitnessFamily H κ δ)) ?_
      rw [Nat.cast_succ] at hbudget
      linarith

/-- The iteration fuel: `⌈1/δ⁴⌉₊` rounds suffice from any starting energy. -/
noncomputable def triadFuel (δ : ℝ) : ℕ := ⌈1 / δ ^ 4⌉₊

/-- The host-independent color bound of the weak summit: `triadFuel δ` rounds of
`cutBound 2`, starting from the trivial `1`-coloring. -/
noncomputable def triadBound (δ : ℝ) : ℕ := triadRegularityBound (triadFuel δ) 1

/-- **The weak triadic regularization summit**: every 3-uniform hypergraph admits a
pair coloring with at most `triadBound δ` colors whose bad keys carry at most a `δ`
fraction of the ordered triple mass. A precursor to, not a formalization of, the
Rödl–Schacht regular-partition theorem (see the module docstring and the design
freeze). -/
theorem exists_goodColoring (H : UniformHypergraph 3 α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadBound δ ∧ badTriadMass H κ' δ ≤ δ := by
  refine exists_goodColoring_of_fuel hδ (triadFuel δ) 1 (fun _ => 0) ?_
  have hE := polyadEnergy_nonneg (fun _ : RSet 2 α => (0 : Fin 1)) (triadObs H)
  have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
  have hceil : 1 / δ ^ 4 ≤ (triadFuel δ : ℝ) := Nat.le_ceil _
  calc 1 - polyadEnergy (fun _ : RSet 2 α => (0 : Fin 1)) (triadObs H)
      ≤ 1 := by linarith
    _ = (1 / δ ^ 4) * δ ^ 4 := by field_simp
    _ ≤ (triadFuel δ : ℝ) * δ ^ 4 := mul_le_mul_of_nonneg_right hceil hδ4.le

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level instance of the global increment at concrete types.
example (H : UniformHypergraph 3 (Fin 5)) (κ : RSet 2 (Fin 5) → Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hbad : δ < badTriadMass H κ δ) :
    δ ^ 4 < polyadEnergy (cutRefine κ (badWitnessFamily H κ δ)) (triadObs H)
        - polyadEnergy κ (triadObs H) :=
  polyadEnergy_cutRefine_gain hδ hbad

-- Contrapositive sanity: for the empty hypergraph the bad mass is 0, so the
-- increment hypothesis forces δ < 0 — the iteration stops immediately on
-- already-regular colorings.
example (δ : ℝ) (hδ : 0 < δ)
    (h : δ < badTriadMass (empty 3 (Fin 3))
      (fun _ : RSet 2 (Fin 3) => (0 : Fin 1)) δ) :
    False := by
  classical
  have hobs : ∀ S : Finset (Fin 3 → Fin 3),
      densityOn S (triadObs (empty 3 (Fin 3))) = 0 := by
    intro S
    rw [densityOn, Finset.filter_false_of_mem, Finset.card_empty]
    · norm_num
    · intro v _
      exact Finset.notMem_empty _
  have hgood : ∀ key : Fin 3 → Fin 1,
      ¬ IsBadTriad (empty 3 (Fin 3)) (fun _ => (0 : Fin 1)) δ key := by
    intro key
    rw [IsBadTriad, not_not]
    intro P _
    rw [hobs, hobs, sub_zero, abs_zero]
    exact hδ.le
  rw [badTriadMass, badTriadMassNum,
    Finset.filter_false_of_mem fun key _ => hgood key, Finset.sum_empty,
    zero_div] at h
  linarith

-- The frozen recurrence, numerically: one round from a single color costs
-- cutBound 2 1 = 2^3 = 8 colors.
example : triadRegularityBound 1 1 = 8 := by
  rw [triadRegularityBound, triadRegularityBound]
  norm_num

-- The color budget only grows along rounds (instance of the general bound).
example : (5 : ℕ) ≤ triadRegularityBound 3 5 := le_triadRegularityBound 3 5

-- The weak summit at concrete types, statement level.
example (H : UniformHypergraph 3 (Fin 6)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 2 (Fin 6) → Fin K'),
      K' ≤ triadBound δ ∧ badTriadMass H κ' δ ≤ δ :=
  exists_goodColoring H hδ

end Tests

end RegularityLemmata
