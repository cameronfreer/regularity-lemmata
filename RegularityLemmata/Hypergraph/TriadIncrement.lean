/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Triad
import RegularityLemmata.Hypergraph.PolyadWitness

/-!
# The global energy increment

Phase 7 unit 4/5 capstone (design freeze in `ARCHITECTURE.md`): when the bad keys of
a pair coloring carry more than a `δ` fraction of the triple mass, one simultaneous
cut round strictly gains more than `δ⁴` of normalized energy
(`polyadEnergy_cutRefine_gain`).

The witness family is canonical (`badWitnessFamily`): an actual `DiscWitness` on
each bad key (classical choice from `exists_discWitness`), the empty face family on
good keys — the cut budget of `cutBound 2 K = K·2^(3K³)` safely counts all possible
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

/-- The canonical simultaneous witness family: an actual witness on each bad key,
the empty face family elsewhere. -/
noncomputable def badWitnessFamily (H : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (δ : ℝ) :
    (Fin 3 → Fin K) → Fin 3 → Finset (RSet 2 α) := by
  classical
  exact fun key =>
    if h : IsBadTriad H κ δ key then (exists_discWitness h).some.faces
    else fun _ => ∅

/-- On a bad key, the canonical family is an actual witness's face system. -/
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

end Tests

end RegularityLemmata
