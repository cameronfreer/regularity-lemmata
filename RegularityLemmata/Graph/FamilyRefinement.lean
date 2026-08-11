/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.FamilyRegularity
import RegularityLemmata.Graph.Regularity

/-!
# Exact-refining finite-family regularity

The ordinary (non-equitable) family summit: from an **arbitrary** seed partition, an
`ε`-regular **exact refinement** for every relation of a finite directed family, with a
host-independent part bound.

This is the family analogue of `exists_regular_refinement`, and it is the prerequisite the
generic finite-family *strong* witness needs. The equitable family summit
(`exists_familyRegular_equipartition`, `Graph/EquitableFamilyRegularity.lean`) cannot serve that
role: it constructs its own starting equipartition and so exposes no `Q ≤ P₀` for a user-supplied
seed, and its increment machinery requires equitability of the seed, which an arbitrary partition
does not have. Exact refinement and equitability do not compose for free — that tension is exactly
what keeps equitable *strong* regularity deferred (`ARCHITECTURE.md`). This file takes the
refinement side and drops equitability entirely.

The argument is `regularity_iterate` with the ceiling raised from `1` to `#ι`: at a non-regular
stage some relation `k` offends, its own weak step gains `ε⁵` (`exists_refinement_energy_increment`),
and the gain lifts to the family energy because every other summand is refinement-monotone
(`familyEnergy_add_le_of_component`). Since `familyEnergy ≤ K` (`familyEnergy_le_card`), at most
`⌈K/ε⁵⌉` steps can fire — the fuel is linear in the family size, matching the ceiling.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)] {ε : ℝ}

/-- **Fuel-parametrized family iteration.** From family energy within `t · ε⁵` of the ceiling
`K`, `t` weak steps reach an `ε`-family-regular exact refinement. -/
theorem familyRegularity_refinement_iterate (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s), (K : ℝ) - (t : ℝ) * ε ^ 5 ≤ familyEnergy Rk P →
      ∃ Q : Finpartition s, Q ≤ P ∧ IsFamilyRegular Rk ε Q ∧
        Q.parts.card ≤ regularityBound t P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, ?_, le_regularityBound 0 _⟩
    by_contra hcon
    rw [IsFamilyRegular] at hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := hcon
    rw [IsRegularPartition, not_le] at hk
    obtain ⟨Q, hQP, hinc, _⟩ := exists_refinement_energy_increment (Rk k) P hε hk
    have h1 : familyEnergy Rk Q ≤ (K : ℝ) := familyEnergy_le_card
    have h2 := familyEnergy_add_le_of_component hQP k hinc
    have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hbudget
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : IsFamilyRegular Rk ε P
    · exact ⟨P, le_rfl, hreg, le_regularityBound _ _⟩
    · rw [IsFamilyRegular] at hreg
      push Not at hreg
      obtain ⟨k, hk⟩ := hreg
      rw [IsRegularPartition, not_le] at hk
      obtain ⟨P', hP'P, hinc, hcard'⟩ := exists_refinement_energy_increment (Rk k) P hε hk
      have hbudget' : (K : ℝ) - (t : ℝ) * ε ^ 5 ≤ familyEnergy Rk P' := by
        have h2 := familyEnergy_add_le_of_component hP'P k hinc
        push_cast at hbudget
        linarith
      obtain ⟨Q, hQP', hQreg, hQcard⟩ := IH P' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQreg, ?_⟩
      calc Q.parts.card ≤ regularityBound t P'.parts.card := hQcard
        _ ≤ regularityBound t (P.parts.card * 2 ^ (2 * P.parts.card)) :=
            regularityBound_mono t hcard'
        _ = regularityBound (t + 1) P.parts.card := by simp only [regularityBound]

/-- **Exact-refining finite-family regularity.** Every partition has an `ε`-family-regular
exact refinement, with the host-independent part bound `regularityBound ⌈K/ε⁵⌉ #P.parts`.

No equitability, no symmetry, and no host-size hypothesis: the seed is arbitrary and the
conclusion refines it. The fuel `⌈K/ε⁵⌉` is linear in the family size because the family energy
ceiling is `K`, not `1`. -/
theorem exists_familyRegular_refinement (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsFamilyRegular Rk ε Q ∧
      Q.parts.card ≤ regularityBound ⌈(K : ℝ) / ε ^ 5⌉₊ P.parts.card := by
  refine familyRegularity_refinement_iterate hε _ P ?_
  have h0 : (0 : ℝ) ≤ familyEnergy Rk P := familyEnergy_nonneg
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have ht : (K : ℝ) ≤ (⌈(K : ℝ) / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := by
    calc (K : ℝ) = (K : ℝ) / ε ^ 5 * ε ^ 5 := by field_simp
      _ ≤ (⌈(K : ℝ) / ε ^ 5⌉₊ : ℝ) * ε ^ 5 :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε5.le
  linarith

/-! ### Endpoints -/

/-- **The empty-family endpoint.** No relations, no work: the seed itself is returned, and the
fuel is `0`. -/
theorem exists_familyRegular_refinement_zero (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (P : Finpartition s) (_hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsFamilyRegular Rk ε Q ∧ Q.parts.card ≤ P.parts.card :=
  ⟨P, le_rfl, isFamilyRegular_zero Rk, le_rfl⟩

/-- **The singleton endpoint.** One relation recovers the single-relation exact-refining
summit's shape. -/
theorem exists_familyRegular_refinement_single (R : α → α → Prop) [DecidableRel R]
    (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsRegularPartition R ε Q ∧
      Q.parts.card ≤ regularityBound ⌈(1 : ℝ) / ε ^ 5⌉₊ P.parts.card := by
  obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
    exists_familyRegular_refinement (fun _ : Fin 1 => R) P hε
  refine ⟨Q, hQP, isFamilyRegular_single.mp hQreg, ?_⟩
  simpa using hQcard

/-! ### Tests -/

-- A family of repeated copies of one relation still terminates: the ceiling argument does
-- not secretly assume the relations are distinct.
example (R : α → α → Prop) [DecidableRel R] (P : Finpartition s) (hε : 0 < ε) (m : ℕ) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsFamilyRegular (fun _ : Fin m => R) ε Q ∧
      Q.parts.card ≤ regularityBound ⌈(m : ℝ) / ε ^ 5⌉₊ P.parts.card :=
  exists_familyRegular_refinement _ P hε

end RegularityLemmata
