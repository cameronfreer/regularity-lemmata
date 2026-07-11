/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Atomise
import RegularityLemmata.Graph.Increment
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The global energy increment and weak regularity

Summing the per-pair witness bridge over the bad pairs (and plain refinement
monotonicity over the good ones): a refinement resolving every bad pair's witness gains
`ε⁴ · badMassNum` of un-normalized energy. When the normalized bad mass exceeds `ε`,
the witness atomisation therefore raises the normalized energy by at least `ε⁵`, with
the part count multiplying by at most `2^(2k)`.

Since the energy lives in `[0, 1]`, at most `⌈1/ε⁵⌉` rounds reach a weakly `ε`-regular
refinement, with the explicit part-count bound `weakBound`.

The bounded-iteration architecture follows mathlib's proof of Szemerédi's regularity
lemma (`Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma` and `….Increment`; see
Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022),
adapted from symmetric simple graphs with equipartitions to an arbitrary directed
relation with mass-weighted energy. Mathlib's global increment is `ε⁵/4` (its constant
absorbs equitabilisation losses); the mass-weighted, non-equitable refinement here
gives the clean `ε⁵`. For the pen-and-paper argument see Y. Zhao, *Graph Theory and
Additive Combinatorics*, ch. 2 (energy boost and iteration).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] {ε : ℝ}

/-- **Global increment, un-normalized.** A refinement resolving every bad pair's
witness gains at least `ε⁴ · badMassNum` of energy. -/
theorem energyNum_increment_of_badMassNum {P P' : Finpartition s} (hP' : P' ≤ P)
    (hε : 0 < ε)
    (hwit : ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPair R ε C D →
      ∃ w : NonuniformWitness R C D ε, IsPartUnion P' w.left ∧ IsPartUnion P' w.right) :
    energyNum R P + ε ^ 4 * badMassNum R ε P ≤ energyNum R P' := by
  classical
  have hpp : ∀ uv ∈ P.parts ×ˢ P.parts,
      blockEnergy R uv.1 uv.2
        + (if IsBadPair R ε uv.1 uv.2 then ε ^ 4 * ((uv.1.card : ℝ) * (uv.2.card : ℝ))
          else 0)
      ≤ ∑ C' ∈ P'.parts.filter (· ⊆ uv.1), ∑ D' ∈ P'.parts.filter (· ⊆ uv.2),
          blockEnergy R C' D' := by
    intro uv huv
    rw [Finset.mem_product] at huv
    obtain ⟨hC, hD⟩ := huv
    by_cases hbad : IsBadPair R ε uv.1 uv.2
    · rw [if_pos hbad, ← mul_assoc]
      obtain ⟨w, hlU, hrU⟩ := hwit uv.1 hC uv.2 hD hbad
      exact blockEnergy_increment_refined R hε w
        (isPartUnion_of_mem_of_le hP' hC) (isPartUnion_of_mem_of_le hP' hD) hlU hrU
    · rw [if_neg hbad, add_zero]
      exact blockEnergy_le_sum_refined hP' R hC hD
  calc energyNum R P + ε ^ 4 * badMassNum R ε P
      = ∑ uv ∈ P.parts ×ˢ P.parts, (blockEnergy R uv.1 uv.2
          + (if IsBadPair R ε uv.1 uv.2 then ε ^ 4 * ((uv.1.card : ℝ) * (uv.2.card : ℝ))
            else 0)) := by
        unfold energyNum badMassNum
        rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
    _ ≤ ∑ uv ∈ P.parts ×ˢ P.parts, ∑ C' ∈ P'.parts.filter (· ⊆ uv.1),
          ∑ D' ∈ P'.parts.filter (· ⊆ uv.2), blockEnergy R C' D' := Finset.sum_le_sum hpp
    _ = energyNum R P' := by
        rw [Finset.sum_product]
        exact energyNum_eq_sum_refined R hP'

/-- **Global increment, normalized.** If the normalized bad mass exceeds `ε`, a
witness-resolving refinement raises the normalized energy by at least `ε⁵`. (The
hypothesis `ε < badMass` with `0 < ε` forces a nonempty ground set — no separate
`Nonempty` assumption.) -/
theorem energy_increment_of_badMass {P P' : Finpartition s} (hP' : P' ≤ P) (hε : 0 < ε)
    (hwit : ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPair R ε C D →
      ∃ w : NonuniformWitness R C D ε, IsPartUnion P' w.left ∧ IsPartUnion P' w.right)
    (hbm : ε < badMass R ε P) :
    energy R P + ε ^ 5 ≤ energy R P' := by
  have hs : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
    by_contra hzero
    push Not at hzero
    have h0 : ((s.card : ℝ)) ^ 2 = 0 := le_antisymm hzero (by positivity)
    rw [badMass, h0, div_zero] at hbm
    linarith
  have hmain := energyNum_increment_of_badMassNum R hP' hε hwit
  have hbmN : ε * (s.card : ℝ) ^ 2 < badMassNum R ε P := by
    rw [badMass, lt_div_iff₀ hs] at hbm
    linarith
  have hgain : ε ^ 5 * (s.card : ℝ) ^ 2 ≤ ε ^ 4 * badMassNum R ε P := by
    have hrw : ε ^ 5 * (s.card : ℝ) ^ 2 = ε ^ 4 * (ε * (s.card : ℝ) ^ 2) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hbmN.le (by positivity)
  have key : energyNum R P + ε ^ 5 * (s.card : ℝ) ^ 2 ≤ energyNum R P' := by
    linarith
  unfold energy
  rw [div_add' _ _ _ hs.ne']
  gcongr

/-- **The weak step.** A partition with normalized bad mass exceeding `ε` has a
refinement gaining `ε⁵` of energy, with part count at most `k · 2^(2k)`. -/
theorem exists_refinement_energy_increment (P : Finpartition s) (hε : 0 < ε)
    (hbm : ε < badMass R ε P) :
    ∃ Q : Finpartition s, Q ≤ P ∧ energy R P + ε ^ 5 ≤ energy R Q ∧
      Q.parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) :=
  ⟨witnessRefinement R ε P, witnessRefinement_le R ε P,
    energy_increment_of_badMass R (witnessRefinement_le R ε P) hε
      (witnessRefinement_resolves R ε P) hbm,
    witnessRefinement_parts_card_le R ε P⟩

/-! ### Bounded iteration -/

/-- Part-count bound after `t` weak steps from `m` parts. -/
def weakBound : ℕ → ℕ → ℕ
  | 0, m => m
  | t + 1, m => weakBound t (m * 2 ^ (2 * m))

theorem le_weakBound (t m : ℕ) : m ≤ weakBound t m := by
  induction t generalizing m with
  | zero => simp [weakBound]
  | succ t IH =>
    rw [weakBound]
    exact le_trans (Nat.le_mul_of_pos_right m (Nat.pow_pos (by norm_num))) (IH _)

theorem weakBound_mono (t : ℕ) {m m' : ℕ} (h : m ≤ m') : weakBound t m ≤ weakBound t m' := by
  induction t generalizing m m' with
  | zero => simpa [weakBound] using h
  | succ t IH =>
    rw [weakBound, weakBound]
    exact IH (Nat.mul_le_mul h (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **Fuel-parametrized iteration.** From energy within `t · ε⁵` of the ceiling `1`,
`t` weak steps reach a weakly `ε`-regular refinement. -/
theorem weak_regularity_iterate (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * ε ^ 5 ≤ energy R P →
      ∃ Q : Finpartition s, Q ≤ P ∧ IsWeakRegular R ε Q ∧
        Q.parts.card ≤ weakBound t P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, ?_, le_weakBound 0 _⟩
    by_contra hcon
    rw [IsWeakRegular, not_le] at hcon
    obtain ⟨Q, _, hinc, _⟩ := exists_refinement_energy_increment R P hε hcon
    have h1 : energy R Q ≤ 1 := energy_le_one R
    have h2 : (1 : ℝ) ≤ energy R P := by simpa using hbudget
    have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : IsWeakRegular R ε P
    · exact ⟨P, le_rfl, hreg, le_weakBound _ _⟩
    · rw [IsWeakRegular, not_le] at hreg
      obtain ⟨P', hP'P, hinc, hcard'⟩ := exists_refinement_energy_increment R P hε hreg
      have hbudget' : 1 - (t : ℝ) * ε ^ 5 ≤ energy R P' := by
        have hexp : ((t : ℝ) + 1) * ε ^ 5 = (t : ℝ) * ε ^ 5 + ε ^ 5 := by ring
        push_cast at hbudget
        rw [hexp] at hbudget
        linarith
      obtain ⟨Q, hQP', hQreg, hQcard⟩ := IH P' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQreg, ?_⟩
      calc Q.parts.card ≤ weakBound t P'.parts.card := hQcard
        _ ≤ weakBound t (P.parts.card * 2 ^ (2 * P.parts.card)) := weakBound_mono t hcard'
        _ = weakBound (t + 1) P.parts.card := by simp only [weakBound]

/-- **Weak regularity.** Every partition has a weakly `ε`-regular refinement with the
explicit host-independent part-count bound `weakBound ⌈1/ε⁵⌉ k`. -/
theorem exists_weak_regular_refinement (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsWeakRegular R ε Q ∧
      Q.parts.card ≤ weakBound ⌈1 / ε ^ 5⌉₊ P.parts.card := by
  refine weak_regularity_iterate R hε _ P ?_
  have h0 : (0 : ℝ) ≤ energy R P := energy_nonneg R
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := by
    calc (1 : ℝ) = 1 / ε ^ 5 * ε ^ 5 := by field_simp
      _ ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε5.le
  linarith

/-! ### Tests and adversarial examples -/

-- weakBound computed: one step from 2 parts allows at most 2·2⁴ = 32.
example : weakBound 1 2 = 32 := by decide

example : weakBound 0 5 = 5 := by decide

-- The bound is host-independent: it mentions only ε and the initial part count.
example (P : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    ∃ Q : Finpartition ({0, 1, 2} : Finset (Fin 3)), Q ≤ P ∧
      IsWeakRegular (fun a b : Fin 3 => a < b) (1 / 2) Q ∧
      Q.parts.card ≤ weakBound ⌈1 / (1 / 2 : ℝ) ^ 5⌉₊ P.parts.card :=
  exists_weak_regular_refinement _ P (by norm_num)

end RegularityLemmata
