/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Regularity

/-!
# Strong regularity via energy-gap stopping

A **strong witness** for a relation `R`, an error schedule `E`, and a gap `δ` consists
of a coarse partition and a fine refinement that is `E(#coarse)`-regular while
gaining at most `δ` of energy over the coarse partition — so the fine partition is
regular *at a tolerance chosen against the coarse complexity*, and the coarse partition
already captures the energy. Error schedules are bundled with their positivity
(`ErrorSchedule`); no monotonicity is required for existence.

Existence (`exists_strongWitness`) iterates the partition regularity theorem: if the fine
refinement gains more than `δ`, restart from it; energy lives in `[0, 1]`, so at most
`⌈1/δ⌉` restarts occur. Part counts are bounded by iterating `monoStepBound`, a
monotone majorant of the one-round bound `regularityBound ⌈1/E(k)⁵⌉ k` (monotonicity is what
lets early stopping compose with the closed-form bound). The bound is host-independent:
it depends only on `E`, `δ`, and the initial part count.

The architecture is the standard strong-regularity iteration (T. Tao, *Szemerédi's
regularity lemma revisited*, Contrib. Discrete Math. 1 (2006); see also Y. Zhao, *Graph
Theory and Additive Combinatorics*, ch. 2), run on the library's mass-weighted energy.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- A positive error schedule: a tolerance for each coarse complexity. -/
structure ErrorSchedule where
  /-- The tolerance assigned to a partition with `k` parts. -/
  toFun : ℕ → ℝ
  /-- Every tolerance is positive. -/
  pos : ∀ k, 0 < toFun k

instance : CoeFun ErrorSchedule (fun _ => ℕ → ℝ) := ⟨ErrorSchedule.toFun⟩

variable (R : α → α → Prop) [DecidableRel R]

/-- A strong regularity witness against a starting partition `P₀`: a coarse refinement
of `P₀` and a fine refinement of it, regular at the schedule's tolerance for the
coarse complexity, with an energy gap of at most `δ`. -/
structure StrongWitness (E : ErrorSchedule) (δ : ℝ) (P₀ : Finpartition s) where
  /-- The coarse partition. -/
  coarse : Finpartition s
  /-- The fine partition. -/
  fine : Finpartition s
  coarse_le : coarse ≤ P₀
  fine_le : fine ≤ coarse
  /-- The fine partition is regular at the tolerance chosen against the
  coarse complexity. -/
  fine_regular : IsRegularPartition R (E coarse.parts.card) fine
  /-- The fine refinement gains at most `δ` of energy. -/
  energy_gap : energy R fine ≤ energy R coarse + δ

/-! ### The monotone step bound -/

/-- Monotone majorant of the one-round part-count bound
`k ↦ regularityBound ⌈1/E(k)⁵⌉ k`. -/
noncomputable def monoStepBound (E : ErrorSchedule) (m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup fun j => regularityBound ⌈1 / (E j) ^ 5⌉₊ j

theorem stepBound_le_monoStepBound (E : ErrorSchedule) (m : ℕ) :
    regularityBound ⌈1 / (E m) ^ 5⌉₊ m ≤ monoStepBound E m := by
  unfold monoStepBound
  exact Finset.le_sup (f := fun j => regularityBound ⌈1 / (E j) ^ 5⌉₊ j)
    (Finset.self_mem_range_succ m)

theorem le_monoStepBound (E : ErrorSchedule) (m : ℕ) : m ≤ monoStepBound E m :=
  le_trans (le_regularityBound _ _) (stepBound_le_monoStepBound E m)

theorem monoStepBound_mono (E : ErrorSchedule) {m m' : ℕ} (h : m ≤ m') :
    monoStepBound E m ≤ monoStepBound E m' := by
  unfold monoStepBound
  exact Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

theorem monoStepBound_iterate_mono (E : ErrorSchedule) (i : ℕ) {m m' : ℕ} (h : m ≤ m') :
    (monoStepBound E)^[i] m ≤ (monoStepBound E)^[i] m' := by
  induction i generalizing m m' with
  | zero => simpa using h
  | succ i IH =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact IH (monoStepBound_mono E h)

theorem le_monoStepBound_iterate (E : ErrorSchedule) (i : ℕ) (m : ℕ) :
    m ≤ (monoStepBound E)^[i] m := by
  induction i with
  | zero => simp
  | succ i IH =>
    rw [Function.iterate_succ_apply]
    exact le_trans IH (monoStepBound_iterate_mono E i (le_monoStepBound E m))

theorem monoStepBound_iterate_le_iterate (E : ErrorSchedule) {i j : ℕ} (hij : i ≤ j)
    (m : ℕ) : (monoStepBound E)^[i] m ≤ (monoStepBound E)^[j] m := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ j IH =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · refine le_trans (IH (by omega)) ?_
      rw [Function.iterate_succ_apply]
      exact monoStepBound_iterate_mono E j (le_monoStepBound E m)
    · have hi : i = j + 1 := by omega
      rw [hi]

/-! ### Existence by energy-gap stopping -/

/-- Fuel-parametrized strong iteration: from energy within `t · δ` of the ceiling,
`t` restarts suffice. -/
theorem strong_iterate (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * δ ≤ energy R P →
      ∃ w : StrongWitness R E δ P,
        w.coarse.parts.card ≤ (monoStepBound E)^[t] P.parts.card ∧
        w.fine.parts.card ≤ (monoStepBound E)^[t + 1] P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_regular_refinement R P (E.pos P.parts.card)
    have hgap : energy R Q ≤ energy R P + δ := by
      have h1 : energy R Q ≤ 1 := energy_le_one R
      have h2 : (1 : ℝ) ≤ energy R P := by simpa using hbudget
      linarith
    refine ⟨⟨P, Q, le_rfl, hQP, hQreg, hgap⟩, by simp, ?_⟩
    calc Q.parts.card ≤ regularityBound ⌈1 / (E P.parts.card) ^ 5⌉₊ P.parts.card := hQcard
      _ ≤ monoStepBound E P.parts.card := stepBound_le_monoStepBound E _
      _ = (monoStepBound E)^[0 + 1] P.parts.card := by simp
  | succ t IH =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_regular_refinement R P (E.pos P.parts.card)
    have hQmono : Q.parts.card ≤ monoStepBound E P.parts.card :=
      le_trans hQcard (stepBound_le_monoStepBound E _)
    by_cases hgap : energy R Q ≤ energy R P + δ
    · refine ⟨⟨P, Q, le_rfl, hQP, hQreg, hgap⟩,
        le_monoStepBound_iterate E _ _, ?_⟩
      calc Q.parts.card ≤ monoStepBound E P.parts.card := hQmono
        _ = (monoStepBound E)^[1] P.parts.card := rfl
        _ ≤ (monoStepBound E)^[t + 1 + 1] P.parts.card :=
            monoStepBound_iterate_le_iterate E (by omega) _
    · rw [not_le] at hgap
      have hbudget' : 1 - (t : ℝ) * δ ≤ energy R Q := by
        push_cast at hbudget
        nlinarith [hgap, hbudget]
      obtain ⟨w, hwc, hwf⟩ := IH Q hbudget'
      refine ⟨⟨w.coarse, w.fine, w.coarse_le.trans hQP, w.fine_le, w.fine_regular,
        w.energy_gap⟩, ?_, ?_⟩
      · calc w.coarse.parts.card ≤ (monoStepBound E)^[t] Q.parts.card := hwc
          _ ≤ (monoStepBound E)^[t] (monoStepBound E P.parts.card) :=
              monoStepBound_iterate_mono E t hQmono
          _ = (monoStepBound E)^[t + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm
      · calc w.fine.parts.card ≤ (monoStepBound E)^[t + 1] Q.parts.card := hwf
          _ ≤ (monoStepBound E)^[t + 1] (monoStepBound E P.parts.card) :=
              monoStepBound_iterate_mono E _ hQmono
          _ = (monoStepBound E)^[t + 1 + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm

/-- **Strong regularity.** Every starting partition admits a strong witness for any
positive error schedule and gap, with explicit host-independent part-count bounds. -/
theorem exists_strongWitness (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ)
    (P₀ : Finpartition s) :
    ∃ w : StrongWitness R E δ P₀,
      w.coarse.parts.card ≤ (monoStepBound E)^[⌈1 / δ⌉₊] P₀.parts.card ∧
      w.fine.parts.card ≤ (monoStepBound E)^[⌈1 / δ⌉₊ + 1] P₀.parts.card := by
  refine strong_iterate R E hδ _ P₀ ?_
  have h0 : (0 : ℝ) ≤ energy R P₀ := energy_nonneg R
  have ht : (1 : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
    calc (1 : ℝ) = 1 / δ * δ := by field_simp
      _ ≤ (⌈1 / δ⌉₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le
  linarith

/-! ### Tests and adversarial examples -/

-- A constant error schedule.
noncomputable example : ErrorSchedule := ⟨fun _ => 1 / 2, fun _ => by norm_num⟩

-- The monotone step bound dominates the identity and one weak round, computed.
example : (2 : ℕ) ≤ monoStepBound ⟨fun _ => 1, fun _ => one_pos⟩ 2 :=
  le_monoStepBound _ 2

-- Strong regularity instantiated on a tiny host with a constant schedule.
example (P₀ : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    ∃ w : StrongWitness (fun a b : Fin 3 => a < b)
        ⟨fun _ => 1 / 2, fun _ => by norm_num⟩ (1 / 2) P₀,
      w.coarse.parts.card
        ≤ (monoStepBound ⟨fun _ => 1 / 2, fun _ => by norm_num⟩)^[⌈(1 : ℝ) / (1 / 2)⌉₊]
            P₀.parts.card :=
  (exists_strongWitness _ _ (by norm_num) P₀).imp fun _ h => h.1

end RegularityLemmata
