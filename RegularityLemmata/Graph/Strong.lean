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

/-! ### The operational meaning of the energy gap -/

/-- The (un-normalized) refinement variance: the mass-weighted squared density shifts
of refined sub-blocks against their coarse parents. -/
noncomputable def refinementVarianceNum (Q P : Finpartition s) : ℝ :=
  ∑ pd ∈ P.parts ×ˢ P.parts,
    ∑ p ∈ (Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2)),
      ((p.1.card : ℝ) * p.2.card)
        * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2

theorem refinementVarianceNum_nonneg {Q P : Finpartition s} :
    0 ≤ refinementVarianceNum R Q P :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The parallel-axis identity, summed: the refinement variance is exactly the
un-normalized energy gain. -/
theorem refinementVarianceNum_eq {Q P : Finpartition s} (hQP : Q ≤ P) :
    refinementVarianceNum R Q P = energyNum R Q - energyNum R P := by
  classical
  have hpd : ∀ S : Finset α,
      (↑(Q.parts.filter (· ⊆ S)) : Set (Finset α)).PairwiseDisjoint id := fun S =>
    Q.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  have hper : ∀ pd ∈ P.parts ×ˢ P.parts,
      (∑ p ∈ (Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2)),
        ((p.1.card : ℝ) * p.2.card)
          * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2)
      = (∑ p ∈ (Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2)),
          blockEnergy R p.1 p.2) - blockEnergy R pd.1 pd.2 := by
    rintro ⟨C, D⟩ hpd'
    rw [Finset.mem_product] at hpd'
    exact variance_eq_sum_blockEnergy_sub R _ _ (hpd C)
      (biUnion_filter_subset_eq hQP hpd'.1) (hpd D)
      (biUnion_filter_subset_eq hQP hpd'.2)
  rw [refinementVarianceNum, Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
  congr 1
  rw [← energyNum_eq_sum_refined R hQP, Finset.sum_product]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.sum_product]

/-- **L² density-shift bound.** The strong witness's energy gap bounds the refinement
variance of the fine partition against the coarse one by `δ·|s|²`. -/
theorem StrongWitness.refinementVarianceNum_le {E : ErrorSchedule} {δ : ℝ}
    {P₀ : Finpartition s} (w : StrongWitness R E δ P₀) :
    refinementVarianceNum R w.fine w.coarse ≤ δ * (s.card : ℝ) ^ 2 := by
  rw [refinementVarianceNum_eq R w.fine_le]
  have hgap := w.energy_gap
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · have hz : ∀ P : Finpartition s, energyNum R P = 0 := by
      intro P
      have hparts : P.parts = ∅ := by
        rw [← Finset.subset_empty]
        intro C hC
        exfalso
        obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hC
        have := P.le hC hx
        rw [Finset.card_eq_zero.mp h0] at this
        exact absurd this (Finset.notMem_empty x)
      rw [energyNum, hparts]
      simp
    rw [hz, hz, h0]
    norm_num
  · have hs2 : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hpos
      positivity
    have h1 : energyNum R w.fine = energy R w.fine * (s.card : ℝ) ^ 2 := by
      rw [energy, div_mul_cancel₀]
      exact hs2.ne'
    have h2 : energyNum R w.coarse = energy R w.coarse * (s.card : ℝ) ^ 2 := by
      rw [energy, div_mul_cancel₀]
      exact hs2.ne'
    rw [h1, h2]
    nlinarith [hgap, hs2]

/-- **Exceptional-mass (Markov) consequence.** The mass of refined rectangles whose
density shifts from their coarse parent by more than `η` is at most `(δ/η²)·|s|²` —
the bridge a strong-witness counting theorem consumes. -/
theorem StrongWitness.deviant_mass_le {E : ErrorSchedule} {δ : ℝ}
    {P₀ : Finpartition s} (w : StrongWitness R E δ P₀) {η : ℝ} (hη : 0 < η) :
    ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
  classical
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have key : (∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)) * η ^ 2
      ≤ refinementVarianceNum R w.fine w.coarse := by
    rw [Finset.sum_mul, refinementVarianceNum]
    refine Finset.sum_le_sum fun pd _ => ?_
    rw [Finset.sum_mul]
    calc ∑ p ∈ (((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
            (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|)),
          ((p.1.card : ℝ) * p.2.card) * η ^ 2
        ≤ ∑ p ∈ (((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
            (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|)),
            ((p.1.card : ℝ) * p.2.card)
              * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          have hdev := hp.2
          have hsq : η ^ 2 ≤ (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 := by
            nlinarith [sq_abs (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2),
              abs_nonneg (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2)]
          have hm : (0 : ℝ) ≤ (p.1.card : ℝ) * p.2.card := by positivity
          exact mul_le_mul_of_nonneg_left hsq hm
      _ ≤ ∑ p ∈ (w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2)),
            ((p.1.card : ℝ) * p.2.card)
              * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun p _ _ => by positivity
  have hvar := w.refinementVarianceNum_le (R := R)
  rw [← le_div_iff₀ hη2] at key
  calc _ ≤ refinementVarianceNum R w.fine w.coarse / η ^ 2 := key
    _ ≤ δ * (s.card : ℝ) ^ 2 / η ^ 2 := (div_le_div_iff_of_pos_right hη2).mpr hvar
    _ = δ / η ^ 2 * (s.card : ℝ) ^ 2 := by ring

end RegularityLemmata
