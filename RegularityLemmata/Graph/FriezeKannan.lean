/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.CutNorm

/-!
# The finite Frieze–Kannan weak regularity lemma

The genuine finite Frieze–Kannan theorem (`frieze_kannan`): for every `ε > 0` there is
a partition with at most `4^(⌈1/ε²⌉ + 1)` parts whose stepped approximation is within
`ε·|s|²` of the true count on **every** rectangle — diagonal pairs handled
automatically, with the expected single-exponential bound.

The proof is the direct energy-increment iteration: if some rectangle `(A, B)` has
discrepancy exceeding `ε·|s|²`, refine every part by `A` and by `B`
(`refineByCuts`, at most `4·#P` parts) and gain `ε²` of energy
(`exists_refinement_energy_increment_of_cut_witness`); energy lives in `[0, 1]`, so at
most `⌈1/ε²⌉ + 1` rounds suffice. The gain is the parallel-axis variance identity plus
Cauchy–Schwarz, run here entirely in Engel form (`titu_finset` at both the per-pair
and the global level), avoiding square roots.

This ports the architecture of the author's graphon development — C. Freer, *Graphons
in Lean 4*, <https://github.com/cameronfreer/graphon>,
`Graphon/Regularity.lean` (`energy_increment_quantitative`: witness rectangle, double
split, conditional variance + Cauchy–Schwarz) — from measurable partitions of a
probability space to finite partitions with counting measure. Literature: A. Frieze
and R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
(1999).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s A B : Finset α} {ε : ℝ}
variable (R : α → α → Prop) [DecidableRel R]

/-! ### Double splitting by a cut witness -/

/-- Refine every part by the two test sets: each part is atomised by its traces of `A`
and `B`. -/
noncomputable def refineByCuts (P : Finpartition s) (A B : Finset α) : Finpartition s :=
  P.bind fun C _ => Finpartition.atomise C {C ∩ A, C ∩ B}

theorem refineByCuts_le (P : Finpartition s) (A B : Finset α) :
    refineByCuts P A B ≤ P := by
  intro b hb
  rw [refineByCuts, Finpartition.mem_bind] at hb
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, (Finpartition.atomise C _).le hb⟩

theorem refineByCuts_parts_card_le (P : Finpartition s) (A B : Finset α) :
    (refineByCuts P A B).parts.card ≤ 4 * P.parts.card := by
  rw [refineByCuts, Finpartition.card_bind]
  calc ∑ C ∈ P.parts.attach, (Finpartition.atomise C.1 {C.1 ∩ A, C.1 ∩ B}).parts.card
      ≤ ∑ _C ∈ P.parts.attach, 4 := by
        refine Finset.sum_le_sum fun C _ => ?_
        refine Finpartition.card_atomise_le.trans ?_
        calc 2 ^ ({C.1 ∩ A, C.1 ∩ B} : Finset (Finset α)).card
            ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num)
              ((Finset.card_insert_le _ _).trans (by norm_num))
          _ = 4 := by norm_num
    _ = P.parts.card * 4 := by rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]
    _ = 4 * P.parts.card := Nat.mul_comm _ _

/-- Atoms respect every member of the cutting family. -/
theorem atomise_subset_or_disjoint {C : Finset α} {F : Finset (Finset α)}
    {t : Finset α} (ht : t ∈ F) {u : Finset α}
    (hu : u ∈ (Finpartition.atomise C F).parts) : u ⊆ t ∨ Disjoint u t := by
  obtain ⟨_, Q, _, rfl⟩ := Finpartition.mem_atomise.mp hu
  by_cases hQt : t ∈ Q
  · left
    intro x hx
    rw [Finset.mem_filter] at hx
    exact (hx.2 t ht).mp hQt
  · right
    rw [Finset.disjoint_left]
    intro x hx hxt
    rw [Finset.mem_filter] at hx
    exact hQt ((hx.2 t ht).mpr hxt)

/-- Every part of the double split lies inside or outside each test set. -/
theorem refineByCuts_subset_or_disjoint {P : Finpartition s} {A B U : Finset α}
    (hU : U ∈ (refineByCuts P A B).parts) :
    (U ⊆ A ∨ Disjoint U A) ∧ (U ⊆ B ∨ Disjoint U B) := by
  rw [refineByCuts, Finpartition.mem_bind] at hU
  obtain ⟨C, hC, hU⟩ := hU
  have hUC : U ⊆ C := (Finpartition.atomise C _).le hU
  constructor
  · rcases atomise_subset_or_disjoint (Finset.mem_insert_self _ _) hU with h | h
    · exact Or.inl (h.trans Finset.inter_subset_right)
    · right
      rw [Finset.disjoint_left] at h ⊢
      exact fun x hx hxA => h hx (Finset.mem_inter.mpr ⟨hUC hx, hxA⟩)
  · rcases atomise_subset_or_disjoint
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hU with h | h
    · exact Or.inl (h.trans Finset.inter_subset_right)
    · right
      rw [Finset.disjoint_left] at h ⊢
      exact fun x hx hxB => h hx (Finset.mem_inter.mpr ⟨hUC hx, hxB⟩)

/-- The parts of a refinement inside a part `C` and inside a respected test set `T`
cover the trace `T ∩ C`. -/
theorem biUnion_filter_subset_inter {Q P : Finpartition s} (hQP : Q ≤ P) {T : Finset α}
    (hdich : ∀ U ∈ Q.parts, U ⊆ T ∨ Disjoint U T) {C : Finset α} (hC : C ∈ P.parts) :
    ((Q.parts.filter fun U => U ⊆ C ∧ U ⊆ T).biUnion id) = T ∩ C := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨U, hUf, hxU⟩ := hx
    rw [Finset.mem_filter] at hUf
    exact Finset.mem_inter.mpr ⟨hUf.2.2 hxU, hUf.2.1 hxU⟩
  · intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨U, hU, hxU⟩ := Q.exists_mem (P.le hC hx.2)
    obtain ⟨C', hC', hUC'⟩ := hQP hU
    have hCC' : C = C' := P.eq_of_mem_parts hC hC' hx.2 (hUC' hxU)
    have hUT : U ⊆ T := by
      rcases hdich U hU with h | h
      · exact h
      · exact absurd hx.1 (Finset.disjoint_left.mp h hxU)
    rw [Finset.mem_biUnion]
    exact ⟨U, Finset.mem_filter.mpr ⟨hU, hCC' ▸ hUC', hUT⟩, hxU⟩

/-! ### The Engel-form Cauchy–Schwarz helper -/

/-- Squared-sum bound from the Engel form: `(Σ a)² ≤ (Σ b) · V` whenever
`Σ a²/b ≤ V` with nonnegative `b` and the zero-denominator convention. -/
private theorem sq_sum_le_sum_mul {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {a b : ι → ℝ} {V : ℝ} (hb : ∀ i ∈ I, 0 ≤ b i)
    (hab : ∀ i ∈ I, b i = 0 → a i = 0) (hV : ∑ i ∈ I, a i ^ 2 / b i ≤ V) :
    (∑ i ∈ I, a i) ^ 2 ≤ (∑ i ∈ I, b i) * V := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg hb) with h0 | hpos
  · have hbz : ∀ i ∈ I, b i = 0 := by
      intro i hi
      by_contra hne
      have hbi : 0 < b i := lt_of_le_of_ne (hb i hi) (Ne.symm hne)
      have : 0 < ∑ j ∈ I, b j := Finset.sum_pos' hb ⟨i, hi, hbi⟩
      linarith [h0]
    rw [Finset.sum_eq_zero fun i hi => hab i hi (hbz i hi), ← h0]
    norm_num
  · have htitu := titu_finset a b I hb hab
    rw [div_le_iff₀ hpos] at htitu
    calc (∑ i ∈ I, a i) ^ 2 ≤ (∑ i ∈ I, a i ^ 2 / b i) * ∑ i ∈ I, b i := htitu
      _ ≤ V * ∑ i ∈ I, b i :=
          mul_le_mul_of_nonneg_right hV (le_of_lt hpos)
      _ = (∑ i ∈ I, b i) * V := mul_comm _ _

/-! ### The quantitative energy increment -/

set_option maxHeartbeats 1000000 in
/-- **FK energy increment.** A rectangle with cut discrepancy exceeding `ε·|s|²`
yields, by double splitting, a refinement with at most `4·#P` parts and an `ε²` energy
gain. -/
theorem exists_refinement_energy_increment_of_cut_witness {P : Finpartition s}
    (hA : A ⊆ s) (hB : B ⊆ s) (hε : 0 < ε)
    (hdev : ε * (s.card : ℝ) ^ 2 < |(pairCount R A B : ℝ) - steppedCount R P A B|) :
    ∃ Q : Finpartition s, Q ≤ P ∧ Q.parts.card ≤ 4 * P.parts.card ∧
      energy R P + ε ^ 2 ≤ energy R Q := by
  classical
  set Q := refineByCuts P A B with hQdef
  have hQP : Q ≤ P := refineByCuts_le P A B
  refine ⟨Q, hQP, refineByCuts_parts_card_le P A B, ?_⟩
  -- notation
  set fib : Finset α → Finset (Finset α) := fun C => Q.parts.filter (· ⊆ C) with hfib
  have hpd : ∀ S : Finset α, (↑(Q.parts.filter (· ⊆ S)) : Set (Finset α)).PairwiseDisjoint
      id := fun S => Q.supIndep.pairwiseDisjoint.subset
    (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  -- per-(C,D): weight, variance, and the selected discrepancy
  set W : Finset α × Finset α → ℝ := fun pd => ((pd.1.card : ℝ)) * pd.2.card with hW
  set V : Finset α × Finset α → ℝ := fun pd =>
    ∑ p ∈ fib pd.1 ×ˢ fib pd.2, ((p.1.card : ℝ) * p.2.card)
      * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 with hV
  set T : Finset α × Finset α → ℝ := fun pd =>
    (pairCount R (A ∩ pd.1) (B ∩ pd.2) : ℝ)
      - pairDensity R pd.1 pd.2 * ((A ∩ pd.1).card : ℝ) * ((B ∩ pd.2).card : ℝ) with hT
  have hV0 : ∀ pd, 0 ≤ V pd := fun pd => Finset.sum_nonneg fun p _ => by positivity
  -- per-pair: T pd ² ≤ W pd · V pd, via the selected/unselected Engel split
  have hTWV : ∀ pd ∈ P.parts ×ˢ P.parts, T pd ^ 2 ≤ W pd * V pd := by
    rintro ⟨C, D⟩ hpd'
    rw [Finset.mem_product] at hpd'
    obtain ⟨hC, hD⟩ := hpd'
    set d := pairDensity R C D with hd
    -- the selected families cover the traces
    have hcovA : ((Q.parts.filter fun U => U ⊆ C ∧ U ⊆ A).biUnion id) = A ∩ C := by
      rw [biUnion_filter_subset_inter hQP
        (fun U hU => (refineByCuts_subset_or_disjoint hU).1) hC]
    have hcovB : ((Q.parts.filter fun U => U ⊆ D ∧ U ⊆ B).biUnion id) = B ∩ D := by
      rw [biUnion_filter_subset_inter hQP
        (fun U hU => (refineByCuts_subset_or_disjoint hU).2) hD]
    set selL := Q.parts.filter fun U => U ⊆ C ∧ U ⊆ A with hselL
    set selR := Q.parts.filter fun V => V ⊆ D ∧ V ⊆ B with hselR
    have hpdL : (↑selL : Set (Finset α)).PairwiseDisjoint id :=
      Q.supIndep.pairwiseDisjoint.subset
        (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
    have hpdR : (↑selR : Set (Finset α)).PairwiseDisjoint id :=
      Q.supIndep.pairwiseDisjoint.subset
        (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
    -- count and mass of the trace rectangle, decomposed over selected pairs
    have hcnt : (pairCount R (A ∩ C) (B ∩ D) : ℝ)
        = ∑ p ∈ selL ×ˢ selR, ((p.1.card : ℝ) * p.2.card) * pairDensity R p.1 p.2 := by
      rw [pairCount_biUnion R selL selR hpdL hcovA hpdR hcovB, Nat.cast_sum]
      exact Finset.sum_congr rfl fun p _ => by
        rw [pairCount_eq_pairDensity_mul]; ring
    have hmass : ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ)
        = ∑ p ∈ selL ×ˢ selR, ((p.1.card : ℝ) * p.2.card) := by
      rw [← sum_card_biUnion_cast selL hpdL hcovA, ← sum_card_biUnion_cast selR hpdR hcovB,
        Finset.sum_mul_sum, Finset.sum_product]
    have hTsum : T (C, D) = ∑ p ∈ selL ×ˢ selR,
        ((p.1.card : ℝ) * p.2.card) * (pairDensity R p.1 p.2 - d) := by
      simp only [hT]
      rw [hcnt, show d * ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ)
          = d * (((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ)) from by ring, hmass,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    -- selected sums as ite-sums over the full fibre product
    have hsel : selL ×ˢ selR = (fib C ×ˢ fib D).filter
        (fun p => p.1 ⊆ A ∧ p.2 ⊆ B) := by
      rw [hselL, hselR, hfib]
      ext p
      simp only [Finset.mem_product, Finset.mem_filter]
      tauto
    set a : Finset α × Finset α → ℝ := fun p =>
      if p.1 ⊆ A ∧ p.2 ⊆ B then ((p.1.card : ℝ) * p.2.card)
        * (pairDensity R p.1 p.2 - d) else 0 with ha
    set b : Finset α × Finset α → ℝ := fun p => ((p.1.card : ℝ)) * p.2.card with hb
    have hTa : T (C, D) = ∑ p ∈ fib C ×ˢ fib D, a p := by
      rw [hTsum, hsel, Finset.sum_filter]
    have hb0 : ∀ p ∈ fib C ×ˢ fib D, 0 ≤ b p := fun p _ => by
      rw [hb]; positivity
    have hab : ∀ p ∈ fib C ×ˢ fib D, b p = 0 → a p = 0 := by
      intro p _ hbz
      simp only [hb] at hbz
      simp only [ha]
      split_ifs with hsel'
      · rw [hbz, zero_mul]
      · rfl
    have haV : ∑ p ∈ fib C ×ˢ fib D, a p ^ 2 / b p ≤ V (C, D) := by
      simp only [hV]
      refine Finset.sum_le_sum fun p _ => ?_
      simp only [ha, hb]
      split_ifs with hsel'
      · rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ ((p.1.card : ℝ)) * p.2.card)
          with h0 | hpos
        · rw [← h0]
          norm_num
        · refine le_of_eq ?_
          field_simp
          ring
      · rw [zero_pow (by norm_num), zero_div]
        positivity
    have := sq_sum_le_sum_mul hb0 hab haV
    rw [← hTa] at this
    refine this.trans ?_
    have hbW : ∑ p ∈ fib C ×ˢ fib D, b p = W (C, D) := by
      simp only [hW, hb]
      calc ∑ p ∈ fib C ×ˢ fib D, ((p.1.card : ℝ)) * p.2.card
          = (∑ U ∈ fib C, (U.card : ℝ)) * ∑ V' ∈ fib D, (V'.card : ℝ) := by
            rw [Finset.sum_mul_sum, Finset.sum_product]
        _ = ((C.card : ℝ)) * D.card := by
            rw [sum_card_biUnion_cast (fib C) (hpd C) (biUnion_filter_subset_eq hQP hC),
              sum_card_biUnion_cast (fib D) (hpd D) (biUnion_filter_subset_eq hQP hD)]
    rw [hbW]
  -- global: Σ W = |s|², Σ V = energyNum Q − energyNum P
  have hWsum : ∑ pd ∈ P.parts ×ˢ P.parts, W pd = (s.card : ℝ) ^ 2 := by
    rw [hW]
    calc ∑ pd ∈ P.parts ×ˢ P.parts, ((pd.1.card : ℝ)) * pd.2.card
        = (∑ C ∈ P.parts, (C.card : ℝ)) * ∑ D ∈ P.parts, (D.card : ℝ) := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]
  have hVsum : ∑ pd ∈ P.parts ×ˢ P.parts, V pd = energyNum R Q - energyNum R P := by
    have hper : ∀ pd ∈ P.parts ×ˢ P.parts, V pd
        = (∑ p ∈ fib pd.1 ×ˢ fib pd.2, blockEnergy R p.1 p.2)
          - blockEnergy R pd.1 pd.2 := by
      rintro ⟨C, D⟩ hpd'
      rw [Finset.mem_product] at hpd'
      rw [hV]
      exact variance_eq_sum_blockEnergy_sub R (fib C) (fib D) (hpd C)
        (biUnion_filter_subset_eq hQP hpd'.1) (hpd D)
        (biUnion_filter_subset_eq hQP hpd'.2)
    rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
    congr 1
    rw [← energyNum_eq_sum_refined R hQP, Finset.sum_product]
    refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun D _ => ?_
    rw [Finset.sum_product]
  -- the discrepancy decomposes over P-pairs as Σ T
  have hDsum : (pairCount R A B : ℝ) - steppedCount R P A B
      = ∑ pd ∈ P.parts ×ˢ P.parts, T pd := by
    rw [steppedCount, pairCount_eq_sum_inter R P hA hB, Nat.cast_sum,
      Finset.sum_sub_distrib]
  -- global Engel: (Σ|T|)² ≤ (ΣW)(ΣV)
  have habs : ∀ pd ∈ P.parts ×ˢ P.parts, W pd = 0 → |T pd| = 0 := by
    intro pd hpd' hW0
    have h := hTWV pd hpd'
    rw [hW0, zero_mul] at h
    have : T pd = 0 := by nlinarith [sq_nonneg (T pd)]
    rw [this, abs_zero]
  have hTV : ∀ pd ∈ P.parts ×ˢ P.parts, |T pd| ^ 2 / W pd ≤ V pd := by
    intro pd hpd'
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ W pd from by simp only [hW]; positivity)
      with h0 | hpos
    · rw [← h0, div_zero]
      exact hV0 pd
    · rw [div_le_iff₀ hpos, sq_abs]
      exact (hTWV pd hpd').trans (le_of_eq (mul_comm _ _))
  have hglobal : (∑ pd ∈ P.parts ×ˢ P.parts, |T pd|) ^ 2
      ≤ (s.card : ℝ) ^ 2 * (energyNum R Q - energyNum R P) := by
    have := sq_sum_le_sum_mul (a := fun pd => |T pd|) (b := W)
      (fun pd _ => by simp only [hW]; positivity) habs
      (Finset.sum_le_sum hTV)
    rw [hWsum, hVsum] at this
    exact this
  -- conclude
  have hDabs : ε * (s.card : ℝ) ^ 2 < ∑ pd ∈ P.parts ×ˢ P.parts, |T pd| := by
    refine lt_of_lt_of_le hdev ?_
    rw [hDsum]
    exact Finset.abs_sum_le_sum_abs _ _
  have hspos : (0 : ℝ) < (s.card : ℝ) := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · exfalso
      have hsempty : s = ∅ := Finset.card_eq_zero.mp h0
      have hA0 : A = ∅ := Finset.subset_empty.mp (hsempty ▸ hA)
      have hB0 : B = ∅ := Finset.subset_empty.mp (hsempty ▸ hB)
      have hpc : pairCount R A B = 0 := by
        rw [hA0]
        simp [pairCount]
      have hsc : steppedCount R P A B = 0 := by
        rw [steppedCount]
        refine Finset.sum_eq_zero fun p _ => ?_
        rw [hA0]
        simp
      rw [hpc, hsc, h0] at hdev
      norm_num at hdev
    · exact_mod_cast hpos
  have hgain : ε ^ 2 * (s.card : ℝ) ^ 2 < energyNum R Q - energyNum R P := by
    have h1 : (ε * (s.card : ℝ) ^ 2) ^ 2
        < (∑ pd ∈ P.parts ×ˢ P.parts, |T pd|) ^ 2 := by
      have hnn : (0:ℝ) ≤ ε * (s.card : ℝ) ^ 2 := by positivity
      nlinarith [hDabs]
    have h2 := lt_of_lt_of_le h1 hglobal
    have hs2 : (0:ℝ) < (s.card : ℝ) ^ 2 := by positivity
    nlinarith [h2]
  rw [energy, energy]
  have hs2 : (0:ℝ) < (s.card : ℝ) ^ 2 := by positivity
  rw [div_add' _ _ _ hs2.ne', div_le_div_iff_of_pos_right hs2]
  linarith

/-! ### The Frieze–Kannan iteration -/

/-- Fuel-parametrized FK iteration: from energy within `t·ε²` of the ceiling, `t`
rounds reach a partition with uniformly `ε·|s|²`-small cut discrepancy. -/
theorem fk_iterate (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * ε ^ 2 ≤ energy R P →
      ∃ Q : Finpartition s, Q ≤ P ∧ Q.parts.card ≤ P.parts.card * 4 ^ t ∧
        ∀ A ⊆ s, ∀ B ⊆ s,
          |(pairCount R A B : ℝ) - steppedCount R Q A B| ≤ ε * (s.card : ℝ) ^ 2 := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, by simp, ?_⟩
    intro A hA B hB
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨Q, _, _, hinc⟩ :=
      exists_refinement_energy_increment_of_cut_witness R hA hB hε hcon
    have h1 : energy R Q ≤ 1 := energy_le_one R
    have h2 : (1 : ℝ) ≤ energy R P := by simpa using hbudget
    have : (0:ℝ) < ε ^ 2 := by positivity
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : ∀ A ⊆ s, ∀ B ⊆ s,
        |(pairCount R A B : ℝ) - steppedCount R P A B| ≤ ε * (s.card : ℝ) ^ 2
    · exact ⟨P, le_rfl, Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num)), hreg⟩
    · push Not at hreg
      obtain ⟨A, hA, B, hB, hdev⟩ := hreg
      obtain ⟨P', hP'P, hP'card, hinc⟩ :=
        exists_refinement_energy_increment_of_cut_witness R hA hB hε hdev
      have hbudget' : 1 - (t : ℝ) * ε ^ 2 ≤ energy R P' := by
        push_cast at hbudget
        nlinarith [hinc]
      obtain ⟨Q, hQP', hQcard, hQreg⟩ := IH P' hbudget'
      refine ⟨Q, hQP'.trans hP'P, ?_, hQreg⟩
      calc Q.parts.card ≤ P'.parts.card * 4 ^ t := hQcard
        _ ≤ (4 * P.parts.card) * 4 ^ t := Nat.mul_le_mul_right _ hP'card
        _ = P.parts.card * 4 ^ (t + 1) := by ring

/-- **Finite Frieze–Kannan weak regularity.** Every relation admits a partition with
at most `4^(⌈1/ε²⌉ + 1)` parts whose stepped approximation is within `ε·|s|²` of the
true count on every rectangle. -/
theorem frieze_kannan (hε : 0 < ε) :
    ∃ P : Finpartition s, P.parts.card ≤ 4 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      ∀ A ⊆ s, ∀ B ⊆ s,
        |(pairCount R A B : ℝ) - steppedCount R P A B| ≤ ε * (s.card : ℝ) ^ 2 := by
  have hbudget : 1 - ((⌈1 / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) * ε ^ 2 ≤ energy R (⊤ : Finpartition s) := by
    have h0 : (0 : ℝ) ≤ energy R (⊤ : Finpartition s) := energy_nonneg R
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) * ε ^ 2 := by
      calc (1 : ℝ) = 1 / ε ^ 2 * ε ^ 2 := by field_simp
        _ ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) * ε ^ 2 :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε2.le
    push_cast
    nlinarith
  obtain ⟨Q, _, hQcard, hQreg⟩ :=
    fk_iterate R hε (⌈1 / ε ^ 2⌉₊ + 1) (⊤ : Finpartition s) hbudget
  refine ⟨Q, ?_, hQreg⟩
  calc Q.parts.card ≤ (⊤ : Finpartition s).parts.card * 4 ^ (⌈1 / ε ^ 2⌉₊ + 1) := hQcard
    _ ≤ 1 * 4 ^ (⌈1 / ε ^ 2⌉₊ + 1) :=
        Nat.mul_le_mul_right _ parts_top_card_le_one
    _ = 4 ^ (⌈1 / ε ^ 2⌉₊ + 1) := one_mul _

/-- The supremum form: the cut discrepancy itself is at most `ε·|s|²`. -/
theorem frieze_kannan_cutDiscrepancy (hε : 0 < ε) :
    ∃ P : Finpartition s, P.parts.card ≤ 4 ^ (⌈1 / ε ^ 2⌉₊ + 1) ∧
      cutDiscrepancy R P ≤ ε * (s.card : ℝ) ^ 2 := by
  obtain ⟨P, hcard, hreg⟩ := frieze_kannan R hε
  exact ⟨P, hcard, (cutDiscrepancy_le_iff R).mpr hreg⟩

/-! ### Tests and adversarial examples -/

-- The double split of ⊤ by the witness rectangle ({0}, {0}) on {0, 1}: at most
-- 4·1 parts, and it refines ⊤.
example :
    (refineByCuts (⊤ : Finpartition (Finset.univ : Finset (Fin 2))) {0} {0}).parts.card
      ≤ 4 :=
  le_trans (refineByCuts_parts_card_le _ _ _) (by
    have := parts_top_card_le_one (s := (Finset.univ : Finset (Fin 2)))
    omega)

-- FK instantiated on a concrete host (statement elaborates; existence proved).
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 3)),
      P.parts.card ≤ 4 ^ (⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ + 1) ∧
      ∀ A ⊆ (Finset.univ : Finset (Fin 3)), ∀ B ⊆ Finset.univ,
        |(pairCount (fun a b : Fin 3 => a < b) A B : ℝ)
          - steppedCount (fun a b : Fin 3 => a < b) P A B|
          ≤ 1 / 2 * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ 2 :=
  frieze_kannan _ (by norm_num)

end RegularityLemmata
