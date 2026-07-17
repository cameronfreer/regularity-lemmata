/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.BadMassDiag
import RegularityLemmata.Graph.Regularity

/-!
# Phase 11 unit 4: diagonal-inclusive witness atomisation and regularity

The diagonal-inclusive increment and iteration (Phase 11 design freeze in
`ARCHITECTURE.md`): near-verbatim ports of `Graph/Atomise.lean` and
`Graph/Regularity.lean` keyed to `IsBadPairDiag` — the witness atomisation, the
per-pair energy bridge, and the bounded-iteration architecture never use
cell-distinctness, and the partition energy is diagonal-inclusive by the frozen
mass-weighted convention, so the growth `k · 2^(2k)` per step, the fuel `⌈1/ε⁵⌉`, and
the part-count bound `regularityBound` (reused, not redefined) are all **unchanged**.

A cell `C` now also receives the two witness sides of its own bad diagonal pair
`(C, C)`; the cut-count bound `2k` and everything downstream absorb this without
modification. The generic gluing lemma `isPartUnion_bind_atomise` is reused directly.

Summit: `exists_regularDiag_refinement` — every partition has a diagonal-inclusively
`ε`-regular refinement with the same host-independent bound as the frozen off-diagonal
ladder; through `IsRegularPartitionDiag.isRegularPartition` it strengthens, and never
disturbs, every existing consumer.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] {ε : ℝ}

/-! ### Diagonal-inclusive witness cuts -/

section Cuts

variable (ε)

open Classical in
/-- The cutting sets landing in the cell `C`: left witnesses of diagonal-inclusive bad
pairs `(C, D)` and right witnesses of bad pairs `(D, C)` — for `D = C` both sides of
the bad diagonal pair land in `C`. -/
noncomputable def diagWitnessCuts (P : Finpartition s) (C : Finset α) :
    Finset (Finset α) :=
  (P.parts.image fun D =>
      if h : IsBadPairDiag R ε C D then (NonuniformWitness.ofNotUniform h).left else ∅)
    ∪ (P.parts.image fun D =>
      if h : IsBadPairDiag R ε D C then (NonuniformWitness.ofNotUniform h).right else ∅)

theorem diagWitnessCuts_card_le (P : Finpartition s) (C : Finset α) :
    (diagWitnessCuts R ε P C).card ≤ 2 * P.parts.card := by
  classical
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := P.parts) (f := fun D =>
    if h : IsBadPairDiag R ε C D then (NonuniformWitness.ofNotUniform h).left else ∅)
  have h2 := Finset.card_image_le (s := P.parts) (f := fun D =>
    if h : IsBadPairDiag R ε D C then (NonuniformWitness.ofNotUniform h).right else ∅)
  omega

theorem diagWitnessCuts_subset (P : Finpartition s) {C : Finset α}
    {b : Finset α} (hb : b ∈ diagWitnessCuts R ε P C) : b ⊆ C := by
  rw [diagWitnessCuts, Finset.mem_union] at hb
  rcases hb with hb | hb <;> rw [Finset.mem_image] at hb <;> obtain ⟨D, _, rfl⟩ := hb
  · split_ifs with h
    · exact (NonuniformWitness.ofNotUniform h).left_subset
    · exact Finset.empty_subset _
  · split_ifs with h
    · exact (NonuniformWitness.ofNotUniform h).right_subset
    · exact Finset.empty_subset _

/-- The diagonal-inclusive simultaneous witness refinement. -/
noncomputable def diagWitnessRefinement (P : Finpartition s) : Finpartition s :=
  P.bind fun C _ => Finpartition.atomise C (diagWitnessCuts R ε P C)

theorem diagWitnessRefinement_le (P : Finpartition s) :
    diagWitnessRefinement R ε P ≤ P := by
  intro b hb
  rw [diagWitnessRefinement, Finpartition.mem_bind] at hb
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, (Finpartition.atomise C (diagWitnessCuts R ε P C)).le hb⟩

/-- **Part-count bound `k · 2^(2k)`** — unchanged from the off-diagonal layer: each
cell still receives at most `2k` cuts (its own diagonal witnesses replace one formerly
empty left slot and one formerly empty right slot). -/
theorem diagWitnessRefinement_parts_card_le (P : Finpartition s) :
    (diagWitnessRefinement R ε P).parts.card
      ≤ P.parts.card * 2 ^ (2 * P.parts.card) := by
  rw [diagWitnessRefinement, Finpartition.card_bind]
  calc ∑ C ∈ P.parts.attach,
        (Finpartition.atomise C.1 (diagWitnessCuts R ε P C.1)).parts.card
      ≤ ∑ _C ∈ P.parts.attach, 2 ^ (2 * P.parts.card) := by
        refine Finset.sum_le_sum fun C _ => ?_
        refine Finpartition.card_atomise_le.trans ?_
        exact Nat.pow_le_pow_right (by norm_num) (diagWitnessCuts_card_le R ε P C.1)
    _ = P.parts.card * 2 ^ (2 * P.parts.card) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]

/-- **Witness resolution, diagonal pairs included.** Every diagonal-inclusive bad pair
has a witness whose sides are part unions of the refinement (via the generic
`isPartUnion_bind_atomise`). -/
theorem diagWitnessRefinement_resolves (P : Finpartition s) :
    ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPairDiag R ε C D →
      ∃ w : NonuniformWitness R C D ε,
        IsPartUnion (diagWitnessRefinement R ε P) w.left ∧
        IsPartUnion (diagWitnessRefinement R ε P) w.right := by
  classical
  intro C hC D hD hbad
  refine ⟨NonuniformWitness.ofNotUniform hbad, ?_, ?_⟩
  · refine isPartUnion_bind_atomise hC ?_
      (NonuniformWitness.ofNotUniform hbad).left_subset
    rw [diagWitnessCuts, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨D, hD, dif_pos hbad⟩
  · refine isPartUnion_bind_atomise hD ?_
      (NonuniformWitness.ofNotUniform hbad).right_subset
    rw [diagWitnessCuts, Finset.mem_union]
    right
    rw [Finset.mem_image]
    exact ⟨C, hC, dif_pos hbad⟩

end Cuts

/-! ### The diagonal-inclusive global increment -/

/-- **Global increment, un-normalized**: a refinement resolving every
diagonal-inclusive bad pair's witness gains at least `ε⁴ · badMassDiagNum` of energy —
the per-pair energy bridge never uses cell-distinctness, and the energy sum is
diagonal-inclusive by the frozen convention. -/
theorem energyNum_increment_of_badMassDiagNum {P P' : Finpartition s} (hP' : P' ≤ P)
    (hε : 0 < ε)
    (hwit : ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPairDiag R ε C D →
      ∃ w : NonuniformWitness R C D ε, IsPartUnion P' w.left ∧ IsPartUnion P' w.right) :
    energyNum R P + ε ^ 4 * badMassDiagNum R ε P ≤ energyNum R P' := by
  classical
  have hpp : ∀ uv ∈ P.parts ×ˢ P.parts,
      blockEnergy R uv.1 uv.2
        + (if IsBadPairDiag R ε uv.1 uv.2
            then ε ^ 4 * ((uv.1.card : ℝ) * (uv.2.card : ℝ)) else 0)
      ≤ ∑ C' ∈ P'.parts.filter (· ⊆ uv.1), ∑ D' ∈ P'.parts.filter (· ⊆ uv.2),
          blockEnergy R C' D' := by
    intro uv huv
    rw [Finset.mem_product] at huv
    obtain ⟨hC, hD⟩ := huv
    by_cases hbad : IsBadPairDiag R ε uv.1 uv.2
    · rw [if_pos hbad, ← mul_assoc]
      obtain ⟨w, hlU, hrU⟩ := hwit uv.1 hC uv.2 hD hbad
      exact blockEnergy_increment_refined R hε w
        (isPartUnion_of_mem_of_le hP' hC) (isPartUnion_of_mem_of_le hP' hD) hlU hrU
    · rw [if_neg hbad, add_zero]
      exact blockEnergy_le_sum_refined hP' R hC hD
  calc energyNum R P + ε ^ 4 * badMassDiagNum R ε P
      = ∑ uv ∈ P.parts ×ˢ P.parts, (blockEnergy R uv.1 uv.2
          + (if IsBadPairDiag R ε uv.1 uv.2
              then ε ^ 4 * ((uv.1.card : ℝ) * (uv.2.card : ℝ)) else 0)) := by
        unfold energyNum badMassDiagNum
        rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
    _ ≤ ∑ uv ∈ P.parts ×ˢ P.parts, ∑ C' ∈ P'.parts.filter (· ⊆ uv.1),
          ∑ D' ∈ P'.parts.filter (· ⊆ uv.2), blockEnergy R C' D' :=
        Finset.sum_le_sum hpp
    _ = energyNum R P' := by
        rw [Finset.sum_product]
        exact energyNum_eq_sum_refined R hP'

/-- **Global increment, normalized**: normalized diagonal-inclusive bad mass exceeding
`ε` yields an `ε⁵` energy gain. -/
theorem energy_increment_of_badMassDiag {P P' : Finpartition s} (hP' : P' ≤ P)
    (hε : 0 < ε)
    (hwit : ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPairDiag R ε C D →
      ∃ w : NonuniformWitness R C D ε, IsPartUnion P' w.left ∧ IsPartUnion P' w.right)
    (hbm : ε < badMassDiag R ε P) :
    energy R P + ε ^ 5 ≤ energy R P' := by
  have hs : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
    by_contra hzero
    push Not at hzero
    have h0 : ((s.card : ℝ)) ^ 2 = 0 := le_antisymm hzero (by positivity)
    rw [badMassDiag, h0, div_zero] at hbm
    linarith
  have hmain := energyNum_increment_of_badMassDiagNum R hP' hε hwit
  have hbmN : ε * (s.card : ℝ) ^ 2 < badMassDiagNum R ε P := by
    rw [badMassDiag, lt_div_iff₀ hs] at hbm
    linarith
  have hgain : ε ^ 5 * (s.card : ℝ) ^ 2 ≤ ε ^ 4 * badMassDiagNum R ε P := by
    have hrw : ε ^ 5 * (s.card : ℝ) ^ 2 = ε ^ 4 * (ε * (s.card : ℝ) ^ 2) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hbmN.le (by positivity)
  have key : energyNum R P + ε ^ 5 * (s.card : ℝ) ^ 2 ≤ energyNum R P' := by
    linarith
  unfold energy
  rw [div_add' _ _ _ hs.ne']
  gcongr

/-- **The diagonal-inclusive weak step** — identical growth `k · 2^(2k)`. -/
theorem exists_refinement_energy_increment_diag (P : Finpartition s) (hε : 0 < ε)
    (hbm : ε < badMassDiag R ε P) :
    ∃ Q : Finpartition s, Q ≤ P ∧ energy R P + ε ^ 5 ≤ energy R Q ∧
      Q.parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) :=
  ⟨diagWitnessRefinement R ε P, diagWitnessRefinement_le R ε P,
    energy_increment_of_badMassDiag R (diagWitnessRefinement_le R ε P) hε
      (diagWitnessRefinement_resolves R ε P) hbm,
    diagWitnessRefinement_parts_card_le R ε P⟩

/-! ### Bounded iteration — `regularityBound` and the fuel are reused unchanged -/

/-- **Fuel-parametrized diagonal-inclusive iteration**: same fuel, same
`regularityBound`, because the energy ceiling `1` is diagonal-inclusive already. -/
theorem regularityDiag_iterate (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s), 1 - (t : ℝ) * ε ^ 5 ≤ energy R P →
      ∃ Q : Finpartition s, Q ≤ P ∧ IsRegularPartitionDiag R ε Q ∧
        Q.parts.card ≤ regularityBound t P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, ?_, le_regularityBound 0 _⟩
    by_contra hcon
    rw [IsRegularPartitionDiag, not_le] at hcon
    obtain ⟨Q, _, hinc, _⟩ := exists_refinement_energy_increment_diag R P hε hcon
    have h1 : energy R Q ≤ 1 := energy_le_one R
    have h2 : (1 : ℝ) ≤ energy R P := by simpa using hbudget
    have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : IsRegularPartitionDiag R ε P
    · exact ⟨P, le_rfl, hreg, le_regularityBound _ _⟩
    · rw [IsRegularPartitionDiag, not_le] at hreg
      obtain ⟨P', hP'P, hinc, hcard'⟩ := exists_refinement_energy_increment_diag R P hε hreg
      have hbudget' : 1 - (t : ℝ) * ε ^ 5 ≤ energy R P' := by
        have hexp : ((t : ℝ) + 1) * ε ^ 5 = (t : ℝ) * ε ^ 5 + ε ^ 5 := by ring
        push_cast at hbudget
        rw [hexp] at hbudget
        linarith
      obtain ⟨Q, hQP', hQreg, hQcard⟩ := IH P' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQreg, ?_⟩
      calc Q.parts.card ≤ regularityBound t P'.parts.card := hQcard
        _ ≤ regularityBound t (P.parts.card * 2 ^ (2 * P.parts.card)) :=
            regularityBound_mono t hcard'
        _ = regularityBound (t + 1) P.parts.card := by simp only [regularityBound]

/-- **Diagonal-inclusive partition regularity.** Every partition has a
diagonal-inclusively `ε`-regular refinement with the SAME host-independent bound
`regularityBound ⌈1/ε⁵⌉ k` as the frozen off-diagonal ladder. -/
theorem exists_regularDiag_refinement (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsRegularPartitionDiag R ε Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ P.parts.card := by
  refine regularityDiag_iterate R hε _ P ?_
  have h0 : (0 : ℝ) ≤ energy R P := energy_nonneg R
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := by
    calc (1 : ℝ) = 1 / ε ^ 5 * ε ^ 5 := by field_simp
      _ ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε5.le
  linarith

/-! ### Tests and adversarial examples -/

-- **Gate 10 (the freeze's ladder-sanity gate).** The single-cell equality-relation
-- partition is diagonal-inclusively BAD at 1/4 (`Graph/BadMassDiag.lean`), and the
-- diagonal-inclusive ladder genuinely fires and resolves it: the summit delivers a
-- refinement that is diagonal-inclusively 1/4-regular — necessarily a strict
-- refinement here, which no off-diagonal machinery would have been forced to produce.
example : ∃ Q : Finpartition (Finset.univ : Finset (Fin 2)),
    Q ≤ Finpartition.indiscrete (by decide) ∧
      IsRegularPartitionDiag (fun a b : Fin 2 => a = b) (1 / 4) Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / (1 / 4 : ℝ) ^ 5⌉₊
        (Finpartition.indiscrete (a := (Finset.univ : Finset (Fin 2)))
          (by decide)).parts.card :=
  exists_regularDiag_refinement _ _ (by norm_num)

-- The diagonal-inclusive summit strengthens the frozen one: statement-level bridge.
example {Q : Finpartition ({0, 1, 2} : Finset (Fin 3))} {ε : ℝ}
    (h : IsRegularPartitionDiag (fun a b : Fin 3 => a < b) ε Q) :
    IsRegularPartition (fun a b : Fin 3 => a < b) ε Q :=
  h.isRegularPartition

-- Growth and fuel are literally the frozen ones (`regularityBound` is reused, not
-- redefined).
example : regularityBound 1 2 = 32 := by decide

end RegularityLemmata
