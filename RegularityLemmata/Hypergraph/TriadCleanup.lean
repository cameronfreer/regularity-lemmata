/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.TriadIncrement

/-!
# The edited summit: regular approximation by deletion

Phase 7's second summit (design freeze in `ARCHITECTURE.md`). An unordered edge is
**bad** (`IsBadTriadEdge`) when one — and by the enumeration of orderings
(`exists_comp_perm_of_tupleRange_eq`) together with the permutation closure of bad
keys, *every* — injective ordering has a bad polyad key
(`isBadTriadEdge_iff_of_tupleRange`). The **triadCleaned hypergraph** (`triadCleaned`) retains
exactly the non-bad edges of `H`: a deletion-only, mathematically finite,
classically decidable construction (the badness predicate is real-valued, so it is
not kernel-computable).

On a good key the triadCleaned observable agrees with `H`'s throughout the parent block
(`triadObs_triadCleaned_iff_of_good`); on a bad key it is identically false
(`not_triadObs_triadCleaned_of_bad`). Hence **every** key — realized or not — is locally
disc-regular for the triadCleaned graph (`isLocalDiscRegular_triadCleaned`): good keys
inherit `H`'s regularity, bad keys are constant-zero at their new own density `0`.
The ordered edit triples are contained in the exceptional tuple set
(`editTriples_subset_badTriadTuples`), giving the edit inequality
`6 · editCount H (triadCleaned H κ δ) ≤ badTriadMassNum H κ δ`.

Combining with the weak summit (`exists_goodColoring`) yields the **edited
summit** (`exists_triadic_regular_approximation`): every 3-uniform hypergraph admits a pair
coloring with at most `triadBound δ` colors and a deletion-only subgraph within
`δ·|V|³` ordered edits, under which every key is locally disc-regular. A precursor
to, not a formalization of, the Rödl–Schacht regular-partition theorem.
-/

namespace RegularityLemmata

open UniformHypergraph

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-! ### Bad edges, independently of ordering -/

/-- An unordered edge is bad when some injective ordering has a bad polyad key. -/
def IsBadTriadEdge (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ)
    (e : RSet 3 α) : Prop :=
  ∃ (v : Fin 3 → α) (hv : Function.Injective v),
    tupleRange v = e.1 ∧ IsBadTriad H κ δ (polyadKey κ hv)

/-- Badness of an edge is ordering-independent: any one injective realization
decides it. -/
theorem isBadTriadEdge_iff_of_tupleRange {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} {e : RSet 3 α} {v : Fin 3 → α}
    (hv : Function.Injective v) (hrange : tupleRange v = e.1) :
    IsBadTriadEdge H κ δ e ↔ IsBadTriad H κ δ (polyadKey κ hv) := by
  constructor
  · rintro ⟨w, hw, hwrange, hbad⟩
    obtain ⟨σ, hσ⟩ := exists_comp_perm_of_tupleRange_eq hw hv
      (by rw [hwrange, hrange])
    subst hσ
    rw [polyadKey_comp_perm κ hw σ hv] at *
    have := (isBadTriad_comp_perm_iff H κ δ (polyadKey κ hw) σ⁻¹).mpr hbad
    rwa [inv_inv] at this
  · intro h
    exact ⟨v, hv, hrange, h⟩

/-! ### The triadCleaned hypergraph -/

/-- The triadCleaned hypergraph: delete every bad edge of `H`. Deletion-only by
construction; classically decidable, not kernel-computable. -/
noncomputable def triadCleaned (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : UniformHypergraph 3 α := by
  classical
  exact ⟨H.edges.filter fun e => ∀ h : e.card = 3, ¬IsBadTriadEdge H κ δ ⟨e, h⟩,
    fun e he => H.card_eq e (Finset.mem_filter.mp he).1⟩

/-- Deletion only. -/
theorem triadCleaned_subset (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ) :
    (triadCleaned H κ δ).edges ⊆ H.edges := by
  classical
  rw [triadCleaned]
  exact Finset.filter_subset _ _

theorem mem_triadCleaned {H : UniformHypergraph 3 α} {κ : RSet 2 α → Fin K} {δ : ℝ}
    {e : Finset α} :
    e ∈ (triadCleaned H κ δ).edges
      ↔ e ∈ H.edges ∧ ∀ h : e.card = 3, ¬IsBadTriadEdge H κ δ ⟨e, h⟩ := by
  classical
  rw [triadCleaned]
  exact Finset.mem_filter

/-- On a good key, the triadCleaned observable agrees with `H`'s throughout the parent
block. -/
theorem triadObs_triadCleaned_iff_of_good {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} {key : Fin 3 → Fin K}
    (hgood : ¬IsBadTriad H κ δ key) {v : Fin 3 → α} (hv : v ∈ polyadBlock κ key) :
    triadObs (triadCleaned H κ δ) v ↔ triadObs H v := by
  have hinj := injective_of_mem_polyadBlock hv
  have hkey := polyadKey_eq_of_mem_polyadBlock hinj hv
  rw [triadObs, triadObs, mem_triadCleaned]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun hcard hbadedge => hgood ?_⟩
    rw [isBadTriadEdge_iff_of_tupleRange hinj rfl] at hbadedge
    rwa [hkey] at hbadedge

/-- On a bad key, the triadCleaned observable is identically false on the parent
block. -/
theorem not_triadObs_triadCleaned_of_bad {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} {key : Fin 3 → Fin K}
    (hbad : IsBadTriad H κ δ key) {v : Fin 3 → α} (hv : v ∈ polyadBlock κ key) :
    ¬triadObs (triadCleaned H κ δ) v := by
  have hinj := injective_of_mem_polyadBlock hv
  have hkey := polyadKey_eq_of_mem_polyadBlock hinj hv
  rw [triadObs, mem_triadCleaned]
  rintro ⟨-, hnotbad⟩
  refine hnotbad (card_tupleRange_of_injective hinj) ?_
  rw [isBadTriadEdge_iff_of_tupleRange hinj rfl, hkey]
  exact hbad

/-! ### Every key is locally regular for the triadCleaned graph -/

/-- **Local regularity everywhere**: for the triadCleaned hypergraph, every key —
realized or not — is locally disc-regular. Good keys inherit `H`'s regularity; bad
keys are constant-zero at their new own density `0`. -/
theorem isLocalDiscRegular_triadCleaned {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} (hδ : 0 ≤ δ) (key : Fin 3 → Fin K) :
    IsLocalDiscRegular κ (triadObs (triadCleaned H κ δ)) key δ := by
  classical
  by_cases hbad : IsBadTriad H κ δ key
  · -- Constant-zero: every density over subsets of the block is 0.
    have hzero : ∀ S : Finset (Fin 3 → α), S ⊆ polyadBlock κ key →
        densityOn S (triadObs (triadCleaned H κ δ)) = 0 := by
      intro S hS
      rw [densityOn, Finset.filter_false_of_mem
        (fun v hvS => not_triadObs_triadCleaned_of_bad hbad (hS hvS)),
        Finset.card_empty]
      norm_num
    intro P _
    rw [hzero _ (discAtom_subset_polyadBlock κ key P),
      hzero _ (Finset.Subset.refl _), sub_zero, abs_zero]
    exact hδ
  · -- Densities agree with `H` on all subsets of the block; inherit regularity.
    have hagree : ∀ S : Finset (Fin 3 → α), S ⊆ polyadBlock κ key →
        densityOn S (triadObs (triadCleaned H κ δ)) = densityOn S (triadObs H) := by
      intro S hS
      rw [densityOn, densityOn, Finset.filter_congr
        fun v hvS => triadObs_triadCleaned_iff_of_good hbad (hS hvS)]
    have hreg : IsLocalDiscRegular κ (triadObs H) key δ := not_not.mp hbad
    intro P hthr
    rw [hagree _ (discAtom_subset_polyadBlock κ key P),
      hagree _ (Finset.Subset.refl _)]
    exact hreg P hthr

/-! ### The edit inequality -/

/-- Every ordered disagreement triple lives in a bad block. -/
theorem editTriples_subset_badTriadTuples (H : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (δ : ℝ) :
    (injectiveTuples α 3).filter
        (fun v => ¬(triadObs H v ↔ triadObs (triadCleaned H κ δ) v))
      ⊆ badTriadTuples H κ δ := by
  classical
  intro v hv
  rw [Finset.mem_filter, mem_injectiveTuples] at hv
  obtain ⟨hinj, hdis⟩ := hv
  rw [badTriadTuples, Finset.mem_biUnion]
  refine ⟨polyadKey κ hinj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
    mem_polyadBlock_polyadKey κ hinj⟩
  by_contra hgood
  exact hdis (Iff.symm (triadObs_triadCleaned_iff_of_good hgood
    (mem_polyadBlock_polyadKey κ hinj)))

/-- **The edit inequality**: the ordered edit mass of cleaning is at most the bad
mass. -/
theorem editCount_triadCleaned_le (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) :
    (6 * editCount H (triadCleaned H κ δ) : ℝ) ≤ badTriadMassNum H κ δ := by
  classical
  rw [← cast_card_badTriadTuples H κ δ]
  have h6 : 6 * editCount H (triadCleaned H κ δ)
      = ((injectiveTuples α 3).filter
          fun v => ¬(triadObs H v ↔ triadObs (triadCleaned H κ δ) v)).card :=
    (card_editTriples H (triadCleaned H κ δ)).symm
  exact_mod_cast h6 ▸ Nat.cast_le.mpr
    (Finset.card_le_card (editTriples_subset_badTriadTuples H κ δ))

/-- Normalized-to-raw conversion of the bad-mass bound, with the empty host handled
explicitly. -/
theorem badTriadMassNum_le_of_mass_le {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} (h : badTriadMass H κ δ ≤ δ) :
    badTriadMassNum H κ δ ≤ δ * (Fintype.card α : ℝ) ^ 3 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · -- Empty host: no functions `Fin 3 → α`, so every block is empty.
    have hempty : ∀ key : Fin 3 → Fin K, (polyadBlock κ key).card = 0 := by
      intro key
      rw [Finset.card_eq_zero]
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨v 0⟩
      omega
    rw [badTriadMassNum]
    rw [Finset.sum_congr rfl fun key _ => by rw [hempty key, Nat.cast_zero]]
    rw [Finset.sum_const, smul_zero, h0]
    norm_num
  · have hV : (0 : ℝ) < (Fintype.card α : ℝ) ^ 3 := by positivity
    rw [badTriadMass, div_le_iff₀ hV] at h
    exact h

/-! ### The edited summit -/

/-- **The edited summit**: every 3-uniform hypergraph admits a pair coloring with at
most `triadBound δ` colors and a deletion-only subgraph within `δ·|V|³` ordered
edits, under which EVERY key is locally disc-regular. -/
theorem exists_triadic_regular_approximation (H : UniformHypergraph 3 α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (κ : RSet 2 α → Fin K) (G : UniformHypergraph 3 α),
      K ≤ triadBound δ
        ∧ G.edges ⊆ H.edges
        ∧ (6 * editCount H G : ℝ) ≤ δ * (Fintype.card α : ℝ) ^ 3
        ∧ ∀ key : Fin 3 → Fin K, IsLocalDiscRegular κ (triadObs G) key δ := by
  obtain ⟨K, κ, hK, hmass⟩ := exists_goodColoring H hδ
  exact ⟨K, κ, triadCleaned H κ δ, hK, triadCleaned_subset H κ δ,
    le_trans (editCount_triadCleaned_le H κ δ) (badTriadMassNum_le_of_mass_le hmass),
    fun key => isLocalDiscRegular_triadCleaned hδ.le key⟩

/-! ### Tests and adversarial examples -/

section Tests

-- Cleaning the empty hypergraph deletes nothing (no edges to delete): the summit
-- specializes trivially, statement-level.
example (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (κ : RSet 2 (Fin 4) → Fin K) (G : UniformHypergraph 3 (Fin 4)),
      K ≤ triadBound δ
        ∧ G.edges ⊆ (empty 3 (Fin 4)).edges
        ∧ (6 * editCount (empty 3 (Fin 4)) G : ℝ)
            ≤ δ * (Fintype.card (Fin 4) : ℝ) ^ 3
        ∧ ∀ key : Fin 3 → Fin K, IsLocalDiscRegular κ (triadObs G) key δ :=
  exists_triadic_regular_approximation (empty 3 (Fin 4)) hδ

-- Ordering independence of edge badness, statement-level.
example (H : UniformHypergraph 3 (Fin 5)) (κ : RSet 2 (Fin 5) → Fin 2) (δ : ℝ)
    (e : RSet 3 (Fin 5)) (v : Fin 3 → Fin 5) (hv : Function.Injective v)
    (hrange : tupleRange v = e.1) :
    IsBadTriadEdge H κ δ e ↔ IsBadTriad H κ δ (polyadKey κ hv) :=
  isBadTriadEdge_iff_of_tupleRange hv hrange

end Tests

end RegularityLemmata
