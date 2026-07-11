/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.PolyadRegularity

/-!
# Realized triads: mass identities and the block density/edit calculus

Phase 7 units 1–2 of the triadic development (design freeze in `ARCHITECTURE.md`):
a precursor built from the index and polyad test surfaces of V. Rödl, M. Schacht,
*Regular partitions of hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16
(2007) — not a formalization of their full regular-partition theorem.

The frozen conventions in action: the objects are unordered `UniformHypergraph 3 α`;
all counting surfaces are ordered injective triples; the observable
`triadObs H v = tupleRange v ∈ H.edges` is set-level, hence permutation-invariant.
The realization identity gives the total ordered mass `6 · #edges`
(`card_realizedTriples`), refined along a pair coloring `κ : RSet 2 α → Fin K` into
per-block realized counts summing back to the total (`sum_blockRealizedCount` — the
mass identity). Edits are unordered symmetric differences (`UniformHypergraph.symmDiff`);
the ordered edit mass is `6 · editCount`, proved, never assumed
(`card_editTriples`), and block densities of two hypergraphs differ by at most the
block density of their symmetric difference (`abs_blockDensity_sub_le`) — the
density/edit bridge consumed by the repair step.
-/

namespace RegularityLemmata

open UniformHypergraph

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-! ### The triadic observable and total mass -/

/-- The triadic observable: an ordered triple realizes an edge when its underlying
set is one. Set-level, hence invariant under permuting the triple. -/
def triadObs (H : UniformHypergraph 3 α) : (Fin 3 → α) → Prop :=
  fun v => tupleRange v ∈ H.edges

instance (H : UniformHypergraph 3 α) : DecidablePred (triadObs H) :=
  fun v => inferInstanceAs (Decidable (tupleRange v ∈ H.edges))

omit [Fintype α] in
/-- On injective triples the observable is the ordered realization relation. -/
theorem triadObs_iff_orderedRel {H : UniformHypergraph 3 α} {v : Fin 3 → α}
    (hv : Function.Injective v) : triadObs H v ↔ H.orderedRel v :=
  ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩

omit [Fintype α] in
/-- Permutation invariance of the observable. -/
theorem triadObs_comp_perm (H : UniformHypergraph 3 α) (v : Fin 3 → α)
    (σ : Equiv.Perm (Fin 3)) : triadObs H (v ∘ σ) ↔ triadObs H v := by
  rw [triadObs, triadObs, tupleRange, tupleRange]
  rw [show Finset.univ.image (v ∘ σ) = Finset.univ.image v from by
    rw [← Finset.image_image, Finset.image_univ_of_surjective σ.surjective]]

/-- **Total realized mass**: the injective triples realizing `H` number exactly
`3! · #edges = 6 · #edges`. -/
theorem card_realizedTriples (H : UniformHypergraph 3 α) :
    ((injectiveTuples α 3).filter (triadObs H)).card = 6 * H.edges.card := by
  have hfilter : (injectiveTuples α 3).filter (triadObs H)
      = (Fintype.piFinset fun _ : Fin 3 => (Finset.univ : Finset α)).filter
          H.orderedRel := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter, mem_injectiveTuples,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨hv, hobs⟩
      exact ⟨fun i => Finset.mem_univ _, hv, hobs⟩
    · rintro ⟨-, hv, hobs⟩
      exact ⟨hv, hobs⟩
  rw [hfilter, show ((Fintype.piFinset fun _ : Fin 3 =>
      (Finset.univ : Finset α)).filter H.orderedRel).card
      = tupleCount H.orderedRel (fun _ => Finset.univ) from rfl, orderedCount_eq]
  norm_num [Nat.factorial]

/-! ### Per-block realized counts and densities -/

/-- The realized count within one triadic block. -/
def blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : ℕ :=
  ((polyadBlock κ key).filter (triadObs H)).card

/-- The density of `H` within one triadic block (guard-free: `0` on an unrealized
key). -/
noncomputable def blockDensity (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : ℝ :=
  densityOn (polyadBlock κ key) (triadObs H)

theorem blockDensity_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : 0 ≤ blockDensity H κ key :=
  densityOn_nonneg

theorem blockDensity_le_one (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : blockDensity H κ key ≤ 1 :=
  densityOn_le_one

/-- Count/density conversion, valid for all keys (both sides `0` when the key is
unrealized). -/
theorem cast_blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) :
    (blockRealizedCount H κ key : ℝ)
      = blockDensity H κ key * ((polyadBlock κ key).card : ℝ) := by
  rw [blockRealizedCount, blockDensity, densityOn]
  rcases Finset.eq_empty_or_nonempty (polyadBlock κ key) with hempty | hne
  · rw [hempty]
    simp
  · rw [div_mul_cancel₀]
    exact_mod_cast (Finset.card_pos.mpr hne).ne'

/-- **The mass identity**: block realized counts sum to the total ordered
realization mass `6 · #edges`. -/
theorem sum_blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) :
    ∑ key : Fin 3 → Fin K, blockRealizedCount H κ key = 6 * H.edges.card := by
  classical
  have hdisj : ∀ key ∈ (Finset.univ : Finset (Fin 3 → Fin K)),
      ∀ key' ∈ (Finset.univ : Finset (Fin 3 → Fin K)), key ≠ key' →
      Disjoint ((polyadBlock κ key).filter (triadObs H))
        ((polyadBlock κ key').filter (triadObs H)) := fun key _ key' _ h =>
    (polyadBlock_disjoint h).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc ∑ key : Fin 3 → Fin K, blockRealizedCount H κ key
      = (Finset.univ.biUnion fun key =>
          (polyadBlock κ key).filter (triadObs H)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = ((Finset.univ.biUnion (polyadBlock κ)).filter (triadObs H)).card := by
        rw [Finset.filter_biUnion]
    _ = ((injectiveTuples α 3).filter (triadObs H)).card := by
        rw [biUnion_polyadBlock]
    _ = 6 * H.edges.card := card_realizedTriples H

/-! ### The edit calculus -/

/-- The unordered edit count between two 3-uniform hypergraphs. -/
def editCount (H G : UniformHypergraph 3 α) : ℕ :=
  (H.symmDiff G).edges.card

omit [Fintype α] in
theorem editCount_comm (H G : UniformHypergraph 3 α) :
    editCount H G = editCount G H := by
  rw [editCount, editCount]
  refine congrArg Finset.card ?_
  ext e
  rw [mem_symmDiff, mem_symmDiff]
  tauto

omit [Fintype α] in
theorem editCount_self (H : UniformHypergraph 3 α) : editCount H H = 0 := by
  rw [editCount, Finset.card_eq_zero]
  ext e
  rw [mem_symmDiff]
  tauto

omit [Fintype α] in
/-- The disagreement observable is the observable of the symmetric difference. -/
theorem triadObs_symmDiff (H G : UniformHypergraph 3 α) (v : Fin 3 → α) :
    triadObs (H.symmDiff G) v ↔ ¬(triadObs H v ↔ triadObs G v) := by
  rw [triadObs, triadObs, triadObs, mem_symmDiff]

/-- **The ordered edit mass and the factor 6**: injective triples witnessing a
disagreement number exactly `6 · editCount` — proved via the realization identity,
never assumed. -/
theorem card_editTriples (H G : UniformHypergraph 3 α) :
    ((injectiveTuples α 3).filter
        fun v => ¬(triadObs H v ↔ triadObs G v)).card = 6 * editCount H G := by
  have hcongr : (injectiveTuples α 3).filter
        (fun v => ¬(triadObs H v ↔ triadObs G v))
      = (injectiveTuples α 3).filter (triadObs (H.symmDiff G)) :=
    Finset.filter_congr fun v _ => (triadObs_symmDiff H G v).symm
  rw [hcongr, card_realizedTriples, editCount]

/-- **The block density/edit bridge**: within any block, the densities of `H` and
`G` differ by at most the block density of their symmetric difference. -/
theorem abs_blockDensity_sub_le (H G : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (key : Fin 3 → Fin K) :
    |blockDensity H κ key - blockDensity G κ key|
      ≤ blockDensity (H.symmDiff G) κ key := by
  rw [blockDensity, blockDensity, blockDensity]
  refine le_trans abs_densityOn_sub_densityOn_le (le_of_eq ?_)
  rw [densityOn, densityOn]
  refine congrArg (· / _) ?_
  exact_mod_cast congrArg Finset.card
    (Finset.filter_congr fun v _ => (triadObs_symmDiff H G v).symm)

/-- Per-block edit mass sums to the ordered total (mass identity for edits). -/
theorem sum_blockRealizedCount_symmDiff (H G : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) :
    ∑ key : Fin 3 → Fin K, blockRealizedCount (H.symmDiff G) κ key
      = 6 * editCount H G :=
  sum_blockRealizedCount (H.symmDiff G) κ

/-! ### Bad keys and their mass -/

/-- A **bad key**: `H` fails local disc regularity at the block's own density
(`IsLocalDiscRegular`, the canonical Phase 7 predicate). -/
def IsBadTriad (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ)
    (key : Fin 3 → Fin K) : Prop :=
  ¬ IsLocalDiscRegular κ (triadObs H) key δ

/-- Unrealized keys are never bad (for `0 ≤ δ`). -/
theorem not_isBadTriad_of_empty_block {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} {key : Fin 3 → Fin K}
    (h : polyadBlock κ key = ∅) (hδ : 0 ≤ δ) : ¬ IsBadTriad H κ δ key :=
  not_not_intro (isLocalDiscRegular_of_empty_block h hδ)

/-- **Permutation closure of bad keys**: the observable is set-level, so all ordered
presentations of an unordered triad go bad together. -/
theorem isBadTriad_comp_perm_iff (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) (key : Fin 3 → Fin K) (σ : Equiv.Perm (Fin 3)) :
    IsBadTriad H κ δ (key ∘ ⇑σ⁻¹) ↔ IsBadTriad H κ δ key :=
  not_congr (isLocalDiscRegular_comp_perm_iff σ fun w => triadObs_comp_perm H w σ)

open Classical in
/-- The (ordered, diagonal-free) mass carried by the bad keys. -/
noncomputable def badTriadMassNum (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : ℝ :=
  ∑ key ∈ Finset.univ.filter (fun key => IsBadTriad H κ δ key),
    ((polyadBlock κ key).card : ℝ)

/-- Normalized bad mass, per the frozen `|V|³` convention (guard-free on `V = ∅`). -/
noncomputable def badTriadMass (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : ℝ :=
  badTriadMassNum H κ δ / (Fintype.card α : ℝ) ^ 3

theorem badTriadMassNum_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : 0 ≤ badTriadMassNum H κ δ :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem badTriadMass_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : 0 ≤ badTriadMass H κ δ :=
  div_nonneg (badTriadMassNum_nonneg H κ δ) (by positivity)

/-- The bad mass is at most the total injective mass. -/
theorem badTriadMassNum_le_count (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : badTriadMassNum H κ δ ≤ (injectiveTupleCount α 3 : ℝ) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => Nat.cast_nonneg _) (le_of_eq ?_)
  rw [← Nat.cast_sum]
  exact_mod_cast sum_card_polyadBlock κ

theorem badTriadMass_le_one (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : badTriadMass H κ δ ≤ 1 := by
  rw [badTriadMass]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hcard | hcard
  · rw [hcard]
    norm_num
  · rw [div_le_one (by positivity)]
    refine le_trans (badTriadMassNum_le_count H κ δ) ?_
    exact_mod_cast injectiveTupleCount_le_pow (α := α) 3

open Classical in
/-- The exceptional tuple set: all ordered triples living in a bad block. -/
noncomputable def badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : Finset (Fin 3 → α) :=
  (Finset.univ.filter fun key => IsBadTriad H κ δ key).biUnion (polyadBlock κ)

open Classical in
theorem card_badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) :
    (badTriadTuples H κ δ).card
      = ∑ key ∈ Finset.univ.filter (fun key => IsBadTriad H κ δ key),
          (polyadBlock κ key).card := by
  classical
  rw [badTriadTuples]
  exact Finset.card_biUnion fun key _ key' _ h => polyadBlock_disjoint h

theorem cast_card_badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) :
    ((badTriadTuples H κ δ).card : ℝ) = badTriadMassNum H κ δ := by
  classical
  rw [card_badTriadTuples, badTriadMassNum, Nat.cast_sum]

/-! ### Tests and adversarial examples -/

section Tests

-- The complete 3-graph on Fin 3 has one edge and 6 = 3! realized triples.
example :
    ((injectiveTuples (Fin 3) 3).filter (triadObs (complete 3 (Fin 3)))).card
      = 6 := by
  rw [card_realizedTriples]
  decide

-- The empty 3-graph realizes nothing.
example :
    ((injectiveTuples (Fin 3) 3).filter (triadObs (empty 3 (Fin 3)))).card = 0 := by
  rw [card_realizedTriples]
  decide

-- Mass identity on a concrete pair coloring of Fin 4 (color by whether the pair
-- contains 0): realized counts over all 8 keys sum to 6 · #edges of the complete
-- 3-graph on Fin 4 (4 edges → 24).
example :
    ∑ key : Fin 3 → Fin 2,
      blockRealizedCount (complete 3 (Fin 4))
        (fun e : RSet 2 (Fin 4) => if (0 : Fin 4) ∈ e.1 then (1 : Fin 2) else 0)
        key = 24 := by
  rw [sum_blockRealizedCount]
  decide

-- Edit calculus: complete vs empty on Fin 3 differ in the single edge, ordered edit
-- mass 6.
example : editCount (complete 3 (Fin 3)) (empty 3 (Fin 3)) = 1 := by decide

example :
    ((injectiveTuples (Fin 3) 3).filter
      fun v => ¬(triadObs (complete 3 (Fin 3)) v ↔ triadObs (empty 3 (Fin 3)) v)).card
      = 6 := by
  rw [card_editTriples]
  decide

-- A trivial coloring with zero bad mass: the empty hypergraph has all densities 0,
-- so every key is locally regular and no key is bad.
example :
    badTriadMass (empty 3 (Fin 3)) (fun _ : RSet 2 (Fin 3) => (0 : Fin 1))
      (1 / 2) = 0 := by
  classical
  have hobs : ∀ S : Finset (Fin 3 → Fin 3),
      densityOn S (triadObs (empty 3 (Fin 3))) = 0 := by
    intro S
    rw [densityOn, Finset.filter_false_of_mem, Finset.card_empty]
    · norm_num
    · intro v _
      exact Finset.notMem_empty _
  have hgood : ∀ key : Fin 3 → Fin 1,
      ¬ IsBadTriad (empty 3 (Fin 3)) (fun _ => (0 : Fin 1)) (1 / 2) key := by
    intro key
    rw [IsBadTriad, not_not]
    intro P _
    rw [hobs, hobs, sub_zero, abs_zero]
    norm_num
  rw [badTriadMass, badTriadMassNum,
    Finset.filter_false_of_mem fun key _ => hgood key, Finset.sum_empty, zero_div]

-- Permutation closure of bad keys, as a statement-level test.
example (H : UniformHypergraph 3 (Fin 4)) (κ : RSet 2 (Fin 4) → Fin 3) (δ : ℝ)
    (key : Fin 3 → Fin 3) (σ : Equiv.Perm (Fin 3)) :
    IsBadTriad H κ δ (key ∘ ⇑σ⁻¹) ↔ IsBadTriad H κ δ key :=
  isBadTriad_comp_perm_iff H κ δ key σ

-- Permutation invariance of the observable, concretely.
example (v : Fin 3 → Fin 4) (σ : Equiv.Perm (Fin 3)) :
    triadObs (complete 3 (Fin 4)) (v ∘ σ) ↔ triadObs (complete 3 (Fin 4)) v :=
  triadObs_comp_perm _ v σ

end Tests

end RegularityLemmata
