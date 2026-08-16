/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Partition.Equipartition

/-!
# Absorbing a leftover into equal-size blocks

Equal-size disjoint blocks covering all but a small complement extend to an **equipartition**
of the whole carrier: each block absorbs at most one leftover element, so every part has size
`s` or `s + 1`. The single hypothesis making this possible is that the leftover is no larger
than the number of blocks.

## Conventions

* **One element per block, not balanced redistribution.** The construction attaches the `i`-th
  leftover element to the `i`-th block under fixed enumerations; blocks with index at least the
  leftover size stay untouched. Sizes land in `{s, s + 1}`, which is exactly
  `Finpartition.IsEquipartition` (`Set.EquitableOn` on cards).
* **The correspondence clause is part of the contract.** Every part contains a designated
  original block; a consumer that has proved a property of each block (e.g. density control
  from `Partition/BalancedSlicing`) transfers it to the parts at the cost of one absorbed
  element — quantitatively, `abs_pairDensity_sub_le_of_grow_one` in `Finite/HomogeneousPair`.
* **Degenerate case.** `blocks = ∅` forces `S = ∅` (empty cover) and then an empty carrier
  (the leftover bound reads `univ.card ≤ 0`); the empty partition witnesses the statement. No
  separate hypothesis excludes this — the construction below handles it uniformly, since the
  index type `Fin 0` is empty.
* **`0 < s` is load-bearing.** Nonempty blocks make the extended parts nonempty, which is what
  makes the part map injective (pairwise-disjoint nonempty sets are distinct) and keeps `⊥`
  out of the parts.

This file sits above the sampling stack and below any graph-level consumer; it imports only
mathlib.
-/

namespace RegularityLemmata

variable {α : Type*}

/-- **Leftover absorption.** Equal-size disjoint blocks covering all but a small complement
extend to an equipartition of the whole carrier: each block absorbs at most one leftover
element, so part sizes lie in `{s, s + 1}`. The correspondence clause lets a consumer
transfer properties proved for the blocks to the parts. -/
theorem exists_equipartition_absorb_leftover [Fintype α] [DecidableEq α]
    {S : Finset α} {blocks : Finset (Finset α)} {s : ℕ} (hs : 0 < s)
    (hdisj : (blocks : Set (Finset α)).PairwiseDisjoint id)
    (hcover : blocks.biUnion id = S)
    (hsize : ∀ b ∈ blocks, b.card = s)
    (hE : (Finset.univ \ S).card ≤ blocks.card) :
    ∃ P : Finpartition (Finset.univ : Finset α),
      P.IsEquipartition ∧
      P.parts.card = blocks.card ∧
      ∀ p ∈ P.parts, ∃ b ∈ blocks, b ⊆ p ∧ p.card ≤ s + 1 := by
  classical
  set E : Finset α := Finset.univ \ S with hEdef
  -- Enumerate the leftover and the blocks.
  let eE : Fin E.card ≃ E := E.equivFin.symm
  let eB : Fin blocks.card ≃ blocks := blocks.equivFin.symm
  -- Blocks sit inside `S`; leftover elements sit outside `S`.
  have hblock_subS : ∀ b ∈ blocks, b ⊆ S := fun b hb ↦ by
    rw [← hcover]
    exact Finset.subset_biUnion_of_mem id hb
  have hE_not_S : ∀ x ∈ E, x ∉ S := fun x hx ↦ (Finset.mem_sdiff.mp hx).2
  -- The extra element (if any) attached to block `i`, and the extended part.
  let extra : Fin blocks.card → Finset α := fun i ↦
    if h : (i : ℕ) < E.card then {((eE ⟨i, h⟩ : E) : α)} else ∅
  let part : Fin blocks.card → Finset α := fun i ↦ ((eB i : blocks) : Finset α) ∪ extra i
  have hextra_def : ∀ i, extra i
      = if h : (i : ℕ) < E.card then {((eE ⟨i, h⟩ : E) : α)} else ∅ := fun _ ↦ rfl
  have hpart_def : ∀ i, part i = ((eB i : blocks) : Finset α) ∪ extra i := fun _ ↦ rfl
  have hextra_subE : ∀ i, extra i ⊆ E := fun i ↦ by
    rw [hextra_def]
    by_cases h : (i : ℕ) < E.card
    · rw [dite_eq_left h, Finset.singleton_subset_iff]
      exact (eE ⟨i, h⟩).2
    · rw [dite_eq_right h]
      exact Finset.empty_subset _
  have hextra_card : ∀ i, (extra i).card ≤ 1 := fun i ↦ by
    rw [hextra_def]
    by_cases h : (i : ℕ) < E.card
    · rw [dite_eq_left h, Finset.card_singleton]
    · rw [dite_eq_right h, Finset.card_empty]
      exact Nat.zero_le _
  -- A block never meets a leftover attachment: they live on opposite sides of `S`.
  have hdisj_be : ∀ i j, Disjoint (((eB i : blocks) : Finset α)) (extra j) := fun i j ↦
    Finset.disjoint_left.mpr fun x hx hx' ↦
      hE_not_S x (hextra_subE j hx') (hblock_subS _ (eB i).2 hx)
  -- Part sizes: exactly the block plus at most one absorbed element.
  have hpart_card_eq : ∀ i, (part i).card = s + (extra i).card := fun i ↦ by
    rw [hpart_def, Finset.card_union_of_disjoint (hdisj_be i i), hsize _ (eB i).2]
  have hpart_card_ge : ∀ i, s ≤ (part i).card := fun i ↦ by
    rw [hpart_card_eq]
    exact Nat.le_add_right _ _
  have hpart_card_le : ∀ i, (part i).card ≤ s + 1 := fun i ↦ by
    rw [hpart_card_eq]
    exact Nat.add_le_add_left (hextra_card i) _
  have hpart_nonempty : ∀ i, (part i).Nonempty := fun i ↦
    Finset.card_pos.mp (lt_of_lt_of_le hs (hpart_card_ge i))
  -- Pairwise disjointness of the extended parts.
  have hpart_disj : ∀ i j, i ≠ j → Disjoint (part i) (part j) := by
    intro i j hij
    rw [hpart_def, hpart_def]
    have hBB : Disjoint (((eB i : blocks) : Finset α)) (((eB j : blocks) : Finset α)) := by
      refine hdisj (eB i).2 (eB j).2 fun hval ↦ hij (eB.injective (Subtype.ext hval))
    have hEE : Disjoint (extra i) (extra j) := by
      rw [hextra_def, hextra_def]
      by_cases hi : (i : ℕ) < E.card
      · by_cases hj : (j : ℕ) < E.card
        · rw [dite_eq_left hi, dite_eq_left hj, Finset.disjoint_singleton_left,
            Finset.mem_singleton]
          intro heq
          have hfin : (⟨(i : ℕ), hi⟩ : Fin E.card) = ⟨(j : ℕ), hj⟩ :=
            eE.injective (Subtype.ext heq)
          have hval : (i : ℕ) = (j : ℕ) := by simpa using hfin
          exact hij (Fin.ext hval)
        · rw [dite_eq_right hj]
          exact Finset.disjoint_empty_right _
      · rw [dite_eq_right hi]
        exact Finset.disjoint_empty_left _
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hBB, hdisj_be i j⟩,
        Finset.disjoint_union_right.mpr ⟨(hdisj_be j i).symm, hEE⟩⟩
  -- Injectivity: pairwise-disjoint nonempty sets are distinct.
  have hpart_inj : Function.Injective part := fun i j hij ↦ by
    by_contra hne
    have hd := hpart_disj i j hne
    rw [hij, disjoint_self, Finset.bot_eq_empty] at hd
    exact (hpart_nonempty j).ne_empty hd
  -- The parts cover everything: `S` through the blocks, the leftover through the attachments.
  have hcover_univ : Finset.univ.sup part = (Finset.univ : Finset α) := by
    refine Finset.Subset.antisymm (Finset.subset_univ _) fun x _ ↦ ?_
    rw [Finset.mem_sup]
    by_cases hxS : x ∈ S
    · rw [← hcover] at hxS
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hxS
      refine ⟨eB.symm ⟨b, hb⟩, Finset.mem_univ _, ?_⟩
      rw [hpart_def]
      refine Finset.mem_union_left _ ?_
      rw [Equiv.apply_symm_apply]
      exact hxb
    · have hxE : x ∈ E := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
      have hjk : ((eE.symm ⟨x, hxE⟩ : Fin E.card) : ℕ) < blocks.card :=
        lt_of_lt_of_le (eE.symm ⟨x, hxE⟩).isLt hE
      refine ⟨⟨(eE.symm ⟨x, hxE⟩ : Fin E.card), hjk⟩, Finset.mem_univ _, ?_⟩
      rw [hpart_def]
      refine Finset.mem_union_right _ ?_
      rw [hextra_def, dite_eq_left (show (((⟨(eE.symm ⟨x, hxE⟩ : Fin E.card), hjk⟩ :
        Fin blocks.card) : ℕ)) < E.card from (eE.symm ⟨x, hxE⟩).isLt)]
      rw [Finset.mem_singleton, Fin.eta, Equiv.apply_symm_apply]
  -- Assemble the partition and its certificates.
  refine ⟨⟨Finset.univ.image part, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `supIndep`, via pairwise disjointness and injectivity.
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    rintro p hp q hq hpq
    rw [Finset.coe_image] at hp hq
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hq
    exact hpart_disj i j fun h ↦ hpq (congrArg part h)
  · -- `sup_parts`: the parts cover the carrier.
    rw [Finset.sup_image, Function.id_comp]
    exact hcover_univ
  · -- `bot_notMem`: parts are nonempty since blocks are.
    intro hbot
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hbot
    rw [Finset.bot_eq_empty] at hi
    exact (hpart_nonempty i).ne_empty hi
  · -- Equipartition: all part sizes lie in `{s, s + 1}`.
    rintro p q hp hq
    rw [Finset.coe_image] at hp hq
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hq
    have h1 := hpart_card_le i
    have h2 := hpart_card_ge j
    omega
  · -- Exactly one part per block.
    rw [Finset.card_image_of_injective _ hpart_inj, Finset.card_univ, Fintype.card_fin]
  · -- Correspondence: each part contains its designated block and has size at most `s + 1`.
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨((eB i : blocks) : Finset α), (eB i).2, ?_, hpart_card_le i⟩
    rw [hpart_def]
    exact Finset.subset_union_left

/-! ### Tests and adversarial examples -/

section Tests

-- Concrete instance: two blocks of size `2` covering `{0, 1, 2, 3} ⊆ Fin 5`, leftover `{4}`.
-- One block absorbs the leftover element, giving an equipartition with part sizes `{2, 3}`.
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 5)),
      P.IsEquipartition ∧
      P.parts.card = ({{0, 1}, {2, 3}} : Finset (Finset (Fin 5))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 5))), b ⊆ p ∧ p.card ≤ 2 + 1 :=
  exists_equipartition_absorb_leftover (S := {0, 1, 2, 3}) two_pos
    (by
      rintro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      fin_cases hx <;> fin_cases hy <;>
        first
          | exact absurd rfl hxy
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 5)) {2, 3})
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 5)) {2, 3}).symm)
    (by decide) (by decide) (by decide)

-- NOTE (adversarial, documented): the leftover bound is sharp at equality — with as many
-- leftover elements as blocks, *every* block absorbs one, and all parts have size `s + 1`.
-- Here: `Fin 6`, two blocks of size `2`, leftover `{4, 5}` of size `2 = blocks.card`.
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 6)),
      P.IsEquipartition ∧
      P.parts.card = ({{0, 1}, {2, 3}} : Finset (Finset (Fin 6))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 6))), b ⊆ p ∧ p.card ≤ 2 + 1 :=
  exists_equipartition_absorb_leftover (S := {0, 1, 2, 3}) two_pos
    (by
      rintro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      fin_cases hx <;> fin_cases hy <;>
        first
          | exact absurd rfl hxy
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 6)) {2, 3})
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 6)) {2, 3}).symm)
    (by decide) (by decide) (by decide)

-- Degenerate case: no blocks. The empty cover forces `S = ∅`, and the leftover bound then
-- forces an empty carrier; the theorem still applies and delivers the empty partition.
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 0)),
      P.IsEquipartition ∧
      P.parts.card = (∅ : Finset (Finset (Fin 0))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ (∅ : Finset (Finset (Fin 0))), b ⊆ p ∧ p.card ≤ 1 + 1 :=
  exists_equipartition_absorb_leftover (S := ∅) one_pos
    (by rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty)
    (by decide) (by decide) (by decide)

end Tests

end RegularityLemmata
