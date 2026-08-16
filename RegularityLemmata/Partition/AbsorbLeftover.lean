/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Partition.Equipartition

/-!
# Absorbing a leftover into equal-size blocks

Equal-size disjoint blocks covering all but a small complement extend to an **equipartition**
of the whole carrier: each block absorbs at most one leftover element, so every part has size
`s` or `s + 1`. The single hypothesis making this possible is that the leftover is no larger
than the number of blocks.

When the leftover may exceed the number of blocks, `exists_equipartition_absorb_chunks`
instead splits it into near-equal chunks, one per block (balanced interval chunking of an
enumeration of the remainder): with `q` the chunk floor `(univ \ S).card / blocks.card`,
part sizes land in `{s + q, s + q + 1}`, again an equipartition with the same part count.
The only hypothesis beyond the one-element version's is `blocks.Nonempty` (so that the
chunk floor is meaningful); the leftover bound disappears.

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

/-- **Chunk absorption.** Exact-size disjoint blocks covering all but a remainder extend to an
equipartition of the whole carrier with the same part count: the remainder splits into
near-equal chunks, one per block, so part sizes take at most two consecutive values. The
correspondence clause bounds each part by `s + q + 1` where `q` is the chunk floor
`(univ \ S).card / blocks.card`. -/
theorem exists_equipartition_absorb_chunks [Fintype α] [DecidableEq α]
    {S : Finset α} {blocks : Finset (Finset α)} {s : ℕ} (hs : 0 < s)
    (hbne : blocks.Nonempty)
    (hdisj : (blocks : Set (Finset α)).PairwiseDisjoint id)
    (hcover : blocks.biUnion id = S)
    (hsize : ∀ b ∈ blocks, b.card = s) :
    ∃ P : Finpartition (Finset.univ : Finset α),
      P.IsEquipartition ∧
      P.parts.card = blocks.card ∧
      ∀ p ∈ P.parts, ∃ b ∈ blocks, b ⊆ p ∧
        p.card ≤ s + (Finset.univ \ S).card / blocks.card + 1 := by
  classical
  set E : Finset α := Finset.univ \ S with hEdef
  set k : ℕ := blocks.card with hkdef
  have hk : 0 < k := Finset.card_pos.mpr hbne
  set q : ℕ := E.card / k with hqdef
  set r : ℕ := E.card % k with hrdef
  have hr : r < k := Nat.mod_lt _ hk
  -- Keep `q` and `r` opaque below: their defining equations are `hqdef` and `hrdef`.
  clear_value q r
  -- Balanced interval endpoints: chunk `j` receives the remainder indices in `[lo j, lo (j+1))`.
  let lo : ℕ → ℕ := fun j ↦ j * q + min j r
  have hlo_def : ∀ j, lo j = j * q + min j r := fun _ ↦ rfl
  have hlo_zero : lo 0 = 0 := by simp [hlo_def]
  have hlo_succ : ∀ j, lo (j + 1) = j * q + q + min (j + 1) r := fun j ↦ by
    rw [hlo_def, Nat.succ_mul]
  have hlo_k : lo k = E.card := by
    rw [hlo_def, min_eq_right hr.le, hqdef, hrdef]
    exact Nat.div_add_mod E.card k
  have hlo_mono : ∀ i j, i ≤ j → lo i ≤ lo j := fun i j hij ↦ by
    rw [hlo_def, hlo_def]
    exact Nat.add_le_add (Nat.mul_le_mul hij le_rfl) (min_le_min hij le_rfl)
  -- Interval lengths are `q` or `q + 1`: exactly the balanced chunk sizes.
  have hlo_step : ∀ j, lo j + q ≤ lo (j + 1) ∧ lo (j + 1) ≤ lo j + q + 1 := fun j ↦ by
    rw [hlo_succ, hlo_def]
    generalize j * q = m
    omega
  -- Enumerate the remainder; `emb` sends an index to the corresponding remainder element.
  let eE : Fin E.card ≃ E := E.equivFin.symm
  let emb : Fin E.card → α := fun t ↦ ((eE t : E) : α)
  have hemb_def : ∀ t, emb t = ((eE t : E) : α) := fun _ ↦ rfl
  have hemb_inj : Function.Injective emb := fun t t' h ↦ eE.injective (Subtype.ext h)
  have hemb_mem : ∀ t, emb t ∈ E := fun t ↦ (eE t).2
  -- Chunk `j`: the remainder elements whose enumeration index lies in `[lo j, lo (j+1))`.
  let chunk : ℕ → Finset α := fun j ↦
    (((Finset.Ico (lo j) (lo (j + 1))).filter (· < E.card)).attachFin
      fun m hm ↦ (Finset.mem_filter.mp hm).2).image emb
  have hchunk_def : ∀ j, chunk j
      = (((Finset.Ico (lo j) (lo (j + 1))).filter (· < E.card)).attachFin
          fun m hm ↦ (Finset.mem_filter.mp hm).2).image emb := fun _ ↦ rfl
  have hmem_chunk : ∀ j x, x ∈ chunk j ↔
      ∃ t : Fin E.card, (lo j ≤ (t : ℕ) ∧ (t : ℕ) < lo (j + 1)) ∧ emb t = x := fun j x ↦ by
    rw [hchunk_def]
    simp only [Finset.mem_image, Finset.mem_attachFin, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨t, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨t, ⟨⟨h1, h2⟩, t.isLt⟩, rfl⟩
  have hchunk_subE : ∀ j, chunk j ⊆ E := fun j x hx ↦ by
    obtain ⟨t, -, htx⟩ := (hmem_chunk j x).mp hx
    exact htx ▸ hemb_mem t
  -- For `j < k` the index interval sits inside `[0, E.card)`, so the chunk has its full size.
  have hchunk_card : ∀ j, j < k → (chunk j).card = lo (j + 1) - lo j := fun j hj ↦ by
    rw [hchunk_def, Finset.card_image_of_injective _ hemb_inj, Finset.card_attachFin]
    have hfil : (Finset.Ico (lo j) (lo (j + 1))).filter (· < E.card)
        = Finset.Ico (lo j) (lo (j + 1)) :=
      Finset.filter_true_of_mem fun m hm ↦
        lt_of_lt_of_le (Finset.mem_Ico.mp hm).2 (hlo_k ▸ hlo_mono (j + 1) k hj)
    rw [hfil, Nat.card_Ico]
  have hchunk_card_bounds : ∀ j, j < k → q ≤ (chunk j).card ∧ (chunk j).card ≤ q + 1 :=
    fun j hj ↦ by
      have hc := hchunk_card j hj
      have hstep := hlo_step j
      omega
  -- Chunks are pairwise disjoint: their index intervals are, and `emb` is injective.
  have hchunk_disj : ∀ i j : ℕ, i ≠ j → Disjoint (chunk i) (chunk j) := fun i j hij ↦
    Finset.disjoint_left.mpr fun x hxi hxj ↦ by
      obtain ⟨t, ⟨hti1, hti2⟩, htx⟩ := (hmem_chunk i x).mp hxi
      obtain ⟨t', ⟨htj1, htj2⟩, ht'x⟩ := (hmem_chunk j x).mp hxj
      obtain rfl : t = t' := hemb_inj (htx.trans ht'x.symm)
      rcases Nat.lt_or_ge i j with h | h
      · have hle : lo (i + 1) ≤ lo j := hlo_mono (i + 1) j h
        omega
      · have hji : j < i := lt_of_le_of_ne h (Ne.symm hij)
        have hle : lo (j + 1) ≤ lo i := hlo_mono (j + 1) i hji
        omega
  -- Chunks cover the remainder: every index lands in the interval of its `findGreatest` chunk.
  have hchunk_cover : ∀ x ∈ E, ∃ j, j < k ∧ x ∈ chunk j := fun x hx ↦ by
    set t : Fin E.card := eE.symm ⟨x, hx⟩ with htdef
    have htx : emb t = x := by rw [hemb_def, htdef, Equiv.apply_symm_apply]
    have htlt : (t : ℕ) < lo k := by rw [hlo_k]; exact t.isLt
    set j : ℕ := Nat.findGreatest (fun i ↦ lo i ≤ (t : ℕ)) k with hjdef
    have hj0 : lo 0 ≤ (t : ℕ) := by rw [hlo_zero]; exact Nat.zero_le _
    have hj_spec : lo j ≤ (t : ℕ) :=
      Nat.findGreatest_spec (P := fun i ↦ lo i ≤ (t : ℕ)) (Nat.zero_le k) hj0
    have hjk : j < k :=
      lt_of_le_of_ne (Nat.findGreatest_le (P := fun i ↦ lo i ≤ (t : ℕ)) k) fun hjeq ↦ by
        rw [hjeq] at hj_spec
        omega
    have hj_max : ¬ lo (j + 1) ≤ (t : ℕ) :=
      Nat.findGreatest_is_greatest (P := fun i ↦ lo i ≤ (t : ℕ)) (Nat.lt_succ_self j) hjk
    exact ⟨j, hjk, (hmem_chunk j x).mpr ⟨t, ⟨hj_spec, by omega⟩, htx⟩⟩
  -- Enumerate the blocks; the part with index `i` is block `i` together with chunk `i`.
  let eB : Fin k ≃ blocks := blocks.equivFin.symm
  have hblock_subS : ∀ b ∈ blocks, b ⊆ S := fun b hb ↦ by
    rw [← hcover]
    exact Finset.subset_biUnion_of_mem id hb
  have hE_not_S : ∀ x ∈ E, x ∉ S := fun x hx ↦ (Finset.mem_sdiff.mp hx).2
  let part : Fin k → Finset α := fun i ↦ ((eB i : blocks) : Finset α) ∪ chunk (i : ℕ)
  have hpart_def : ∀ i, part i = ((eB i : blocks) : Finset α) ∪ chunk (i : ℕ) := fun _ ↦ rfl
  -- A block never meets a chunk: they live on opposite sides of `S`.
  have hdisj_bc : ∀ (i : Fin k) (j : ℕ), Disjoint (((eB i : blocks) : Finset α)) (chunk j) :=
    fun i j ↦ Finset.disjoint_left.mpr fun x hx hx' ↦
      hE_not_S x (hchunk_subE j hx') (hblock_subS _ (eB i).2 hx)
  -- Part sizes: the block plus its chunk, hence `s + q` or `s + q + 1`.
  have hpart_card_eq : ∀ i, (part i).card = s + (chunk (i : ℕ)).card := fun i ↦ by
    rw [hpart_def, Finset.card_union_of_disjoint (hdisj_bc i (i : ℕ)), hsize _ (eB i).2]
  have hpart_card_ge : ∀ i, s + q ≤ (part i).card := fun i ↦ by
    rw [hpart_card_eq]
    exact Nat.add_le_add_left (hchunk_card_bounds (i : ℕ) i.isLt).1 _
  have hpart_card_le : ∀ i, (part i).card ≤ s + q + 1 := fun i ↦ by
    rw [hpart_card_eq]
    have h := (hchunk_card_bounds (i : ℕ) i.isLt).2
    omega
  have hpart_nonempty : ∀ i, (part i).Nonempty := fun i ↦
    Finset.card_pos.mp (by rw [hpart_card_eq]; omega)
  -- Pairwise disjointness of the extended parts.
  have hpart_disj : ∀ i j, i ≠ j → Disjoint (part i) (part j) := by
    intro i j hij
    rw [hpart_def, hpart_def]
    have hBB : Disjoint (((eB i : blocks) : Finset α)) (((eB j : blocks) : Finset α)) := by
      refine hdisj (eB i).2 (eB j).2 fun hval ↦ hij (eB.injective (Subtype.ext hval))
    have hCC : Disjoint (chunk (i : ℕ)) (chunk (j : ℕ)) :=
      hchunk_disj _ _ fun hval ↦ hij (Fin.ext hval)
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hBB, hdisj_bc i (j : ℕ)⟩,
        Finset.disjoint_union_right.mpr ⟨(hdisj_bc j (i : ℕ)).symm, hCC⟩⟩
  -- Injectivity: pairwise-disjoint nonempty sets are distinct.
  have hpart_inj : Function.Injective part := fun i j hij ↦ by
    by_contra hne
    have hd := hpart_disj i j hne
    rw [hij, disjoint_self, Finset.bot_eq_empty] at hd
    exact (hpart_nonempty j).ne_empty hd
  -- The parts cover everything: `S` through the blocks, the remainder through the chunks.
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
      obtain ⟨j, hjk, hxj⟩ := hchunk_cover x hxE
      refine ⟨⟨j, hjk⟩, Finset.mem_univ _, ?_⟩
      rw [hpart_def]
      exact Finset.mem_union_right _ hxj
  -- Assemble the partition and its certificates.
  refine ⟨⟨Finset.univ.image part, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `supIndep`, via pairwise disjointness and injectivity.
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    rintro p hp p' hp' hne
    rw [Finset.coe_image] at hp hp'
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hp'
    exact hpart_disj i j fun h ↦ hne (congrArg part h)
  · -- `sup_parts`: the parts cover the carrier.
    rw [Finset.sup_image, Function.id_comp]
    exact hcover_univ
  · -- `bot_notMem`: parts are nonempty since blocks are.
    intro hbot
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hbot
    rw [Finset.bot_eq_empty] at hi
    exact (hpart_nonempty i).ne_empty hi
  · -- Equipartition: all part sizes lie in `{s + q, s + q + 1}`.
    rintro p p' hp hp'
    rw [Finset.coe_image] at hp hp'
    obtain ⟨i, -, rfl⟩ := hp
    obtain ⟨j, -, rfl⟩ := hp'
    have h1 := hpart_card_le i
    have h2 := hpart_card_ge j
    omega
  · -- Exactly one part per block.
    rw [Finset.card_image_of_injective _ hpart_inj, Finset.card_univ, Fintype.card_fin]
  · -- Correspondence: each part contains its designated block, within the chunked size bound.
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
    (by decide) (by intro b hb; fin_cases hb <;> rfl) (by decide)

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

-- Chunk absorption with a remainder *larger* than the number of blocks: two blocks of size
-- `2` covering `{0, ..., 3} ⊆ Fin 7`, remainder `{4, 5, 6}` of size `3 > 2`. Here `q = 1`,
-- `r = 1`: one chunk of size `2` and one of size `1`, so parts have sizes `4` and `3`.
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 7)),
      P.IsEquipartition ∧
      P.parts.card = ({{0, 1}, {2, 3}} : Finset (Finset (Fin 7))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 7))), b ⊆ p ∧
        p.card ≤ 2 + (Finset.univ \ ({0, 1, 2, 3} : Finset (Fin 7))).card
          / ({{0, 1}, {2, 3}} : Finset (Finset (Fin 7))).card + 1 :=
  exists_equipartition_absorb_chunks (S := {0, 1, 2, 3}) two_pos ⟨{0, 1}, by decide⟩
    (by
      rintro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      fin_cases hx <;> fin_cases hy <;>
        first
          | exact absurd rfl hxy
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 7)) {2, 3})
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 7)) {2, 3}).symm)
    (by decide) (by intro b hb; fin_cases hb <;> rfl)

-- Remainder-empty case: the blocks already cover the carrier, `q = 0`, and chunk absorption
-- reduces to the pure block partition (all parts of size exactly `2`).
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 4)),
      P.IsEquipartition ∧
      P.parts.card = ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))), b ⊆ p ∧
        p.card ≤ 2 + (Finset.univ \ ({0, 1, 2, 3} : Finset (Fin 4))).card
          / ({{0, 1}, {2, 3}} : Finset (Finset (Fin 4))).card + 1 :=
  exists_equipartition_absorb_chunks (S := {0, 1, 2, 3}) two_pos ⟨{0, 1}, by decide⟩
    (by
      rintro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      fin_cases hx <;> fin_cases hy <;>
        first
          | exact absurd rfl hxy
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3})
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 4)) {2, 3}).symm)
    (by decide) (by intro b hb; fin_cases hb <;> rfl)

-- NOTE (adversarial, documented): remainder smaller than the block count (`E.card < k`), the
-- regime where balanced chunking degenerates — `q = 0`, `r = 1`: one block absorbs the single
-- leftover element (part sizes `3` and `2`), and the other block's chunk is empty.
example :
    ∃ P : Finpartition (Finset.univ : Finset (Fin 5)),
      P.IsEquipartition ∧
      P.parts.card = ({{0, 1}, {2, 3}} : Finset (Finset (Fin 5))).card ∧
      ∀ p ∈ P.parts, ∃ b ∈ ({{0, 1}, {2, 3}} : Finset (Finset (Fin 5))), b ⊆ p ∧
        p.card ≤ 2 + (Finset.univ \ ({0, 1, 2, 3} : Finset (Fin 5))).card
          / ({{0, 1}, {2, 3}} : Finset (Finset (Fin 5))).card + 1 :=
  exists_equipartition_absorb_chunks (S := {0, 1, 2, 3}) two_pos ⟨{0, 1}, by decide⟩
    (by
      rintro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      fin_cases hx <;> fin_cases hy <;>
        first
          | exact absurd rfl hxy
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 5)) {2, 3})
          | exact (by decide : Disjoint ({0, 1} : Finset (Fin 5)) {2, 3}).symm)
    (by decide) (by intro b hb; fin_cases hb <;> rfl)

end Tests

end RegularityLemmata
