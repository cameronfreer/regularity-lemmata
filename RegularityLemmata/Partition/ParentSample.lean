/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Order.Partition.Finpartition
import RegularityLemmata.Partition.ActiveTraceSchedule
import RegularityLemmata.Partition.ParentSubtypeRekey

/-!
# The per-parent sampling wrapper

The certificate for sampling INSIDE one parent cell: a `Finpartition` of the parent into
exactly `m` blocks of size exactly `s`, with every ambient trace (test set) satisfying the
proportional upper window on every block.  Existence follows the fixed recipe: rekey the trace
family to the parent subtype (`ParentSubtypeRekey`), run the coupled active-trace sampler
(`ActiveTraceSchedule`, at moment order `t/8`), map the sampled blocks back through
`Function.Embedding.subtype`, build the partition, and transfer the intersection counts
losslessly (`card_inter_traceOnParent`).

Schedule-independent: the only quantitative input is the active-trace ratio inequality.  The
upper windows convert to the cross-multiplied estimates consumed by downstream transfer
arguments via `cross_mul_le_of_upper_window`.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-- **The per-parent sample certificate**: an equal partition of the parent `A` into `m`
blocks of size `s`, every ambient trace of `F` proportionally bounded on every block. -/
structure TiledSliceCert (A : Finset α) (F : Finset (Finset α)) (m s t : ℕ) where
  P : Finpartition A
  part_count : P.parts.card = m
  part_card : ∀ p ∈ P.parts, p.card = s
  trace_upper : ∀ T ∈ F, ∀ p ∈ P.parts,
    (T ∩ p).card ≤ (A ∩ T).card * s / A.card + t

open Classical in
/-- **The per-parent sample exists** under the active-trace ratio inequality (stated over the
rekeyed subtype family; inactive traces are discharged exactly by the sampler). -/
theorem tiledSliceCert_exists (A : Finset α) (F : Finset (Finset α)) {m s t : ℕ}
    (hA : A.card = m * s) (hs : 0 < s) (ht : t < s)
    (hchoose : 0 < (m * s).choose s)
    (hratio : m * ((traceFamilyOnParent A F).filter
        fun T ↦ T.card * s / (m * s) + t < s).card * (2 * s - t) ^ (t / 8)
      < (2 * s) ^ (t / 8)) :
    Nonempty (TiledSliceCert A F m s t) := by
  classical
  have hn : Fintype.card {x // x ∈ A} = m * s := by
    rw [Fintype.card_coe]
    exact hA
  obtain ⟨e, he⟩ := exists_equiv_forall_blocks_proportional_eighth_moment hn rfl
    (traceFamilyOnParent A F) hs ht hchoose hratio
  -- the blocks, mapped back to the ambient carrier
  set blk : ℕ → Finset α :=
    fun j ↦ (sampleBlock e s j).map (Function.Embedding.subtype _) with hblkdef
  have hjs : ∀ j, j < m → (j + 1) * s ≤ m * s :=
    fun j hj ↦ Nat.mul_le_mul_right s hj
  have hblk_card : ∀ j, j < m → (blk j).card = s := by
    intro j hj
    rw [hblkdef, Finset.card_map]
    exact card_sampleBlock e (hjs j hj)
  have hblk_sub : ∀ j, blk j ⊆ A := by
    intro j a ha
    rw [hblkdef, Finset.mem_map] at ha
    obtain ⟨⟨a', ha'⟩, _, rfl⟩ := ha
    exact ha'
  have hblk_disj : ∀ i j, i ≠ j → Disjoint (blk i) (blk j) := by
    intro i j hij
    rw [hblkdef, Finset.disjoint_map]
    exact sampleBlock_disjoint e hij
  have hblk_cover : (Finset.range m).biUnion blk = A := by
    ext a
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨j, _, ha⟩
      exact hblk_sub j ha
    · intro ha
      have hsub : (⟨a, ha⟩ : {x // x ∈ A}) ∈
          (Finset.range m).biUnion (fun j ↦ sampleBlock e s j) := by
        rw [biUnion_sampleBlock e rfl]
        exact Finset.mem_univ _
      obtain ⟨j, hj, hmem⟩ := Finset.mem_biUnion.mp hsub
      exact ⟨j, hj, by
        rw [hblkdef, Finset.mem_map]
        exact ⟨⟨a, ha⟩, hmem, rfl⟩⟩
  have hblk_inj : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m, blk i = blk j → i = j := by
    intro i hi j hj hij
    by_contra hne
    have hd := hblk_disj i j hne
    rw [hij] at hd
    have hpos : 0 < (blk j).card := by
      rw [hblk_card j (Finset.mem_range.mp hj)]
      exact hs
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact Finset.disjoint_left.mp hd ha ha
  refine ⟨{
    P := {
      parts := (Finset.range m).image blk
      supIndep := by
        rw [Finset.supIndep_iff_pairwiseDisjoint]
        intro p hp q hq hpq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
        exact hblk_disj i j (fun hij ↦ hpq (congrArg blk hij))
      sup_parts := by
        rw [Finset.sup_image, Function.id_comp, Finset.sup_eq_biUnion]
        exact hblk_cover
      bot_notMem := by
        rw [Finset.bot_eq_empty]
        intro hempty
        obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hempty
        have hpos : 0 < (blk j).card := by
          rw [hblk_card j (Finset.mem_range.mp hj)]
          exact hs
        rw [hje, Finset.card_empty] at hpos
        omega }
    part_count := by
      change ((Finset.range m).image blk).card = m
      rw [Finset.card_image_iff.mpr (fun i hi j hj ↦ hblk_inj i hi j hj), Finset.card_range]
    part_card := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      exact hblk_card j (Finset.mem_range.mp hj)
    trace_upper := by
      intro T hT p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      have hj' := Finset.mem_range.mp hj
      have hbound := he (traceOnParent A T)
        (traceOnParent_mem_traceFamilyOnParent A F hT) j hj'
      have htransfer : (sampleBlock e s j ∩ traceOnParent A T).card
          = ((sampleBlock e s j).map (Function.Embedding.subtype _) ∩ T).card :=
        card_inter_traceOnParent A T (sampleBlock e s j)
      have h1 : (blk j ∩ T).card = (traceOnParent A T ∩ sampleBlock e s j).card := by
        rw [hblkdef]
        rw [← htransfer, Finset.inter_comm]
      have hgoal : (blk j ∩ T).card ≤ (traceOnParent A T).card * s / (m * s) + t := by
        rw [h1]
        exact hbound
      rw [card_traceOnParent] at hgoal
      rw [hA, Finset.inter_comm T (blk j)]
      exact hgoal }⟩

end RegularityLemmata
