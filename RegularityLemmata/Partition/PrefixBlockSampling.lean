/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.ParentSample

/-!
# Prefix block sampling with an unused tail

The exact parent sampler requires the parent cardinality to be divisible by the common block
size.  General slices of the carrier do not have that divisibility.  This module generalizes
the simultaneous, proportional, and active-trace samplers to the first `m` blocks of a
permutation under `m * s ≤ n`, then packages those blocks as `SliceCert`.

At `m = |A| / s`, the blocks leave exactly `|A| % s < s` vertices.  This is the
remainder-aware sampling primitive for parents whose size is not divisible by the block size;
it makes no claim about any downstream endpoint.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Simultaneous sampling on the first `m` size-`s` blocks of a permutation.  Unlike the
exact-tiling theorem, this leaves an unused tail when `m * s < n`. -/
theorem exists_equiv_forall_prefix_blocks_window {n s m : ℕ}
    (hn : Fintype.card α = n) (hms : m * s ≤ n)
    (F : Finset (Finset α)) (lo hi : Finset α → ℕ)
    (hsum : m * ∑ A ∈ F,
        ((upperViolations A s (hi A)).card + (lowerViolations A s (lo A)).card)
      < n.choose s) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      lo A ≤ (A ∩ sampleBlock e s j).card ∧
        (A ∩ sampleBlock e s j).card ≤ hi A := by
  classical
  have hs : s ≤ n := by
    by_contra hsn
    push Not at hsn
    rw [Nat.choose_eq_zero_of_lt hsn] at hsum
    omega
  set I := {A // A ∈ F} × Fin m × Bool with hI
  set fam : I → Finset (Finset α) := fun i ↦
    Bool.rec (lowerViolations i.1.1 s (lo i.1.1))
      (upperViolations i.1.1 s (hi i.1.1)) i.2.2 with hfamdef
  have hblk : ∀ i : I, ((i.2.1 : ℕ) + 1) * s ≤ n := by
    intro i
    exact (Nat.mul_le_mul_right s i.2.1.isLt).trans hms
  have hfam : ∀ i : I, ∀ S ∈ fam i, S.card = s := by
    rintro ⟨A, j, b⟩ S hS
    have hpow : S ∈ ((Finset.univ : Finset α).powersetCard s) := by
      cases b <;> exact (Finset.mem_filter.mp hS).1
    exact (Finset.mem_powersetCard.mp hpow).2
  have htotal : ∑ i : I, (fam i).card < n.choose s := by
    calc
      ∑ i : I, (fam i).card =
          ∑ A : {A // A ∈ F}, ∑ j : Fin m, ∑ b : Bool,
            (fam (A, j, b)).card := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun A _ ↦ Fintype.sum_prod_type _
      _ = ∑ A : {A // A ∈ F},
            m * ((upperViolations A.1 s (hi A.1)).card +
              (lowerViolations A.1 s (lo A.1)).card) := by
        refine Finset.sum_congr rfl fun A _ ↦ ?_
        have hb : ∀ j : Fin m, ∑ b : Bool, (fam (A, j, b)).card =
            (upperViolations A.1 s (hi A.1)).card +
              (lowerViolations A.1 s (lo A.1)).card := by
          intro j
          rw [Fintype.sum_bool]
        rw [Finset.sum_congr rfl fun j _ ↦ hb j, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = m * ∑ A ∈ F,
            ((upperViolations A s (hi A)).card +
              (lowerViolations A s (lo A)).card) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort F fun A ↦
          (upperViolations A s (hi A)).card +
            (lowerViolations A s (lo A)).card
      _ < n.choose s := hsum
  obtain ⟨e, he⟩ := exists_equiv_avoids_all hn hs
    (fun i : I ↦ (i.2.1 : ℕ)) fam hblk hfam htotal
  refine ⟨e, fun A hA j hj ↦ ?_⟩
  have hjs : (j + 1) * s ≤ n :=
    (Nat.mul_le_mul_right s hj).trans hms
  have hSmem : sampleBlock e s j ∈
      ((Finset.univ : Finset α).powersetCard s) :=
    Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, card_sampleBlock e hjs⟩
  constructor
  · have hnotlow := he (⟨A, hA⟩, ⟨j, hj⟩, false)
    by_contra hlt
    push Not at hlt
    exact hnotlow (Finset.mem_filter.mpr ⟨hSmem, hlt⟩)
  · have hnothigh := he (⟨A, hA⟩, ⟨j, hj⟩, true)
    by_contra hlt
    push Not at hlt
    exact hnothigh (Finset.mem_filter.mpr ⟨hSmem, hlt⟩)

/-- One-sided proportional sampling on an initial family of disjoint equal blocks, leaving
an unused tail when the ambient cardinality is not divisible by the block size. -/
theorem exists_equiv_forall_prefix_blocks_upper {n s m : ℕ}
    (hn : Fintype.card α = n) (hms : m * s ≤ n)
    (F : Finset (Finset α)) (hi : Finset α → ℕ)
    (hsum : m * ∑ C ∈ F, (upperViolations C s (hi C)).card < n.choose s) :
    ∃ e : Fin n ≃ α, ∀ C ∈ F, ∀ j, j < m →
      (C ∩ sampleBlock e s j).card ≤ hi C := by
  have hsum' : m * ∑ C ∈ F,
      ((upperViolations C s (hi C)).card + (lowerViolations C s 0).card) <
        n.choose s := by
    have hzero : ∀ C ∈ F,
        (upperViolations C s (hi C)).card + (lowerViolations C s 0).card =
          (upperViolations C s (hi C)).card := by
      intro C _
      rw [lowerViolations_zero, Finset.card_empty, Nat.add_zero]
    rw [Finset.sum_congr rfl hzero]
    exact hsum
  obtain ⟨e, he⟩ :=
    exists_equiv_forall_prefix_blocks_window hn hms F (fun _ ↦ 0) hi hsum'
  exact ⟨e, fun C hC j hj ↦ (he C hC j hj).2⟩

/-- Active-trace proportional sampling on a prefix of disjoint size-`s` blocks. -/
theorem exists_equiv_forall_prefix_blocks_proportional_of_active_ratio
    {n s m t r : ℕ} (hn : Fintype.card α = n) (hms : m * s ≤ n)
    (F : Finset (Finset α)) (hs : 0 < s) (ht : t < s) (hr : 8 * r ≤ t)
    (hchoose : 0 < n.choose s)
    (hratio : m * (F.filter fun A ↦ A.card * s / n + t < s).card *
        (2 * s - t) ^ r < (2 * s) ^ r) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ A.card * s / n + t := by
  let active := F.filter fun A ↦ A.card * s / n + t < s
  have hsn : s ≤ n := by
    by_contra h
    push Not at h
    rw [Nat.choose_eq_zero_of_lt h] at hchoose
    omega
  have htail : ∀ A ∈ active,
      (upperViolations A s (A.card * s / n + t)).card * (2 * s) ^ r ≤
        n.choose s * (2 * s - t) ^ r := by
    intro A hA
    exact card_upperViolations_mul_pow_le A hn hs hsn ht hr
      (Finset.mem_filter.mp hA).2
  have hD : 0 < (2 * s) ^ r := pow_pos (by omega) r
  have hsum : m * ∑ A ∈ active,
      (upperViolations A s (A.card * s / n + t)).card < n.choose s :=
    sum_bad_lt_of_mul_le_and_event_ratio active
      (fun A ↦ (upperViolations A s (A.card * s / n + t)).card)
      hchoose hD htail (by simpa [active] using hratio)
  obtain ⟨e, he⟩ :=
    exists_equiv_forall_prefix_blocks_upper
      hn hms active (fun A ↦ A.card * s / n + t) hsum
  refine ⟨e, fun A hA j hj ↦ ?_⟩
  by_cases hactive : A.card * s / n + t < s
  · exact he A (Finset.mem_filter.mpr ⟨hA, hactive⟩) j hj
  · have hjs : (j + 1) * s ≤ n :=
      (Nat.mul_le_mul_right s hj).trans hms
    calc
      (A ∩ sampleBlock e s j).card ≤ (sampleBlock e s j).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = s := card_sampleBlock e hjs
      _ ≤ A.card * s / n + t := by omega

/-- Concrete eighth-moment prefix sampler. -/
theorem exists_equiv_forall_prefix_blocks_proportional_eighth_moment
    {n s m t : ℕ} (hn : Fintype.card α = n) (hms : m * s ≤ n)
    (F : Finset (Finset α)) (hs : 0 < s) (ht : t < s)
    (hchoose : 0 < n.choose s)
    (hratio : m * (F.filter fun A ↦ A.card * s / n + t < s).card *
        (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8)) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ A.card * s / n + t := by
  exact exists_equiv_forall_prefix_blocks_proportional_of_active_ratio
    hn hms F hs ht (eighth_moment_le_slack t) hchoose hratio

section SliceCert

variable {α : Type*} [DecidableEq α]

/-- A sampled prefix of disjoint equal blocks inside a parent, without requiring the blocks to
cover the parent. -/
structure SliceCert (A : Finset α) (F : Finset (Finset α)) (m s t : ℕ) where
  block : Fin m → Finset α
  block_card : ∀ j, (block j).card = s
  block_subset : ∀ j, block j ⊆ A
  block_disjoint : ∀ {i j}, i ≠ j → Disjoint (block i) (block j)
  trace_upper : ∀ T ∈ F, ∀ j,
    (T ∩ block j).card ≤ (A ∩ T).card * s / A.card + t

namespace SliceCert

variable {A : Finset α} {F : Finset (Finset α)} {m s t : ℕ}

/-- The union of all sampled prefix blocks. -/
def covered (cert : SliceCert A F m s t) : Finset α :=
  Finset.univ.biUnion cert.block

/-- The unused tail of the parent. -/
def leftover (cert : SliceCert A F m s t) : Finset α :=
  A \ cert.covered

theorem covered_subset (cert : SliceCert A F m s t) : cert.covered ⊆ A := by
  intro x hx
  rw [covered, Finset.mem_biUnion] at hx
  obtain ⟨j, _, hxj⟩ := hx
  exact cert.block_subset j hxj

theorem card_covered (cert : SliceCert A F m s t) : cert.covered.card = m * s := by
  rw [covered, Finset.card_biUnion]
  · simp [cert.block_card]
  · intro i _ j _ hij
    exact cert.block_disjoint hij

theorem card_leftover (cert : SliceCert A F m s t) :
    cert.leftover.card = A.card - m * s := by
  rw [leftover, Finset.card_sdiff_of_subset cert.covered_subset, cert.card_covered]

theorem card_leftover_eq_mod (cert : SliceCert A F (A.card / s) s t) :
    cert.leftover.card = A.card % s := by
  rw [cert.card_leftover]
  have hmod := Nat.mod_add_div A.card s
  rw [Nat.add_comm, Nat.mul_comm] at hmod
  omega

theorem card_leftover_lt (cert : SliceCert A F (A.card / s) s t) (hs : 0 < s) :
    cert.leftover.card < s := by
  rw [cert.card_leftover_eq_mod]
  exact Nat.mod_lt _ hs

end SliceCert

open Classical in
/-- A prefix sample exists under the same active-trace ratio as the exact parent sampler. -/
theorem sliceCert_exists (A : Finset α) (F : Finset (Finset α)) {m s t : ℕ}
    (hms : m * s ≤ A.card) (hs : 0 < s) (ht : t < s)
    (hchoose : 0 < A.card.choose s)
    (hratio : m * ((traceFamilyOnParent A F).filter
        fun T ↦ T.card * s / A.card + t < s).card *
          (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8)) :
    Nonempty (SliceCert A F m s t) := by
  classical
  have hn : Fintype.card {x // x ∈ A} = A.card := Fintype.card_coe A
  obtain ⟨e, he⟩ :=
    exists_equiv_forall_prefix_blocks_proportional_eighth_moment
      hn hms (traceFamilyOnParent A F) hs ht hchoose hratio
  let blk : Fin m → Finset α := fun j ↦
    (sampleBlock e s j).map (Function.Embedding.subtype _)
  have hjs : ∀ j : Fin m, ((j : ℕ) + 1) * s ≤ A.card := by
    intro j
    exact (Nat.mul_le_mul_right s j.isLt).trans hms
  refine ⟨{
    block := blk
    block_card := ?_
    block_subset := ?_
    block_disjoint := ?_
    trace_upper := ?_
  }⟩
  · intro j
    change ((sampleBlock e s j).map (Function.Embedding.subtype _)).card = s
    rw [Finset.card_map]
    exact card_sampleBlock e (hjs j)
  · intro j a ha
    change a ∈ (sampleBlock e s j).map (Function.Embedding.subtype _) at ha
    rw [Finset.mem_map] at ha
    obtain ⟨⟨a', ha'⟩, _, rfl⟩ := ha
    exact ha'
  · intro i j hij
    change Disjoint
      ((sampleBlock e s i).map (Function.Embedding.subtype _))
      ((sampleBlock e s j).map (Function.Embedding.subtype _))
    rw [Finset.disjoint_map]
    exact sampleBlock_disjoint e (fun h ↦ hij (Fin.ext h))
  · intro T hT j
    have hbound := he (traceOnParent A T)
      (traceOnParent_mem_traceFamilyOnParent A F hT) j j.isLt
    have htransfer : (sampleBlock e s j ∩ traceOnParent A T).card =
        ((sampleBlock e s j).map (Function.Embedding.subtype _) ∩ T).card :=
      card_inter_traceOnParent A T (sampleBlock e s j)
    have heq : (blk j ∩ T).card =
        (traceOnParent A T ∩ sampleBlock e s j).card := by
      change
        ((sampleBlock e s j).map (Function.Embedding.subtype _) ∩ T).card = _
      rw [← htransfer, Finset.inter_comm]
    rw [Finset.inter_comm T (blk j), heq]
    simpa [card_traceOnParent] using hbound

open Classical in
/-- Floor-many prefix blocks exist under the active ratio without a separate choose-positivity
premise.  If the parent is thinner than one block, the demanded family is empty, so the
certificate is canonical even though `A.card.choose s = 0`. -/
theorem sliceCert_floor_exists (A : Finset α) (F : Finset (Finset α)) {s t : ℕ}
    (hs : 0 < s) (ht : t < s)
    (hratio : (A.card / s) *
        ((traceFamilyOnParent A F).filter
          fun T ↦ T.card * s / A.card + t < s).card *
          (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8)) :
    Nonempty (SliceCert A F (A.card / s) s t) := by
  by_cases hsize : s ≤ A.card
  · exact sliceCert_exists A F (Nat.div_mul_le_self A.card s) hs ht
      (Nat.choose_pos hsize) hratio
  · have hzero : A.card / s = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hsize)
    rw [hzero]
    exact ⟨{
      block := fun j ↦ Fin.elim0 j
      block_card := fun j ↦ Fin.elim0 j
      block_subset := fun j ↦ Fin.elim0 j
      block_disjoint := fun {i} _ ↦ Fin.elim0 i
      trace_upper := fun _ _ j ↦ Fin.elim0 j
    }⟩

end SliceCert

/-! ### Tests and adversarial examples

Remainder-aware sanity checks: a genuinely nondivisible parent, the exact one-vertex tail it
leaves, and the thin parent on which the old choose-positivity premise fails but the
floor-many wrapper still returns the canonical zero-block certificate. -/

-- A genuinely nondivisible parent (`5 = 2 * 2 + 1`) admits two sampled blocks.
example : Nonempty (SliceCert (Finset.univ : Finset (Fin 5)) ∅ 2 2 1) := by
  apply sliceCert_exists
  · decide
  · decide
  · decide
  · decide
  · decide

-- Every such prefix certificate leaves exactly the one-vertex division tail.
example (cert : SliceCert (Finset.univ : Finset (Fin 5)) ∅ 2 2 1) :
    cert.leftover.card = 1 := by
  rw [cert.card_leftover]
  decide

-- The old choose-positivity premise genuinely fails below one full block.
example : (Finset.univ : Finset (Fin 1)).card.choose 2 = 0 := by decide

-- The floor-many wrapper still returns the canonical zero-block certificate on a thin parent.
example :
    Nonempty (SliceCert (Finset.univ : Finset (Fin 1)) ∅
      ((Finset.univ : Finset (Fin 1)).card / 2) 2 1) := by
  apply sliceCert_floor_exists
  · decide
  · decide
  · decide

end RegularityLemmata
