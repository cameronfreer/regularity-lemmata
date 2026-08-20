/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.AverageSlicing

/-!
# Common-size blocks across a partition

Every piece of a partition sliced into blocks of one **common** exact size `m`, each block
staying inside its piece and keeping the averages of that piece's `[0,1]`-valued function
family within `2νs + (1 + νs)β` of the piece average. The uncovered remainder — the
original exceptional set plus one sub-`m` leftover per piece — has mass at most
`|A₀| + ν|X|` when `m ≤ ν|Aᵢ|` for every piece. Even redistribution of the remainder is
`exists_equipartition_absorb_chunks`; the two compose at the consumer.
-/

namespace RegularityLemmata

variable {α : Type*}

/-- **Common-size blocks**: slicing every piece of a partition at one exact block size `m`,
under the per-piece ratio hypothesis. The remainder collects the exceptional set and the
sub-`m` leftovers; each block remembers a piece it lives in and the two-sided average
control against that piece. -/
theorem exists_common_blocks [DecidableEq α]
    {X A₀ : Finset α} {s : ℕ} {A : Fin s → Finset α}
    {q m t : ℕ} (φ : Fin s → Fin q → α → ℝ) {β ν νs : ℝ}
    (hcover : A₀ ∪ Finset.univ.biUnion A = X)
    (hdisj0 : ∀ i, Disjoint (A i) A₀)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i'))
    (hm0 : 0 < m) (ht : t < m) (htβ : (t : ℝ) ≤ β * m) (hβ : 0 ≤ β) (hνs : 0 < νs)
    (hν : 0 ≤ ν) (hνm : ∀ i, (m : ℝ) ≤ ν * (A i).card)
    (hrange : ∀ i k, ∀ x ∈ A i, φ i k x ∈ Set.Icc (0 : ℝ) 1)
    (hratio : ∀ i, ((A i).card / m) * (2 * (q * ⌈1 / νs⌉₊)) * (2 * m - t) ^ (t / 8)
      < (2 * m) ^ (t / 8)) :
    ∃ (B : Finset (Finset α)) (X₀ : Finset α),
      A₀ ⊆ X₀ ∧
      (∀ b ∈ B, Disjoint b X₀) ∧
      (↑B : Set (Finset α)).PairwiseDisjoint id ∧
      X₀ ∪ B.biUnion id = X ∧
      ((X₀.card : ℝ) ≤ (A₀.card : ℝ) + ν * (X.card : ℝ)) ∧
      B.card * m ≤ X.card ∧
      ∀ b ∈ B, b.card = m ∧ ∃ i, b ⊆ A i ∧
        ∀ k, |averageOn b (φ i k) - averageOn (A i) (φ i k)|
          ≤ 2 * νs + (1 + νs) * β := by
  classical
  -- Pieces are nonempty: `1 ≤ m ≤ ν |Aᵢ|` forces `|Aᵢ| > 0`.
  have hAne : ∀ i, (A i).Nonempty := by
    intro i
    rw [← Finset.card_pos]
    by_contra hc
    push Not at hc
    have h0 : (A i).card = 0 := Nat.le_zero.mp hc
    have := hνm i
    rw [h0] at this
    simp only [Nat.cast_zero, mul_zero] at this
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    linarith
  have hAX : ∀ i, A i ⊆ X := by
    intro i a ha
    rw [← hcover]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩)
  -- Slice each piece.
  have hslice : ∀ i : Fin s, ∃ block : Fin ((A i).card / m) → Finset α,
      (∀ j, (block j).card = m) ∧
      (∀ j, block j ⊆ A i) ∧
      (∀ {j j'}, j ≠ j' → Disjoint (block j) (block j')) ∧
      ∀ k j, |averageOn (block j) (φ i k) - averageOn (A i) (φ i k)|
        ≤ 2 * νs + (1 + νs) * β :=
    fun i ↦ exists_average_slicing (A i) (φ i) (hAne i) hm0 ht htβ hβ hνs
      (hrange i) (hratio i)
  choose blk hblkcard hblksub hblkdisj hblkavg using hslice
  -- Per-piece nonemptiness of blocks, and injectivity of the block enumeration.
  have hblkne : ∀ i j, (blk i j).Nonempty := by
    intro i j
    rw [← Finset.card_pos, hblkcard i j]
    exact hm0
  -- Assemble the block family and the remainder.
  set B : Finset (Finset α) :=
    Finset.univ.biUnion
      (fun i : Fin s ↦ (Finset.univ : Finset (Fin ((A i).card / m))).image (blk i))
    with hB
  set X₀ : Finset α := X \ B.biUnion id with hX₀
  -- Membership unpacking: every member of `B` is a block of some piece.
  have hBmem : ∀ b ∈ B, ∃ i j, b = blk i j := by
    intro b hb
    rw [hB] at hb
    obtain ⟨i, -, hb'⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨j, -, hbj⟩ := Finset.mem_image.mp hb'
    exact ⟨i, j, hbj.symm⟩
  have hBmem' : ∀ i j, blk i j ∈ B := by
    intro i j
    rw [hB]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  -- Distinct blocks are disjoint (same piece: slicing; different pieces: piece disjointness).
  have hdisjB : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b' := by
    intro b hb b' hb' hne
    obtain ⟨i, j, rfl⟩ := hBmem b hb
    obtain ⟨i', j', rfl⟩ := hBmem b' hb'
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := fun h ↦ hne (congrArg (blk i) h)
      exact hblkdisj i hjj
    · exact Finset.disjoint_of_subset_left (hblksub i j)
        (Finset.disjoint_of_subset_right (hblksub i' j') (hdisj i i' hii))
  have hdisjB' : (↑B : Set (Finset α)).PairwiseDisjoint id := fun b hb b' hb' hne ↦
    hdisjB b (Finset.mem_coe.mp hb) b' (Finset.mem_coe.mp hb') hne
  -- The covered part sits inside `X`.
  have hBX : B.biUnion id ⊆ X := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨i, j, rfl⟩ := hBmem b hb
    exact hAX i (hblksub i j hab)
  have hcover' : X₀ ∪ B.biUnion id = X := by
    rw [hX₀]
    exact Finset.sdiff_union_of_subset hBX
  -- The exceptional set is untouched by the blocks.
  have hA₀X₀ : A₀ ⊆ X₀ := by
    intro a ha
    rw [hX₀, Finset.mem_sdiff]
    refine ⟨by rw [← hcover]; exact Finset.mem_union_left _ ha, ?_⟩
    intro hmem
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp hmem
    obtain ⟨i, j, rfl⟩ := hBmem b hb
    exact Finset.disjoint_left.mp (hdisj0 i) (hblksub i j hab) ha
  -- Remainder mass: the exceptional set plus one sub-`m` leftover per piece.
  have hcovered : ∀ i, ((Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card
      = ((A i).card / m) * m := by
    intro i
    rw [Finset.card_biUnion (fun j _ j' _ hjj ↦ hblkdisj i hjj)]
    rw [Finset.sum_congr rfl (fun j _ ↦ hblkcard i j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hX₀sub : X₀ ⊆ A₀ ∪ Finset.univ.biUnion
      (fun i : Fin s ↦ A i \ (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)) := by
    intro a ha
    rw [hX₀, Finset.mem_sdiff] at ha
    obtain ⟨haX, hanb⟩ := ha
    rw [← hcover] at haX
    rcases Finset.mem_union.mp haX with h0 | hpieces
    · exact Finset.mem_union_left _ h0
    · obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.mp hpieces
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
      rw [Finset.mem_sdiff]
      refine ⟨hai, ?_⟩
      intro hmem
      obtain ⟨j, -, haj⟩ := Finset.mem_biUnion.mp hmem
      exact hanb (Finset.mem_biUnion.mpr ⟨blk i j, hBmem' i j, haj⟩)
  have hX₀card : (X₀.card : ℝ) ≤ (A₀.card : ℝ) + ν * (X.card : ℝ) := by
    have h1 : X₀.card ≤ A₀.card + ∑ i : Fin s,
        (A i \ (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card := by
      calc X₀.card ≤ (A₀ ∪ Finset.univ.biUnion (fun i : Fin s ↦ A i \
              (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i))).card :=
            Finset.card_le_card hX₀sub
        _ ≤ A₀.card + (Finset.univ.biUnion (fun i : Fin s ↦ A i \
              (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i))).card :=
            Finset.card_union_le _ _
        _ ≤ A₀.card + ∑ i : Fin s, (A i \
              (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card := by
            exact Nat.add_le_add_left (Finset.card_biUnion_le) _
    -- Each per-piece leftover has size `|Aᵢ| % m < m ≤ ν |Aᵢ|`.
    have h2 : ∀ i : Fin s, ((A i \
        (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card : ℝ)
        ≤ ν * ((A i).card : ℝ) := by
      intro i
      have hsub : (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i) ⊆ A i := by
        intro a ha
        obtain ⟨j, -, haj⟩ := Finset.mem_biUnion.mp ha
        exact hblksub i j haj
      have hcard : (A i \ (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card
          = (A i).card - ((A i).card / m) * m := by
        rw [Finset.card_sdiff_of_subset hsub, hcovered i]
      have hmod : (A i).card - ((A i).card / m) * m ≤ m := by
        have h2' : m * ((A i).card / m) + (A i).card % m = (A i).card :=
          Nat.div_add_mod _ _
        have h3' : (A i).card % m < m := Nat.mod_lt _ hm0
        have h4' : ((A i).card / m) * m = m * ((A i).card / m) := Nat.mul_comm _ _
        omega
      calc ((A i \ (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card : ℝ)
          ≤ (m : ℝ) := by
            rw [hcard]
            exact_mod_cast hmod
        _ ≤ ν * ((A i).card : ℝ) := hνm i
    -- Piece masses sum to at most `|X|`.
    have h3 : ∑ i : Fin s, ((A i).card : ℝ) ≤ (X.card : ℝ) := by
      have hsum : (Finset.univ.biUnion A).card = ∑ i : Fin s, (A i).card :=
        Finset.card_biUnion (fun i _ i' _ hii ↦ hdisj i i' hii)
      have hsub : Finset.univ.biUnion A ⊆ X := by
        intro a ha
        obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.mp ha
        exact hAX i hai
      have := Finset.card_le_card hsub
      rw [hsum] at this
      exact_mod_cast this
    have h1R : (X₀.card : ℝ) ≤ (A₀.card : ℝ) + ∑ i : Fin s, ((A i \
        (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card : ℝ) := by
      exact_mod_cast h1
    calc (X₀.card : ℝ)
        ≤ (A₀.card : ℝ) + ∑ i : Fin s, ((A i \
            (Finset.univ : Finset (Fin ((A i).card / m))).biUnion (blk i)).card : ℝ) := h1R
      _ ≤ (A₀.card : ℝ) + ∑ i : Fin s, ν * ((A i).card : ℝ) :=
          add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ h2 i)
      _ = (A₀.card : ℝ) + ν * ∑ i : Fin s, ((A i).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (A₀.card : ℝ) + ν * (X.card : ℝ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hν)
  -- The mass form of the block count.
  have hcount : B.card * m ≤ X.card := by
    have h1 : (B.biUnion id).card = ∑ b ∈ B, b.card :=
      Finset.card_biUnion (fun b hb b' hb' hne ↦ hdisjB b hb b' hb' hne)
    have h2 : ∑ b ∈ B, b.card = B.card * m :=
      Finset.sum_const_nat fun b hb ↦ by
        obtain ⟨i, j, rfl⟩ := hBmem b hb
        exact hblkcard i j
    have h3 := Finset.card_le_card hBX
    omega
  refine ⟨B, X₀, hA₀X₀, ?_, hdisjB', hcover', hX₀card, hcount, ?_⟩
  · intro b hb
    rw [hX₀]
    exact Finset.disjoint_sdiff.mono_left (Finset.subset_biUnion_of_mem id hb)
  · intro b hb
    obtain ⟨i, j, rfl⟩ := hBmem b hb
    exact ⟨hblkcard i j, i, hblksub i j, fun k ↦ hblkavg i k j⟩

end RegularityLemmata
