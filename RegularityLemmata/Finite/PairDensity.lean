/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Density

/-!
# Pair counts and pair density

`pairCount R A B` counts the pairs of `A ×ˢ B` related by `R`; `pairDensity` is the
corresponding density (zero when a side is empty, by the division convention). The
additivity lemma `pairCount_biUnion` over two-dimensional disjoint covers is the
counting backbone of block-energy superadditivity.
-/

namespace RegularityLemmata

variable {α : Type*}
variable {R : α → α → Prop} [DecidableRel R] {A B : Finset α}

/-- Number of `R`-related pairs in `A ×ˢ B`. -/
def pairCount (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℕ :=
  ((A ×ˢ B).filter fun p => R p.1 p.2).card

/-- Density of `R` on `A ×ˢ B`; `0` if a side is empty. -/
noncomputable def pairDensity (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℝ :=
  densityOn (A ×ˢ B) fun p => R p.1 p.2

/-- Guard-free division form: agrees with `densityOn` since `x / 0 = 0`. -/
theorem pairDensity_eq_count_div :
    pairDensity R A B = (pairCount R A B : ℝ) / (((A.card) : ℝ) * B.card) := by
  rw [pairDensity, densityOn, pairCount, Finset.card_product, Nat.cast_mul]

theorem pairDensity_nonneg : 0 ≤ pairDensity R A B := densityOn_nonneg

theorem pairDensity_le_one : pairDensity R A B ≤ 1 := densityOn_le_one

/-- Raw count from the density: `#pairs = d·|A||B|`, unconditionally (an empty side
gives `0 = d · 0`). -/
theorem pairCount_eq_pairDensity_mul :
    (pairCount R A B : ℝ) = pairDensity R A B * (((A.card) : ℝ) * B.card) := by
  rcases eq_or_ne (((A.card) : ℝ) * B.card) 0 with hm | hm
  · rw [hm, mul_zero]
    rcases mul_eq_zero.mp hm with h | h
    · rw [pairCount, Finset.card_eq_zero.mp (by exact_mod_cast h : A.card = 0)]
      simp
    · rw [pairCount, Finset.card_eq_zero.mp (by exact_mod_cast h : B.card = 0)]
      simp
  · rw [pairDensity_eq_count_div, div_mul_cancel₀]
    exact hm

/-- Sum of part cardinalities over a disjoint cover of `C` equals `|C|` (real cast). -/
theorem sum_card_biUnion_cast [DecidableEq α] {C : Finset α} (sC : Finset (Finset α))
    (hdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hcover : sC.biUnion id = C) :
    (∑ C' ∈ sC, (C'.card : ℝ)) = (C.card : ℝ) := by
  have h : (sC.biUnion id).card = ∑ C' ∈ sC, (id C').card :=
    Finset.card_biUnion fun x hx y hy hne => hdisj hx hy hne
  rw [hcover] at h
  simp only [id_eq] at h
  rw [h, Nat.cast_sum]

/-- The pair count is additive over a two-dimensional disjoint cover:
`C = ⊔ sC`, `D = ⊔ sD`. -/
theorem pairCount_biUnion [DecidableEq α] (R : α → α → Prop) [DecidableRel R] {C D : Finset α}
    (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    pairCount R C D = ∑ p ∈ sC ×ˢ sD, pairCount R p.1 p.2 := by
  have hset : (C ×ˢ D).filter (fun q => R q.1 q.2)
      = (sC ×ˢ sD).biUnion (fun p => (p.1 ×ˢ p.2).filter (fun q => R q.1 q.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Prod.exists]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hR⟩
      rw [← hCcover, Finset.mem_biUnion] at hq1
      rw [← hDcover, Finset.mem_biUnion] at hq2
      obtain ⟨C', hC', hq1'⟩ := hq1
      obtain ⟨D', hD', hq2'⟩ := hq2
      simp only [id_eq] at hq1' hq2'
      exact ⟨C', D', ⟨hC', hD'⟩, ⟨hq1', hq2'⟩, hR⟩
    · rintro ⟨C', D', ⟨hC', hD'⟩, ⟨hq1, hq2⟩, hR⟩
      refine ⟨⟨?_, ?_⟩, hR⟩
      · rw [← hCcover, Finset.mem_biUnion]; exact ⟨C', hC', by simpa using hq1⟩
      · rw [← hDcover, Finset.mem_biUnion]; exact ⟨D', hD', by simpa using hq2⟩
  have hdisj : ∀ p ∈ sC ×ˢ sD, ∀ p' ∈ sC ×ˢ sD, p ≠ p' →
      Disjoint ((p.1 ×ˢ p.2).filter (fun q => R q.1 q.2))
        ((p'.1 ×ˢ p'.2).filter (fun q => R q.1 q.2)) := by
    intro p hp p' hp' hne
    rw [Finset.mem_product] at hp hp'
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    rw [Finset.mem_filter, Finset.mem_product] at hxy hxy'
    by_cases hC : p.1 = p'.1
    · have hD : p.2 ≠ p'.2 := fun h => hne (Prod.ext hC h)
      exact (Finset.disjoint_left.mp (hDdisj hp.2 hp'.2 hD)) hxy.1.2 hxy'.1.2
    · exact (Finset.disjoint_left.mp (hCdisj hp.1 hp'.1 hC)) hxy.1.1 hxy'.1.1
  unfold pairCount
  rw [hset, Finset.card_biUnion hdisj]

/-! ### Sub-rectangle perturbation

Shrinking a rectangle discards at most the mass of the discarded strips. These are the
primitives behind approximating a set by the parts of a partition contained in it. -/

section Perturbation

variable [DecidableEq α] {A' B' : Finset α}

omit [DecidableEq α] in
/-- The pair count is monotone in both sides. -/
theorem pairCount_mono (hA : A' ⊆ A) (hB : B' ⊆ B) :
    pairCount R A' B' ≤ pairCount R A B :=
  Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.product_subset_product hA hB))

/-- Shrinking a rectangle loses at most the two discarded strips' worth of pairs. No
containment hypothesis is needed: every related pair of `A ×ˢ B` outside `A' ×ˢ B'` has
its left coordinate in `A \ A'` or its right coordinate in `B \ B'`. -/
theorem pairCount_le_add :
    pairCount R A B
      ≤ pairCount R A' B' + (A \ A').card * B.card + A.card * (B \ B').card := by
  have hsub : (A ×ˢ B).filter (fun p => R p.1 p.2)
      ⊆ ((A' ×ˢ B').filter (fun p => R p.1 p.2) ∪ (A \ A') ×ˢ B) ∪ A ×ˢ (B \ B') := by
    rintro ⟨x, y⟩ hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨⟨hx, hy⟩, hR⟩ := hxy
    by_cases hxA' : x ∈ A'
    · by_cases hyB' : y ∈ B'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxA', hyB'⟩, hR⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨hy, hyB'⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, hxA'⟩, hy⟩))
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  refine Nat.add_le_add ?_ (le_of_eq (Finset.card_product _ _))
  exact le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_left (le_of_eq (Finset.card_product _ _)) _)

/-- **Multiplication-form density comparison.** Shrinking a rectangle to `A' ⊆ A`,
`B' ⊆ B` moves the pair density by at most the discarded mass — stated multiplied through
by the shrunken mass, so that no denominator positivity is needed (both sides are `0`
when the shrunken rectangle is degenerate). -/
theorem abs_pairDensity_sub_mul_le (hA : A' ⊆ A) (hB : B' ⊆ B) :
    |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
      ≤ ((A \ A').card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B \ B').card : ℝ) := by
  have hcA : ((A \ A').card : ℝ) = (A.card : ℝ) - (A'.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hA, Nat.cast_sub (Finset.card_le_card hA)]
  have hcB : ((B \ B').card : ℝ) = (B.card : ℝ) - (B'.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hB, Nat.cast_sub (Finset.card_le_card hB)]
  have haa : (A'.card : ℝ) ≤ (A.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hA)
  have hbb : (B'.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hB)
  have ha0 : (0 : ℝ) ≤ (A'.card : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ (B'.card : ℝ) := Nat.cast_nonneg _
  have hgap : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) - (A'.card : ℝ) * (B'.card : ℝ) := by
    nlinarith
  have hstrip : (A.card : ℝ) * (B.card : ℝ) - (A'.card : ℝ) * (B'.card : ℝ)
      ≤ ((A.card : ℝ) - (A'.card : ℝ)) * (B.card : ℝ)
        + (A.card : ℝ) * ((B.card : ℝ) - (B'.card : ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haa) (sub_nonneg.mpr hbb)]
  rcases eq_or_lt_of_le (mul_nonneg ha0 hb0) with hm | hm
  · rw [← hm, mul_zero, hcA, hcB]
    linarith
  · have hmne : ((A'.card : ℝ) * (B'.card : ℝ)) ≠ 0 := ne_of_gt hm
    have habs : |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
        = |(pairDensity R A' B' - pairDensity R A B) * ((A'.card : ℝ) * (B'.card : ℝ))| := by
      rw [abs_mul, abs_of_pos hm]
    have hprod : (pairDensity R A' B' - pairDensity R A B) * ((A'.card : ℝ) * (B'.card : ℝ))
        = (pairCount R A' B' : ℝ)
          - pairDensity R A B * ((A'.card : ℝ) * (B'.card : ℝ)) := by
      rw [sub_mul, pairDensity_eq_count_div, div_mul_cancel₀ _ hmne]
    rw [habs, hprod, abs_sub_le_iff]
    have hd0 : 0 ≤ pairDensity R A B := pairDensity_nonneg
    have hd1 : pairDensity R A B ≤ 1 := pairDensity_le_one
    have hNle : (pairCount R A' B' : ℝ) ≤ (pairCount R A B : ℝ) :=
      Nat.cast_le.mpr (pairCount_mono hA hB)
    have hN : (pairCount R A B : ℝ) = pairDensity R A B * ((A.card : ℝ) * (B.card : ℝ)) :=
      pairCount_eq_pairDensity_mul
    have hadd : (pairCount R A B : ℝ)
        ≤ (pairCount R A' B' : ℝ) + ((A \ A').card : ℝ) * (B.card : ℝ)
          + (A.card : ℝ) * ((B \ B').card : ℝ) := by
      have := pairCount_le_add (R := R) (A := A) (B := B) (A' := A') (B' := B')
      exact_mod_cast this
    -- The shrunken mass is dominated by the full mass, weighted by the density.
    have hmass : pairDensity R A B * ((A'.card : ℝ) * (B'.card : ℝ))
        ≤ pairDensity R A B * ((A.card : ℝ) * (B.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hd0
    -- The density-weighted gap is at most the raw gap, hence at most the strips.
    have hweighted : pairDensity R A B
          * ((A.card : ℝ) * (B.card : ℝ) - (A'.card : ℝ) * (B'.card : ℝ))
        ≤ ((A.card : ℝ) - (A'.card : ℝ)) * (B.card : ℝ)
          + (A.card : ℝ) * ((B.card : ℝ) - (B'.card : ℝ)) := by
      nlinarith
    rw [hcA, hcB] at hadd ⊢
    constructor
    · nlinarith
    · linarith

end Perturbation

/-! ### Tests and adversarial examples -/

-- The strict-order relation on `Fin 3` relates 3 of the 9 pairs.
example : pairCount (fun a b : Fin 3 => a < b) Finset.univ Finset.univ = 3 := by decide

-- Empty sides give zero density (division convention).
example : pairDensity (fun _ _ : Fin 3 => True) ∅ Finset.univ = 0 := by
  rw [pairDensity_eq_count_div]
  simp

-- Additivity over the split {0} ∪ {1,2} of the C side (a concrete 2+1 cover).
example :
    pairCount (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
      = ∑ p ∈ ({({0} : Finset (Fin 3)), {1, 2}} : Finset (Finset (Fin 3)))
          ×ˢ ({Finset.univ} : Finset (Finset (Fin 3))), pairCount (· < ·) p.1 p.2 := by
  decide

end RegularityLemmata
