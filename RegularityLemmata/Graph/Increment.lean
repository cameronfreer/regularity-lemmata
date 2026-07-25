/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Uniformity
import RegularityLemmata.Graph.Variance

/-!
# The one-block energy increment

If the ordered block `(A, B)` fails `ε`-uniformity, witnessed by the sub-rectangle
`(w.left, w.right)`, then refining `(A, B)` into the `2 × 2` rectangle partition
`{left, A \ left} × {right, B \ right}` raises the summed block energy by at least
`ε⁴ · |A| · |B|` (`blockEnergy_increment`). `blockEnergy_increment_refined` transports
the gain to any partition in which the block and both witness sides are part unions —
the per-pair bridge consumed by the global bad-mass increment.

Both come in an `ε`-free general form — `blockEnergy_increment_general` and
`blockEnergy_increment_refined_general` — in which the distinguished sub-rectangle is
ARBITRARY and the gain is AT LEAST its own mass-weighted squared deviation from the
parent density — an inequality, never an equality: the other three cells may contribute
further variance. The witness enters only through `NonuniformWitness.pow_four_mul_le`,
the single lemma that converts the witness's two defining inequalities into the raw `ε⁴`
gain. The general forms are what an approximate (equitabilised) refinement needs, since
there the recovered sides are not witnesses for any prescribed tolerance.

The algebra is isolated in `energy_increment_abstract`: four cells refining a parent,
with the distinguished (witness) cell's variance against the parent mean as the gain
(an `engel_defect_lower` + `titu_three` consequence).

This is the "energy boost for an irregular pair" (Y. Zhao, *Graph Theory and Additive
Combinatorics*, ch. 2). Machine-checked antecedents: mathlib's
`Mathlib.Combinatorics.SimpleGraph.Regularity.Increment` (symmetric, equipartition
setting) and the Isabelle AFP entry *Szemerédi's Regularity Lemma* by C. Edmonds,
A. Koutsoukou-Argyraki, and L. C. Paulson.
-/

namespace RegularityLemmata

variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {ε : ℝ}

/-- The abstract `2 × 2` energy increment: four cells with counts `cᵢⱼ` and masses
`mᵢⱼ` refining a parent with count `c` and mass `M`; the refined Engel sum exceeds the
parent's by at least the witness cell's weighted squared deviation. -/
theorem energy_increment_abstract {c11 c12 c21 c22 m11 m12 m21 m22 M c gain : ℝ}
    (hm11 : 0 < m11) (hm12 : 0 ≤ m12) (hm21 : 0 ≤ m21) (hm22 : 0 ≤ m22)
    (hz12 : m12 = 0 → c12 = 0) (hz21 : m21 = 0 → c21 = 0) (hz22 : m22 = 0 → c22 = 0)
    (hM : M = m11 + m12 + m21 + m22) (hc : c = c11 + c12 + c21 + c22)
    (hgain : gain ≤ m11 * (c11 / m11 - c / M) ^ 2) :
    c ^ 2 / M + gain ≤ c11 ^ 2 / m11 + c12 ^ 2 / m12 + c21 ^ 2 / m21 + c22 ^ 2 / m22 := by
  have hsum_nn : (0 : ℝ) ≤ m12 + m21 + m22 := by linarith
  rcases hsum_nn.lt_or_eq with hq | hq0
  · have h3 : (c12 + c21 + c22) ^ 2 / (m12 + m21 + m22)
        ≤ c12 ^ 2 / m12 + c21 ^ 2 / m21 + c22 ^ 2 / m22 :=
      titu_three hm12 hm21 hm22 hz12 hz21 hz22
    have hdefect := engel_defect_lower (a := c11) (b := c12 + c21 + c22) (p := m11)
      (q := m12 + m21 + m22) hm11 hq
    have hsum_c : c11 + (c12 + c21 + c22) = c := by rw [hc]; ring
    have hsum_m : m11 + (m12 + m21 + m22) = M := by rw [hM]; ring
    rw [hsum_c, hsum_m] at hdefect
    linarith [h3, hdefect, hgain]
  · have e12 : m12 = 0 := le_antisymm (by linarith) hm12
    have e21 : m21 = 0 := le_antisymm (by linarith) hm21
    have e22 : m22 = 0 := le_antisymm (by linarith) hm22
    have hc12 : c12 = 0 := hz12 e12
    have hc21 : c21 = 0 := hz21 e21
    have hc22 : c22 = 0 := hz22 e22
    have hMm : M = m11 := by rw [hM, e12, e21, e22]; ring
    have hcc : c = c11 := by rw [hc, hc12, hc21, hc22]; ring
    have hg0 : gain ≤ 0 := by rw [hcc, hMm] at hgain; simpa using hgain
    rw [hMm, hcc, e12, e21, e22, hc12, hc21, hc22]
    simp
    linarith [hg0]

/-- **The general one-block energy increment.** Refining `(A, B)` by ANY nondegenerate
sub-rectangle `(A', B')` gains AT LEAST that cell's mass-weighted squared deviation from
the parent density; the remaining three cells may contribute more, so this is an
inequality. No tolerance and no witness are involved: the two consumers below supply
their own lower bound for the gain. -/
theorem blockEnergy_increment_general [DecidableEq α] {A B A' B' : Finset α}
    (hA' : A' ⊆ A) (hB' : B' ⊆ B) (hpos : 0 < (A'.card : ℝ) * (B'.card : ℝ)) :
    blockEnergy R A B
        + (A'.card : ℝ) * (B'.card : ℝ) * (pairDensity R A' B' - pairDensity R A B) ^ 2
      ≤ blockEnergy R A' B' + blockEnergy R A' (B \ B')
        + blockEnergy R (A \ A') B' + blockEnergy R (A \ A') (B \ B') := by
  have hA'pos : 0 < (A'.card : ℝ) := by
    rcases (mul_pos_iff.mp hpos) with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (not_lt.mpr (Nat.cast_nonneg _))
  have hB'pos : 0 < (B'.card : ℝ) := by
    rcases (mul_pos_iff.mp hpos) with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h (not_lt.mpr (Nat.cast_nonneg _))
  have hAsplit : (A.card : ℝ) = (A'.card : ℝ) + ((A \ A').card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hA'
    rw [← h]; push_cast; ring
  have hBsplit : (B.card : ℝ) = (B'.card : ℝ) + ((B \ B').card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hB'
    rw [← h]; push_cast; ring
  rw [blockEnergy_eq_count_sq_div R A B, blockEnergy_eq_count_sq_div R A' B',
    blockEnergy_eq_count_sq_div R A' (B \ B'), blockEnergy_eq_count_sq_div R (A \ A') B',
    blockEnergy_eq_count_sq_div R (A \ A') (B \ B')]
  apply energy_increment_abstract
  · exact mul_pos hA'pos hB'pos
  · positivity
  · positivity
  · positivity
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (ne_of_gt hA'pos)
    · have hz : (B \ B').card = 0 := by exact_mod_cast h2
      simp [pairCount_of_right_card_eq_zero R A' hz]
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have hz : (A \ A').card = 0 := by exact_mod_cast h1
      simp [pairCount_of_left_card_eq_zero R B' hz]
    · exact absurd h2 (ne_of_gt hB'pos)
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have hz : (A \ A').card = 0 := by exact_mod_cast h1
      simp [pairCount_of_left_card_eq_zero R (B \ B') hz]
    · have hz : (B \ B').card = 0 := by exact_mod_cast h2
      simp [pairCount_of_right_card_eq_zero R (A \ A') hz]
  · rw [hAsplit, hBsplit]; ring
  · have hsplit := pairCount_split R A' B' hA' hB'
    rw [hsplit]; push_cast; ring
  · rw [(pairDensity_eq_count_div : pairDensity R A' B' = _),
      (pairDensity_eq_count_div : pairDensity R A B = _)]

/-- Both sides of a nonuniformity witness's ambient block are nonempty: an empty side
would force both densities to `0`, contradicting the strict deviation. -/
private theorem card_pos_of_witness {A B : Finset α} (w : NonuniformWitness R A B ε)
    (hε : 0 < ε) : 0 < (A.card : ℝ) ∧ 0 < (B.card : ℝ) := by
  obtain ⟨A', B', hA', hB', _, _, hdev⟩ := w
  constructor
  · rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · exfalso
      have hA'0 : A'.card = 0 := Nat.le_zero.mp (le_trans (Finset.card_le_card hA') h0.le)
      rw [pairDensity_of_left_card_eq_zero R B' hA'0,
        pairDensity_of_left_card_eq_zero R B h0] at hdev
      simp at hdev
      linarith
    · exact_mod_cast hpos
  · rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · exfalso
      have hB'0 : B'.card = 0 := Nat.le_zero.mp (le_trans (Finset.card_le_card hB') h0.le)
      rw [pairDensity_of_right_card_eq_zero R A' hB'0,
        pairDensity_of_right_card_eq_zero R A h0] at hdev
      simp at hdev
      linarith
    · exact_mod_cast hpos

/-- The witness rectangle is nondegenerate. -/
theorem NonuniformWitness.card_mul_pos {A B : Finset α} (w : NonuniformWitness R A B ε)
    (hε : 0 < ε) : 0 < (w.left.card : ℝ) * (w.right.card : ℝ) := by
  obtain ⟨hApos, hBpos⟩ := card_pos_of_witness w hε
  exact mul_pos (lt_of_lt_of_le (mul_pos hε hApos) w.left_card)
    (lt_of_lt_of_le (mul_pos hε hBpos) w.right_card)

/-- **The witness gain bound**: a nonuniformity witness's mass-weighted squared deviation
dominates the raw `ε⁴ · |A| · |B|`. This is the ONLY place the witness's two defining
inequalities are consumed; everything else about the increment is `ε`-free. -/
theorem NonuniformWitness.pow_four_mul_le {A B : Finset α} (w : NonuniformWitness R A B ε)
    (hε : 0 < ε) :
    ε ^ 4 * (A.card : ℝ) * (B.card : ℝ)
      ≤ (w.left.card : ℝ) * (w.right.card : ℝ)
        * (pairDensity R w.left w.right - pairDensity R A B) ^ 2 := by
  obtain ⟨hApos, hBpos⟩ := card_pos_of_witness w hε
  have hA'pos : 0 < (w.left.card : ℝ) := lt_of_lt_of_le (mul_pos hε hApos) w.left_card
  have hDsq : ε ^ 2 < (pairDensity R w.left w.right - pairDensity R A B) ^ 2 := by
    nlinarith [sq_abs (pairDensity R w.left w.right - pairDensity R A B), w.dev, hε,
      abs_nonneg (pairDensity R w.left w.right - pairDensity R A B)]
  have hmass : ε ^ 2 * ((A.card : ℝ) * (B.card : ℝ))
      ≤ (w.left.card : ℝ) * (w.right.card : ℝ) := by
    have h1 : (ε * (A.card : ℝ)) * (ε * (B.card : ℝ))
        ≤ (w.left.card : ℝ) * (w.right.card : ℝ) :=
      mul_le_mul w.left_card w.right_card (mul_nonneg hε.le (Nat.cast_nonneg _))
        (le_of_lt hA'pos)
    nlinarith [h1]
  have hstep : ε ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) * ε ^ 2
      ≤ ((w.left.card : ℝ) * (w.right.card : ℝ))
        * (pairDensity R w.left w.right - pairDensity R A B) ^ 2 :=
    mul_le_mul hmass hDsq.le (sq_nonneg ε) (by positivity)
  calc ε ^ 4 * (A.card : ℝ) * (B.card : ℝ)
      = ε ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) * ε ^ 2 := by ring
    _ ≤ _ := hstep

/-- **The one-block energy increment.** A nonuniformity witness turns into an
`ε⁴ · |A| · |B|` energy gain across the `2 × 2` witness refinement. -/
theorem blockEnergy_increment [DecidableEq α] {A B : Finset α}
    (w : NonuniformWitness R A B ε) (hε : 0 < ε) :
    blockEnergy R A B + ε ^ 4 * (A.card : ℝ) * (B.card : ℝ)
      ≤ blockEnergy R w.left w.right + blockEnergy R w.left (B \ w.right)
        + blockEnergy R (A \ w.left) w.right + blockEnergy R (A \ w.left) (B \ w.right) := by
  refine le_trans ?_
    (blockEnergy_increment_general w.left_subset w.right_subset (w.card_mul_pos hε))
  have := w.pow_four_mul_le hε
  linarith

/-- **The general per-pair bridge**: any nondegenerate sub-rectangle whose sides — and
whose ambient block — are part unions of `P'` transports at least its own weighted
squared deviation to the summed energies of the refined sub-blocks. The `ε`-free form: the
consumer chooses the sub-rectangle and supplies the gain bound. -/
theorem blockEnergy_increment_refined_general [DecidableEq α] {s : Finset α}
    {P' : Finpartition s} (R : α → α → Prop) [DecidableRel R] {C D A' B' : Finset α}
    (hA' : A' ⊆ C) (hB' : B' ⊆ D) (hpos : 0 < (A'.card : ℝ) * (B'.card : ℝ))
    (hCU : IsPartUnion P' C) (hDU : IsPartUnion P' D)
    (hlU : IsPartUnion P' A') (hrU : IsPartUnion P' B') :
    blockEnergy R C D
        + (A'.card : ℝ) * (B'.card : ℝ) * (pairDensity R A' B' - pairDensity R C D) ^ 2 ≤
      ∑ C' ∈ P'.parts.filter (· ⊆ C), ∑ D' ∈ P'.parts.filter (· ⊆ D),
        blockEnergy R C' D' := by
  have hpd : ∀ S : Finset α,
      (↑(P'.parts.filter (· ⊆ S)) : Set (Finset α)).PairwiseDisjoint id := fun S =>
    P'.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  have hC2U : IsPartUnion P' (C \ A') := isPartUnion_sdiff hCU hlU hA'
  have hD2U : IsPartUnion P' (D \ B') := isPartUnion_sdiff hDU hrU hB'
  have hb11 := blockEnergy_superadditive R (P'.parts.filter (· ⊆ A'))
    (P'.parts.filter (· ⊆ B')) (hpd _) hlU (hpd _) hrU
  have hb12 := blockEnergy_superadditive R (P'.parts.filter (· ⊆ A'))
    (P'.parts.filter (· ⊆ D \ B')) (hpd _) hlU (hpd _) hD2U
  have hb21 := blockEnergy_superadditive R (P'.parts.filter (· ⊆ C \ A'))
    (P'.parts.filter (· ⊆ B')) (hpd _) hC2U (hpd _) hrU
  have hb22 := blockEnergy_superadditive R (P'.parts.filter (· ⊆ C \ A'))
    (P'.parts.filter (· ⊆ D \ B')) (hpd _) hC2U (hpd _) hD2U
  have hdecomp : ∑ C' ∈ P'.parts.filter (· ⊆ C), ∑ D' ∈ P'.parts.filter (· ⊆ D),
        blockEnergy R C' D'
      = (∑ C' ∈ P'.parts.filter (· ⊆ A'), ∑ D' ∈ P'.parts.filter (· ⊆ B'),
          blockEnergy R C' D')
        + (∑ C' ∈ P'.parts.filter (· ⊆ A'),
            ∑ D' ∈ P'.parts.filter (· ⊆ D \ B'), blockEnergy R C' D')
        + (∑ C' ∈ P'.parts.filter (· ⊆ C \ A'),
            ∑ D' ∈ P'.parts.filter (· ⊆ B'), blockEnergy R C' D')
        + (∑ C' ∈ P'.parts.filter (· ⊆ C \ A'),
            ∑ D' ∈ P'.parts.filter (· ⊆ D \ B'), blockEnergy R C' D') := by
    rw [filter_subset_eq_union hlU hA', filter_subset_eq_union hrU hB']
    simp only [Finset.sum_union filter_subset_disjoint, Finset.sum_add_distrib]
    ring
  rw [hdecomp]
  calc blockEnergy R C D
        + (A'.card : ℝ) * (B'.card : ℝ) * (pairDensity R A' B' - pairDensity R C D) ^ 2
      ≤ blockEnergy R A' B' + blockEnergy R A' (D \ B')
        + blockEnergy R (C \ A') B' + blockEnergy R (C \ A') (D \ B') :=
        blockEnergy_increment_general hA' hB' hpos
    _ ≤ _ := add_le_add (add_le_add (add_le_add hb11 hb12) hb21) hb22

/-- The per-pair bridge: a witness whose block and sides are part unions of `P'`
transports the `ε⁴` gain to the summed energies of the refined sub-blocks. -/
theorem blockEnergy_increment_refined [DecidableEq α] {s : Finset α}
    {P' : Finpartition s} (R : α → α → Prop) [DecidableRel R] {C D : Finset α} {ε : ℝ}
    (hε : 0 < ε) (w : NonuniformWitness R C D ε)
    (hCU : IsPartUnion P' C) (hDU : IsPartUnion P' D)
    (hlU : IsPartUnion P' w.left) (hrU : IsPartUnion P' w.right) :
    blockEnergy R C D + ε ^ 4 * (C.card : ℝ) * (D.card : ℝ) ≤
      ∑ C' ∈ P'.parts.filter (· ⊆ C), ∑ D' ∈ P'.parts.filter (· ⊆ D),
        blockEnergy R C' D' := by
  refine le_trans ?_ (blockEnergy_increment_refined_general R w.left_subset w.right_subset
    (w.card_mul_pos hε) hCU hDU hlU hrU)
  have := w.pow_four_mul_le hε
  linarith

/-! ### Tests and adversarial examples -/

-- The abstract increment instantiated with concrete numbers: parent count 2, mass 4,
-- witness cell (1,1) with count 1, mass 1; gain 1·(1 - 1/2)² = 1/4.
example :
    (2 : ℝ) ^ 2 / 4 + 1 / 4 ≤ 1 ^ 2 / 1 + 1 ^ 2 / 1 + 0 ^ 2 / 1 + 0 ^ 2 / 1 := by
  have := energy_increment_abstract (c11 := 1) (c12 := 1) (c21 := 0) (c22 := 0)
    (m11 := 1) (m12 := 1) (m21 := 1) (m22 := 1) (M := 4) (c := 2) (gain := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

end RegularityLemmata
