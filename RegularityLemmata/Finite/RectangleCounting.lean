/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Average

/-!
# Rectangle counting for exceptional sets

Double-counting identities between the cardinality of an exceptional set
`E : Finset (X × Y)` on a rectangle, its fiber counts, and the iterated `averageOn` of its
indicator — the bookkeeping that prices exceptional-set trace functions
`α(x) = 𝔼_B 1_E(x, ·)` through the slicing machinery. All identities are guard-free (an
empty side makes both sides `0`).
-/

namespace RegularityLemmata

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- Fiber count over the right side: the rectangle trace of `E` counted by columns. -/
theorem card_product_inter_eq_sum_right (E : Finset (X × Y)) (U : Finset X) (V : Finset Y) :
    ((U ×ˢ V) ∩ E).card = ∑ y ∈ V, (U.filter fun x ↦ (x, y) ∈ E).card := by
  rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_product_right]
  exact Finset.sum_congr rfl fun y _ ↦ (Finset.card_filter _ _).symm

/-- Fiber count over the left side: the rectangle trace of `E` counted by rows. -/
theorem card_product_inter_eq_sum_left (E : Finset (X × Y)) (U : Finset X) (V : Finset Y) :
    ((U ×ˢ V) ∩ E).card = ∑ x ∈ U, (V.filter fun y ↦ (x, y) ∈ E).card := by
  rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ ↦ (Finset.card_filter _ _).symm

omit [DecidableEq X] [DecidableEq Y] in
/-- **Fubini for iterated finite averages**, guard-free. -/
theorem averageOn_averageOn_comm (g : X → Y → ℝ) (U : Finset X) (V : Finset Y) :
    averageOn U (fun x ↦ averageOn V (g x)) = averageOn V (fun y ↦ averageOn U (g · y)) := by
  rw [← rectAverageCount_eq_averageOn_left g U V, rectAverageCount_eq_averageOn_right]

/-- The mass form of the iterated indicator average: it prices exactly the rectangle trace
of the exceptional set. Guard-free. -/
theorem averageOn_averageOn_indicator_mul (E : Finset (X × Y)) (U : Finset X)
    (V : Finset Y) :
    averageOn U (fun x ↦ averageOn V fun y ↦ if (x, y) ∈ E then (1 : ℝ) else 0)
      * ((U.card : ℝ) * (V.card : ℝ)) = (((U ×ˢ V) ∩ E).card : ℝ) := by
  rw [← mul_assoc, averageOn_mul_card, Finset.sum_mul]
  have hinner : ∀ x, averageOn V (fun y ↦ if (x, y) ∈ E then (1 : ℝ) else 0) * (V.card : ℝ)
      = ((V.filter fun y ↦ (x, y) ∈ E).card : ℝ) := by
    intro x
    rw [averageOn_mul_card, Finset.sum_boole]
  rw [Finset.sum_congr rfl fun x _ ↦ hinner x]
  rw [card_product_inter_eq_sum_left E U V]
  push_cast
  rfl

/-- The iterated indicator average of an exceptional set within the rectangle is below the
tolerance that bounds its mass. -/
theorem averageOn_averageOn_indicator_lt {E : Finset (X × Y)} {A : Finset X} {B : Finset Y}
    {ε : ℝ} (hE : E ⊆ A ×ˢ B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hmass : (E.card : ℝ) < ε * A.card * B.card) :
    averageOn A (fun x ↦ averageOn B fun y ↦ if (x, y) ∈ E then (1 : ℝ) else 0) < ε := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  have hkey := averageOn_averageOn_indicator_mul E A B
  rw [Finset.inter_eq_right.mpr hE] at hkey
  have hpos : (0 : ℝ) < (A.card : ℝ) * (B.card : ℝ) := by positivity
  rw [← mul_lt_mul_iff_of_pos_right hpos, hkey]
  nlinarith

end RegularityLemmata
