/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Density

/-!
# Section disagreement and inclusive mixedness

The resampling defect of a Boolean section. For a finite set `A` and a predicate `p` on it,
`sectionDisagreement A p` is the number of **ordered** pairs `(a, a') ∈ A × A` on which `p`
differs. Writing `m` for the number of points of `A` satisfying `p`, it equals `2·m·(|A| − m)`,
so its value normalized by `|A|²` is `2·d·(1 − d)` with `d = densityOn A p` the section's
density; both are `0` on the empty set, and no nonemptiness is assumed anywhere.

**Inclusive mixedness.** A density `d` is `θ`-mixed *inclusively* when `θ ≤ d ≤ 1 − θ`; this
differs from the strict version at the two boundary points `d = θ` and `d = 1 − θ`, which count
as mixed here. A section that is not inclusively mixed has normalized disagreement at most
`2·θ`; any section has normalized disagreement at most `1/2`. Hence, for a family of sections
indexed by a finite parameter set `Y` in which at most `γ·|Y|` parameters are inclusively
mixed, the total normalized disagreement is at most `(2·θ + γ/2)·|Y|`, with `0 ≤ θ` the only sign
hypothesis (`sum_normalizedDisagreement_le`; a negative `γ` is not excluded, it only makes the
counting hypothesis stronger). Stated with the sum rather
than the average, so it is guard-free for `Y = ∅`.

Nothing here refers to a partition or to a relation of higher arity; the coordinate-wise
hybrid argument that consumes these sections is `Finite/ProductHybrid.lean`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-- The number of ordered pairs `(a, a') ∈ A × A` on which the Boolean section `p` differs. -/
def sectionDisagreement (A : Finset α) (p : α → Prop) [DecidablePred p] : ℕ :=
  ((A ×ˢ A).filter fun q => ¬ (p q.1 ↔ p q.2)).card

section Count

variable (A : Finset α) (p : α → Prop) [DecidablePred p]

/-- The disagreeing pairs are the two rectangles `{p} × {¬p}` and `{¬p} × {p}`. -/
theorem sectionDisagreement_eq :
    sectionDisagreement A p = 2 * (A.filter p).card * (A.filter fun a => ¬ p a).card := by
  classical
  unfold sectionDisagreement
  have hsplit : (A ×ˢ A).filter (fun q => ¬ (p q.1 ↔ p q.2))
      = (A.filter p) ×ˢ (A.filter fun a => ¬ p a)
        ∪ (A.filter fun a => ¬ p a) ×ˢ (A.filter p) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      by_cases hpa : p a
      · have hpb : ¬ p b := fun hpb => h ⟨fun _ => hpb, fun _ => hpa⟩
        exact Or.inl ⟨⟨ha, hpa⟩, hb, hpb⟩
      · have hpb : p b := by
          by_contra hpb
          exact h ⟨fun hpa' => absurd hpa' hpa, fun hpb' => absurd hpb' hpb⟩
        exact Or.inr ⟨⟨ha, hpa⟩, hb, hpb⟩
    · rintro (⟨⟨ha, hpa⟩, hb, hpb⟩ | ⟨⟨ha, hpa⟩, hb, hpb⟩)
      · exact ⟨⟨ha, hb⟩, fun h => hpb (h.mp hpa)⟩
      · exact ⟨⟨ha, hb⟩, fun h => hpa (h.mpr hpb)⟩
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product]
  · ring
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_filter] at h₁ h₂
    exact h₂.1.2 h₁.1.2

omit [DecidableEq α] in
@[simp] theorem sectionDisagreement_empty : sectionDisagreement (∅ : Finset α) p = 0 := by
  simp [sectionDisagreement]

omit [DecidableEq α] in
/-- The disagreement counted row by row: for each `b ∈ A`, the points of `A` on which `p` differs
from its value at `b`. -/
theorem sectionDisagreement_eq_sum :
    sectionDisagreement A p = ∑ b ∈ A, (A.filter fun a => ¬ (p b ↔ p a)).card := by
  unfold sectionDisagreement
  rw [Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

omit [DecidableEq α] in
theorem sectionDisagreement_le_sq : sectionDisagreement A p ≤ A.card ^ 2 := by
  unfold sectionDisagreement
  calc ((A ×ˢ A).filter fun q => ¬ (p q.1 ↔ p q.2)).card ≤ (A ×ˢ A).card :=
        Finset.card_filter_le _ _
    _ = A.card ^ 2 := by rw [Finset.card_product, sq]

/-- Normalized by `|A|²`, the disagreement is `2·d·(1 − d)` for the density `d` of the section;
guard-free at `A = ∅` (both sides `0`). -/
theorem sectionDisagreement_div_sq :
    (sectionDisagreement A p : ℝ) / (A.card : ℝ) ^ 2
      = 2 * densityOn A p * (1 - densityOn A p) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [densityOn]
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [sectionDisagreement_eq]
  have hnot : ((A.filter fun a => ¬ p a).card : ℝ) = A.card - (A.filter p).card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (p := p)
    have h := congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at h
    linarith
  unfold densityOn
  push_cast
  rw [hnot]
  field_simp

/-- The normalized disagreement never exceeds `1/2`. -/
theorem two_mul_mul_one_sub_le_half {d : ℝ} : 2 * d * (1 - d) ≤ 1 / 2 := by
  nlinarith [sq_nonneg (2 * d - 1)]

end Count

/-! ### Inclusive mixedness -/

/-- A density `d` is inclusively `θ`-mixed when `θ ≤ d ≤ 1 − θ`; the boundary points count as
mixed, unlike the strict version. -/
def InclusiveMixed (θ d : ℝ) : Prop := θ ≤ d ∧ d ≤ 1 - θ

noncomputable instance (θ d : ℝ) : Decidable (InclusiveMixed θ d) := by
  unfold InclusiveMixed; infer_instance

/-- A density in `[0, 1]` that is not inclusively `θ`-mixed has `2·d·(1 − d) ≤ 2·θ`. -/
theorem two_mul_mul_one_sub_le_of_not_inclusiveMixed {θ d : ℝ} (hθ : 0 ≤ θ) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (h : ¬ InclusiveMixed θ d) : 2 * d * (1 - d) ≤ 2 * θ := by
  unfold InclusiveMixed at h
  push Not at h
  by_cases hlt : d < θ
  · nlinarith
  · have := h (not_lt.mp hlt)
    nlinarith

/-- **The inclusive-decency bound.** For sections `p y` on `A` indexed by `y ∈ Y`, if at most
`γ·|Y|` of them are inclusively `θ`-mixed, the total normalized disagreement is at most
`(2·θ + γ/2)·|Y|`. Only `0 ≤ θ` is assumed (the rate `γ` enters through the counting
hypothesis alone); `Y = ∅` and `A = ∅` are covered. -/
theorem sum_normalizedDisagreement_le {ι : Type*} (Y : Finset ι) (A : Finset α)
    (p : ι → α → Prop) [∀ y, DecidablePred (p y)] {θ γ : ℝ} (hθ : 0 ≤ θ)
    (hmixed : ((Y.filter fun y => InclusiveMixed θ (densityOn A (p y))).card : ℝ)
      ≤ γ * Y.card) :
    ∑ y ∈ Y, (sectionDisagreement A (p y) : ℝ) / (A.card : ℝ) ^ 2
      ≤ (2 * θ + γ / 2) * Y.card := by
  classical
  have hpt : ∀ y ∈ Y, (sectionDisagreement A (p y) : ℝ) / (A.card : ℝ) ^ 2
      ≤ 2 * θ + (if InclusiveMixed θ (densityOn A (p y)) then (1 / 2 : ℝ) else 0) := by
    intro y _
    rw [sectionDisagreement_div_sq]
    split_ifs with hm
    · linarith [two_mul_mul_one_sub_le_half (d := densityOn A (p y))]
    · have := two_mul_mul_one_sub_le_of_not_inclusiveMixed hθ densityOn_nonneg densityOn_le_one hm
      linarith
  calc ∑ y ∈ Y, (sectionDisagreement A (p y) : ℝ) / (A.card : ℝ) ^ 2
      ≤ ∑ y ∈ Y, (2 * θ + (if InclusiveMixed θ (densityOn A (p y)) then (1 / 2 : ℝ) else 0)) :=
        Finset.sum_le_sum hpt
    _ = 2 * θ * Y.card
        + (1 / 2) * ((Y.filter fun y => InclusiveMixed θ (densityOn A (p y))).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite,
          Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * θ * Y.card + (1 / 2) * (γ * Y.card) := by
        have := mul_le_mul_of_nonneg_left hmixed (by norm_num : (0:ℝ) ≤ 1 / 2)
        linarith
    _ = (2 * θ + γ / 2) * Y.card := by ring

/-! ### Tests and adversarial examples -/

section Tests

-- On `{0, 1, 2}` with `p = (· = 0)`: one point in, two out, so `2·1·2 = 4` disagreeing pairs.
example : sectionDisagreement ({0, 1, 2} : Finset (Fin 3)) (fun a => a = 0) = 4 := by decide

-- A constant section disagrees nowhere; the empty set disagrees nowhere.
example : sectionDisagreement ({0, 1, 2} : Finset (Fin 3)) (fun _ => True) = 0 := by decide
example : sectionDisagreement (∅ : Finset (Fin 3)) (fun a => a = 0) = 0 := by decide

-- The normalized value at density `1/3` is `2·(1/3)·(2/3) = 4/9`.
example : (sectionDisagreement ({0, 1, 2} : Finset (Fin 3)) (fun a => a = 0) : ℝ)
    / ((3 : ℕ) : ℝ) ^ 2 = 4 / 9 := by
  have : sectionDisagreement ({0, 1, 2} : Finset (Fin 3)) (fun a => a = 0) = 4 := by decide
  rw [this]; norm_num

-- **Inclusive versus strict**: the boundary density `θ` itself is inclusively mixed.
example : InclusiveMixed (1 / 3 : ℝ) (1 / 3) := ⟨le_rfl, by norm_num⟩
-- Below the threshold it is not, and the bound `2·d·(1−d) ≤ 2·θ` applies.
example : ¬ InclusiveMixed (1 / 3 : ℝ) (1 / 4) := fun h => by
  have := h.1; norm_num at this

-- **Decency with no mixed parameter** gives the bound `2·θ·|Y|` (`γ = 0`), statement-level.
example {ι : Type*} (Y : Finset ι) (A : Finset α) (p : ι → α → Prop)
    [∀ y, DecidablePred (p y)] {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ y ∈ Y, ¬ InclusiveMixed θ (densityOn A (p y))) :
    ∑ y ∈ Y, (sectionDisagreement A (p y) : ℝ) / (A.card : ℝ) ^ 2 ≤ (2 * θ + 0 / 2) * Y.card :=
  sum_normalizedDisagreement_le Y A p hθ (by
    rw [Finset.filter_false_of_mem h, Finset.card_empty]; simp)

end Tests

end RegularityLemmata
