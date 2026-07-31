/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.WeightedChoice
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

/-!
# Phase 11 unit 7 substrate: aggregate mass into selection hypotheses

`Finite/WeightedChoice.lean` supplies the selection and expectation machinery, whose
hypotheses `hbad` and `hexp` are stated as PER-EVENT masses against the total weight. This
file is the seam on the other side: it converts AGGREGATE mass estimates — the form actual
combinatorial bounds come in — into those hypotheses.

* `sum_le_sum_of_exists_mem` — the union bound: a set every element of which lies in at
  least one of finitely many sets has mass at most the summed masses. This is where a
  colour multiplicity comes from when one condition must hold simultaneously for every
  colour of a finite palette.
* `sum_event_mass_le_of_weight_floor` — a uniform floor `w₀` on the coordinate weights turns
  the per-event masses of the `hbad` hypothesis into the AGGREGATE event mass scaled by
  `w₀⁻²` and the total weight. The number of events multiplies nothing: each event
  contributes only its own mass.
* `sum_piFinset_weight_mul_eventCost_le_of_weight_floor` — the two composed for the cost
  channel: an aggregate event-mass bound produces the `μ` input directly, for the
  unit-charge event cost.

All three are generic: no partition, no relation, no palette appears.
-/

namespace RegularityLemmata

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- **The union bound.** A set every element of which lies in at least one of finitely many
sets has mass at most the summed masses. This is where a palette factor comes from when one
forbidden condition must hold for EVERY colour simultaneously: the forbidden set is the
union of the per-colour ones, not a product of the event index with the colours. -/
theorem sum_le_sum_of_exists_mem {γ κ : Type*} [DecidableEq γ] [Fintype κ]
    (S : Finset γ) (T : κ → Finset γ) (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcov : ∀ x ∈ S, ∃ k, x ∈ T k) :
    ∑ x ∈ S, f x ≤ ∑ k, ∑ x ∈ T k, f x := by
  classical
  calc ∑ x ∈ S, f x
      ≤ ∑ x ∈ S, ∑ k : κ, (if x ∈ T k then f x else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨k, hk⟩ := hcov x hx
        have hterm : f x = (if x ∈ T k then f x else 0) := by rw [if_pos hk]
        refine le_trans (le_of_eq hterm) (Finset.single_le_sum
          (f := fun k => if x ∈ T k then f x else 0)
          (fun k _ => by by_cases h : x ∈ T k <;> simp [h, hf x]) (Finset.mem_univ k))
    _ = ∑ k : κ, ∑ x ∈ S, (if x ∈ T k then f x else 0) := Finset.sum_comm
    _ ≤ ∑ k : κ, ∑ x ∈ T k, f x := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_ite_mem]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          fun x _ _ => hf x

/-- **The event budget is the aggregate mass divided by the squared weight floor.** For an
event `e` the product `hbad` omits is the total product divided by the two coordinate
weights, so a uniform floor `w₀` on those weights converts the `hbad` left-hand side into
the AGGREGATE event mass, scaled by `w₀⁻²` and the total weight. The number of events never
multiplies anything: each event contributes only its own mass. -/
theorem sum_event_mass_le_of_weight_floor {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) (Bad : E → Finset (β × β))
    {w₀ : ℝ} (hw₀ : 0 < w₀) (hW : ∀ j, w₀ ≤ ∑ x ∈ t j, wt x) :
    ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x
      ≤ (∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) / w₀ ^ 2
        * ∏ j, ∑ x ∈ t j, wt x := by
  classical
  set W : ι → ℝ := fun j => ∑ x ∈ t j, wt x with hWdef
  have hWpos : ∀ j, 0 < W j := fun j => lt_of_lt_of_le hw₀ (hW j)
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  have hmass : (0 : ℝ) ≤ ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hwt _) (hwt _)
  rw [← Finset.sum_mul]
  have hmem₂ : i₂ e ∈ Finset.univ.erase (i₁ e) :=
    Finset.mem_erase.mpr ⟨(hne e).symm, Finset.mem_univ _⟩
  have hsplit : W (i₁ e) * (W (i₂ e) * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j)
      = ∏ j, W j := by
    rw [Finset.mul_prod_erase _ W hmem₂, Finset.mul_prod_erase _ W (Finset.mem_univ (i₁ e))]
  have hrest : (0 : ℝ) ≤ ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j :=
    Finset.prod_nonneg fun j _ => (hWpos j).le
  have hbound : ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j ≤ (∏ j, W j) / w₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j) * w₀ ^ 2
        ≤ (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j) * (W (i₁ e) * W (i₂ e)) := by
          have := mul_le_mul (hW (i₁ e)) (hW (i₂ e)) hw₀.le (hWpos (i₁ e)).le
          nlinarith [hrest]
      _ = ∏ j, W j := by rw [← hsplit]; ring
  calc (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j
      ≤ (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) * ((∏ j, W j) / w₀ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hmass
    _ = (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) / w₀ ^ 2 * ∏ j, W j := by
        ring

/-- **The cost channel in one step.** An aggregate bound `A` on the summed event masses
produces the `μ` input of `exists_piFinset_forall_not_mem_bad_cost_le` directly, for the
unit-charge event cost: `μ = A / w₀ ^ 2`. -/
theorem sum_piFinset_weight_mul_eventCost_le_of_weight_floor {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) (Dev : E → Finset (β × β))
    {w₀ A : ℝ} (hw₀ : 0 < w₀) (hW : ∀ j, w₀ ≤ ∑ x ∈ t j, wt x)
    (hagg : ∑ e : E, ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2 ≤ A) :
    ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j))
        * (∑ e : E, if (g (i₁ e), g (i₂ e)) ∈ Dev e then (1 : ℝ) else 0)
      ≤ A / w₀ ^ 2 * ∏ j, ∑ x ∈ t j, wt x := by
  classical
  have hprod : (0 : ℝ) ≤ ∏ j, ∑ x ∈ t j, wt x :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun x _ => hwt x
  rw [sum_piFinset_weight_mul_eventCost t wt i₁ i₂ hne Dev (fun _ => (1 : ℝ))]
  simp only [one_mul]
  refine le_trans (sum_event_mass_le_of_weight_floor t wt hwt i₁ i₂ hne Dev hw₀ hW) ?_
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hagg (by positivity)) hprod

/-! ### Tests -/

section Tests

-- The factorization is genuinely event-count free: with an EMPTY forbidden family the
-- budget is zero however many events there are.
example {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] {E : Type*} [Fintype E]
    (t : ι → Finset β) (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ j, w₀ ≤ ∑ _ ∈ t j, (1 : ℝ)) :
    ∑ e : E, ∑ _ ∈ (∅ : Finset (β × β)) ∩ (t (i₁ e) ×ˢ t (i₂ e)), (1 : ℝ) * 1
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ _ ∈ t j, (1 : ℝ)
      ≤ (∑ e : E, ∑ _ ∈ (∅ : Finset (β × β)) ∩ (t (i₁ e) ×ˢ t (i₂ e)), (1 : ℝ) * 1) / w₀ ^ 2
        * ∏ j, ∑ _ ∈ t j, (1 : ℝ) :=
  sum_event_mass_le_of_weight_floor t (fun _ => 1) (fun _ => zero_le_one) i₁ i₂ hne
    (fun _ => ∅) hw₀ hW

end Tests

end RegularityLemmata
