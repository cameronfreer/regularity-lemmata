/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Phase 11 unit 7 substrate: abstract weighted selection

The finite weighted-choice lemma behind the role-indexed representative selection
(Phase 11 design freeze in `ARCHITECTURE.md`), with **all constants exposed** — raw
weighted masses, no probability vocabulary.

Selections are elements of `Fintype.piFinset t` for a candidate family
`t : ι → Finset β`, weighted by the product `∏ j, wt (g j)`. The three layers:

* `sum_piFinset_pinned_two` — pinning two DISTINCT coordinates factorizes the total
  weight: the pinned weights times the full weights of the remaining coordinates.
* `sum_piFinset_filter_pair_mem` — marginalization: the weight of the selections whose
  `(i₁, i₂)`-pair lands in a bad set `B` is the `B`-restricted pair mass times the
  remaining coordinates' weight.
* `exists_piFinset_forall_not_mem_bad` — the union bound: if the summed bad-event
  masses are strictly below the total weight, some selection avoids every bad event.

The events carry two distinct coordinates each (`i₁ e ≠ i₂ e`); in the application
the coordinates are (cell, role) pairs, so events over EQUAL cells with distinct roles
are perfectly admissible — exactly the diagonal case the removal route needs.
-/

namespace RegularityLemmata

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- **Pinning two distinct coordinates factorizes the weight.** -/
theorem sum_piFinset_pinned_two (t : ι → Finset β) (wt : β → ℝ) {i₁ i₂ : ι}
    (hne : i₁ ≠ i₂) {a b : β} (ha : a ∈ t i₁) (hb : b ∈ t i₂) :
    ∑ g ∈ (Fintype.piFinset t).filter (fun g => g i₁ = a ∧ g i₂ = b), ∏ j, wt (g j)
      = wt a * wt b
        * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, ∑ x ∈ t j, wt x := by
  classical
  have hset : (Fintype.piFinset t).filter (fun g => g i₁ = a ∧ g i₂ = b)
      = Fintype.piFinset (Function.update (Function.update t i₁ {a}) i₂ {b}) := by
    ext g
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hg, h1, h2⟩ j
      rcases eq_or_ne j i₂ with rfl | hj2
      · rw [Function.update_self]
        exact Finset.mem_singleton.mpr h2
      · rw [Function.update_of_ne hj2]
        rcases eq_or_ne j i₁ with rfl | hj1
        · rw [Function.update_self]
          exact Finset.mem_singleton.mpr h1
        · rw [Function.update_of_ne hj1]
          exact hg j
    · intro hg
      refine ⟨fun j => ?_, ?_, ?_⟩
      · have hgj := hg j
        rcases eq_or_ne j i₂ with rfl | hj2
        · rw [Function.update_self] at hgj
          rw [Finset.mem_singleton.mp hgj]
          exact hb
        · rw [Function.update_of_ne hj2] at hgj
          rcases eq_or_ne j i₁ with rfl | hj1
          · rw [Function.update_self] at hgj
            rw [Finset.mem_singleton.mp hgj]
            exact ha
          · rwa [Function.update_of_ne hj1] at hgj
      · have hgi := hg i₁
        rw [Function.update_of_ne hne, Function.update_self] at hgi
        exact Finset.mem_singleton.mp hgi
      · have hgi := hg i₂
        rw [Function.update_self] at hgi
        exact Finset.mem_singleton.mp hgi
  rw [hset, ← Finset.prod_univ_sum]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁),
    ← Finset.mul_prod_erase (Finset.univ.erase i₁) _
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩)]
  have hFi₁ : ∑ x ∈ Function.update (Function.update t i₁ {a}) i₂ {b} i₁, wt x
      = wt a := by
    rw [Function.update_of_ne hne, Function.update_self, Finset.sum_singleton]
  have hFi₂ : ∑ x ∈ Function.update (Function.update t i₁ {a}) i₂ {b} i₂, wt x
      = wt b := by
    rw [Function.update_self, Finset.sum_singleton]
  have hFrest : ∏ j ∈ (Finset.univ.erase i₁).erase i₂,
        (∑ x ∈ Function.update (Function.update t i₁ {a}) i₂ {b} j, wt x)
      = ∏ j ∈ (Finset.univ.erase i₁).erase i₂, ∑ x ∈ t j, wt x := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1, Function.update_of_ne hj.2.1]
  rw [hFi₁, hFi₂, hFrest, mul_assoc]

/-- **Marginalization over a bad pair set.** -/
theorem sum_piFinset_filter_pair_mem (t : ι → Finset β) (wt : β → ℝ) {i₁ i₂ : ι}
    (hne : i₁ ≠ i₂) (B : Finset (β × β)) :
    ∑ g ∈ (Fintype.piFinset t).filter (fun g => (g i₁, g i₂) ∈ B), ∏ j, wt (g j)
      = ∑ p ∈ B ∩ (t i₁ ×ˢ t i₂), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, ∑ x ∈ t j, wt x := by
  classical
  have hmaps : ∀ g ∈ (Fintype.piFinset t).filter (fun g => (g i₁, g i₂) ∈ B),
      (fun g : ι → β => (g i₁, g i₂)) g ∈ B ∩ (t i₁ ×ˢ t i₂) := by
    intro g hg
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hg
    exact Finset.mem_inter.mpr
      ⟨hg.2, Finset.mem_product.mpr ⟨hg.1 i₁, hg.1 i₂⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun g : ι → β => ∏ j, wt (g j))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_inter, Finset.mem_product] at hp
  have hfilter : ((Fintype.piFinset t).filter
        (fun g => (g i₁, g i₂) ∈ B)).filter (fun g => (g i₁, g i₂) = p)
      = (Fintype.piFinset t).filter (fun g => g i₁ = p.1 ∧ g i₂ = p.2) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hg, _⟩, hpin⟩
      exact ⟨hg, congrArg Prod.fst hpin, congrArg Prod.snd hpin⟩
    · rintro ⟨hg, h1, h2⟩
      have hpin : (g i₁, g i₂) = p := Prod.ext h1 h2
      exact ⟨⟨hg, hpin ▸ hp.1⟩, hpin⟩
  rw [hfilter, sum_piFinset_pinned_two t wt hne hp.2.1 hp.2.2]

/-- **Covering-count identity.** Summing each event's bad-selection mass counts every
selection with multiplicity the number of events it violates. -/
theorem sum_filter_pair_mem_eq_badCount {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (i₁ i₂ : E → ι) (Bad : E → Finset (β × β)) :
    ∑ e : E, ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => (g (i₁ e), g (i₂ e)) ∈ Bad e), ∏ j, wt (g j)
      = ∑ g ∈ Fintype.piFinset t,
          ((Finset.univ.filter
            (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
            * ∏ j, wt (g j) := by
  classical
  calc ∑ e : E, ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => (g (i₁ e), g (i₂ e)) ∈ Bad e), ∏ j, wt (g j)
      = ∑ e : E, ∑ g ∈ Fintype.piFinset t,
          if (g (i₁ e), g (i₂ e)) ∈ Bad e then ∏ j, wt (g j) else 0 := by
        exact Finset.sum_congr rfl fun e _ => Finset.sum_filter _ _
    _ = ∑ g ∈ Fintype.piFinset t, ∑ e : E,
          if (g (i₁ e), g (i₂ e)) ∈ Bad e then ∏ j, wt (g j) else 0 :=
        Finset.sum_comm
    _ = ∑ g ∈ Fintype.piFinset t,
          ((Finset.univ.filter
            (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
            * ∏ j, wt (g j) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **The weighted union bound.** If the summed masses of the bad events are strictly
below the total selection weight, some selection avoids every bad event. Events carry
two DISTINCT coordinates; equal-cell distinct-role events are admissible. -/
theorem exists_piFinset_forall_not_mem_bad {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) (Bad : E → Finset (β × β))
    (hlt : ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x
        < ∏ j, ∑ x ∈ t j, wt x) :
    ∃ g ∈ Fintype.piFinset t, ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e := by
  classical
  by_contra hcon
  push Not at hcon
  have hprodnn : ∀ g : ι → β, 0 ≤ ∏ j, wt (g j) :=
    fun g => Finset.prod_nonneg fun j _ => hwt _
  have htotal : ∏ j, ∑ x ∈ t j, wt x
      = ∑ g ∈ Fintype.piFinset t, ∏ j, wt (g j) :=
    Finset.prod_univ_sum t fun _ x => wt x
  have hswap := sum_filter_pair_mem_eq_badCount t wt i₁ i₂ Bad
  have hcover : ∀ g ∈ Fintype.piFinset t,
      (1 : ℝ) ≤ ((Finset.univ.filter
        (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ) := by
    intro g hg
    obtain ⟨e, he⟩ := hcon g hg
    have hmem : e ∈ Finset.univ.filter
        (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
    have hpos : 0 < (Finset.univ.filter
        (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card :=
      Finset.card_pos.mpr ⟨e, hmem⟩
    exact_mod_cast hpos
  have hge : ∑ g ∈ Fintype.piFinset t, ∏ j, wt (g j)
      ≤ ∑ g ∈ Fintype.piFinset t,
          ((Finset.univ.filter
            (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
            * ∏ j, wt (g j) :=
    Finset.sum_le_sum fun g hg =>
      le_mul_of_one_le_left (hprodnn g) (hcover g hg)
  have hmarg : ∑ e : E, ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => (g (i₁ e), g (i₂ e)) ∈ Bad e), ∏ j, wt (g j)
      = ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
    Finset.sum_congr rfl fun e _ =>
      sum_piFinset_filter_pair_mem t wt (hne e) (Bad e)
  rw [htotal] at hlt
  rw [← hmarg, hswap] at hlt
  linarith

/-- **Expected-cost identity for event-indicator costs.** The weighted total of a cost
that charges `w e` whenever the selection's `e`-pair lands in `Dev e` equals the sum of
the per-event charges times the marginalized `Dev`-pair masses. This is the mechanical
route to the `μ` input of `exists_piFinset_forall_not_mem_bad_cost_le`: in the intended
application the events range over the six ordered role pairs and the `K` palette
colors, each `Dev`-mass is controlled by the witness deviance bound, and the
per-event weights are the coarse-pair volumes. -/
theorem sum_piFinset_weight_mul_eventCost {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e)
    (Dev : E → Finset (β × β)) (w : E → ℝ) :
    ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j))
        * (∑ e : E, if (g (i₁ e), g (i₂ e)) ∈ Dev e then w e else 0)
      = ∑ e : E, w e * ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x := by
  classical
  calc ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j))
        * (∑ e : E, if (g (i₁ e), g (i₂ e)) ∈ Dev e then w e else 0)
      = ∑ g ∈ Fintype.piFinset t, ∑ e : E,
          if (g (i₁ e), g (i₂ e)) ∈ Dev e then w e * ∏ j, wt (g j) else 0 := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_ite, mul_zero, mul_comm (∏ j, wt (g j)) (w e)]
    _ = ∑ e : E, ∑ g ∈ Fintype.piFinset t,
          if (g (i₁ e), g (i₂ e)) ∈ Dev e then w e * ∏ j, wt (g j) else 0 :=
        Finset.sum_comm
    _ = ∑ e : E, w e * ∑ g ∈ (Fintype.piFinset t).filter
          (fun g => (g (i₁ e), g (i₂ e)) ∈ Dev e), ∏ j, wt (g j) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_filter, Finset.mul_sum]
    _ = ∑ e : E, w e * ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
        Finset.sum_congr rfl fun e _ => by
          rw [sum_piFinset_filter_pair_mem t wt (hne e) (Dev e)]

/-- **Per-event factor accounting.** Pinned-pair bounds
`w e · (Dev-restricted pair mass) ≤ μe e · (pinned-coordinate weights)` convert the
expected-cost identity into the `μ = ∑ e, μe e` input of the conditioned selection
bound, with no reference to the remaining coordinates. -/
theorem sum_piFinset_weight_mul_eventCost_le {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e)
    (Dev : E → Finset (β × β)) (w μe : E → ℝ)
    (hμe : ∀ e : E, w e * ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
        ≤ μe e * ((∑ x ∈ t (i₁ e), wt x) * ∑ x ∈ t (i₂ e), wt x)) :
    ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j))
        * (∑ e : E, if (g (i₁ e), g (i₂ e)) ∈ Dev e then w e else 0)
      ≤ (∑ e : E, μe e) * ∏ j, ∑ x ∈ t j, wt x := by
  classical
  rw [sum_piFinset_weight_mul_eventCost t wt i₁ i₂ hne Dev w, Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  have hR : 0 ≤ ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun x _ => hwt x
  have hprod : ∏ j, ∑ x ∈ t j, wt x
      = (∑ x ∈ t (i₁ e), wt x) * ((∑ x ∈ t (i₂ e), wt x)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (i₁ e)),
      ← Finset.mul_prod_erase (Finset.univ.erase (i₁ e)) _
        (Finset.mem_erase.mpr ⟨(hne e).symm, Finset.mem_univ (i₂ e)⟩)]
  have hfac : ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x
      = (∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
    (Finset.sum_mul _ _ _).symm
  rw [hfac, hprod]
  calc w e * ((∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x)
      = (w e * ∑ p ∈ Dev e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
        (mul_assoc _ _ _).symm
    _ ≤ (μe e * ((∑ x ∈ t (i₁ e), wt x) * ∑ x ∈ t (i₂ e), wt x))
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
        mul_le_mul_of_nonneg_right (hμe e) hR
    _ = μe e * ((∑ x ∈ t (i₁ e), wt x) * ((∑ x ∈ t (i₂ e), wt x)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x)) := by
        ring

/-- **The conditioned selection-with-cost bound.**

    bad selection mass ≤ σ · total,   σ < 1
    weighted expected cost ≤ μ · total
    ─────────────────────────────────────────
    ∃ good selection with cost ≤ μ / (1 − σ)

Conditioning on avoiding every bad event inflates the expected-cost bound by exactly
the factor `1/(1 − σ)`; with the half-budget `σ ≤ 1/2` this is a factor `2`. The bound
is honest: without the conditioning factor the conclusion is FALSE (a cost supported
exactly on the good selections has conditional average `μ/(1 − σ)`, not `μ`). -/
theorem exists_piFinset_forall_not_mem_bad_cost_le {E : Type*} [Fintype E]
    (t : ι → Finset β) (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) (Bad : E → Finset (β × β))
    (cost : (ι → β) → ℝ) (hcost : ∀ g, 0 ≤ cost g) {σ μ : ℝ} (hσ : σ < 1)
    (hWpos : 0 < ∏ j, ∑ x ∈ t j, wt x)
    (hbad : ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x
        ≤ σ * ∏ j, ∑ x ∈ t j, wt x)
    (hexp : ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j)) * cost g
        ≤ μ * ∏ j, ∑ x ∈ t j, wt x) :
    ∃ g ∈ Fintype.piFinset t,
      (∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e) ∧ cost g ≤ μ / (1 - σ) := by
  classical
  have hσ' : (0 : ℝ) < 1 - σ := by linarith
  have hprodnn : ∀ g : ι → β, 0 ≤ ∏ j, wt (g j) :=
    fun g => Finset.prod_nonneg fun j _ => hwt _
  -- The complement mass is at most the summed event masses (covering count ≥ 1).
  have hcompl : ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => ¬ ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j)
      ≤ σ * ∏ j, ∑ x ∈ t j, wt x := by
    calc ∑ g ∈ (Fintype.piFinset t).filter
          (fun g => ¬ ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j)
        ≤ ∑ g ∈ (Fintype.piFinset t).filter
            (fun g => ¬ ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e),
            ((Finset.univ.filter
              (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
              * ∏ j, wt (g j) := by
          refine Finset.sum_le_sum fun g hg => ?_
          rw [Finset.mem_filter] at hg
          push Not at hg
          obtain ⟨e, he⟩ := hg.2
          have hone : (1 : ℝ) ≤ ((Finset.univ.filter
              (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ) := by
            exact_mod_cast Finset.card_pos.mpr
              ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩⟩
          exact le_mul_of_one_le_left (hprodnn g) hone
      _ ≤ ∑ g ∈ Fintype.piFinset t,
            ((Finset.univ.filter
              (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
              * ∏ j, wt (g j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun g _ _ => mul_nonneg (Nat.cast_nonneg _) (hprodnn g)
      _ = ∑ e : E, ∑ g ∈ (Fintype.piFinset t).filter
            (fun g => (g (i₁ e), g (i₂ e)) ∈ Bad e), ∏ j, wt (g j) :=
          (sum_filter_pair_mem_eq_badCount t wt i₁ i₂ Bad).symm
      _ = ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
            * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x :=
          Finset.sum_congr rfl fun e _ =>
            sum_piFinset_filter_pair_mem t wt (hne e) (Bad e)
      _ ≤ σ * ∏ j, ∑ x ∈ t j, wt x := hbad
  -- Hence the good selections carry mass at least `(1 − σ)` times the total.
  have htotal : ∏ j, ∑ x ∈ t j, wt x
      = ∑ g ∈ Fintype.piFinset t, ∏ j, wt (g j) :=
    Finset.prod_univ_sum t fun _ x => wt x
  have hsplit : ∑ g ∈ Fintype.piFinset t, ∏ j, wt (g j)
      = (∑ g ∈ (Fintype.piFinset t).filter
          (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j))
        + ∑ g ∈ (Fintype.piFinset t).filter
            (fun g => ¬ ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hgoodmass : (1 - σ) * ∏ j, ∑ x ∈ t j, wt x
      ≤ ∑ g ∈ (Fintype.piFinset t).filter
          (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j) := by
    nlinarith [hcompl, htotal, hsplit]
  have hμ0 : 0 ≤ μ := by
    have h0 : (0 : ℝ) ≤ ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j)) * cost g :=
      Finset.sum_nonneg fun g _ => mul_nonneg (hprodnn g) (hcost g)
    nlinarith [hWpos, hexp]
  by_contra hcon
  push Not at hcon
  -- Some good selection has positive weight (the good mass is positive).
  have hgoodpos : 0 < ∑ g ∈ (Fintype.piFinset t).filter
      (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j) :=
    lt_of_lt_of_le (mul_pos hσ' hWpos) hgoodmass
  obtain ⟨g₀, hg₀, hFg₀⟩ : ∃ g ∈ (Fintype.piFinset t).filter
      (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), 0 < ∏ j, wt (g j) := by
    by_contra hz
    push Not at hz
    exact absurd hgoodpos (not_lt.mpr (Finset.sum_nonpos fun g hg => hz g hg))
  -- If every good selection had cost above `μ/(1 − σ)`, the strict weighted average
  -- on the good set would exceed the total expected cost — a contradiction.
  have hstrict : μ / (1 - σ) * ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j)
      < ∑ g ∈ (Fintype.piFinset t).filter
          (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e),
          (∏ j, wt (g j)) * cost g := by
    rw [Finset.mul_sum]
    refine Finset.sum_lt_sum (fun g hg => ?_) ⟨g₀, hg₀, ?_⟩
    · obtain ⟨hgpi, hgood⟩ := Finset.mem_filter.mp hg
      have hcg : μ / (1 - σ) < cost g := hcon g hgpi hgood
      rw [mul_comm (μ / (1 - σ)) (∏ j, wt (g j))]
      exact mul_le_mul_of_nonneg_left hcg.le (hprodnn g)
    · obtain ⟨hgpi, hgood⟩ := Finset.mem_filter.mp hg₀
      have hcg : μ / (1 - σ) < cost g₀ := hcon g₀ hgpi hgood
      calc μ / (1 - σ) * ∏ j, wt (g₀ j)
          < cost g₀ * ∏ j, wt (g₀ j) := mul_lt_mul_of_pos_right hcg hFg₀
        _ = (∏ j, wt (g₀ j)) * cost g₀ := mul_comm _ _
  have hsub : ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), (∏ j, wt (g j)) * cost g
      ≤ ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j)) * cost g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun g _ _ => mul_nonneg (hprodnn g) (hcost g)
  have hc₀nn : 0 ≤ μ / (1 - σ) := div_nonneg hμ0 hσ'.le
  have hlast : μ / (1 - σ) * ((1 - σ) * ∏ j, ∑ x ∈ t j, wt x)
      ≤ μ / (1 - σ) * ∑ g ∈ (Fintype.piFinset t).filter
          (fun g => ∀ e : E, (g (i₁ e), g (i₂ e)) ∉ Bad e), ∏ j, wt (g j) :=
    mul_le_mul_of_nonneg_left hgoodmass hc₀nn
  have hid : μ / (1 - σ) * ((1 - σ) * ∏ j, ∑ x ∈ t j, wt x)
      = μ * ∏ j, ∑ x ∈ t j, wt x := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hσ')]
  linarith

/-! ### Tests and adversarial examples -/

section Tests

-- With no events, any candidate family of positive total weight admits a selection.
example (t : Fin 2 → Finset (Fin 3)) (wt : Fin 3 → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hpos : 0 < ∏ j, ∑ x ∈ t j, wt x) :
    ∃ g ∈ Fintype.piFinset t, ∀ e : Empty,
      (g (Empty.elim e), g (Empty.elim e)) ∉ (Empty.elim e : Finset (Fin 3 × Fin 3)) :=
  exists_piFinset_forall_not_mem_bad t wt hwt Empty.elim Empty.elim
    (fun e => e.elim) Empty.elim (by simpa using hpos)

-- Equal-CELL events with distinct ROLES are admissible: the two coordinates of an
-- event live in a product index, so distinctness of the second components suffices —
-- statement-level, with the index type `Fin 1 × Fin 2` (one cell, two roles).
example (t : Fin 1 × Fin 2 → Finset (Fin 3)) (wt : Fin 3 → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (Bad : Unit → Finset (Fin 3 × Fin 3))
    (hlt : ∑ e : Unit, ∑ p ∈ Bad e ∩ (t (0, 0) ×ˢ t (0, 1)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (0, 0)).erase (0, 1), ∑ x ∈ t j, wt x
        < ∏ j, ∑ x ∈ t j, wt x) :
    ∃ g ∈ Fintype.piFinset t, ∀ e : Unit, (g (0, 0), g (0, 1)) ∉ Bad e :=
  exists_piFinset_forall_not_mem_bad t wt hwt (fun _ => (0, 0)) (fun _ => (0, 1))
    (fun _ => by decide) Bad hlt

-- SHARPNESS of the conditioning factor. Two equal-weight selections over
-- `t = ![{0, 1}, {0}]` (unit weights), one event marking `![1, 0]` bad, and ALL cost
-- on the surviving selection `![0, 0]`. The inputs hold with equality at
-- `σ = μ = 1/2`, and EVERY good selection has cost exactly `μ/(1 − σ) = 1 > μ`:
-- the factor `1/(1 − σ)` is attained and cannot be improved, and the unconditioned
-- bound `cost ≤ μ` is FALSE for this instance.
section Sharpness

private abbrev tSharp : Fin 2 → Finset (Fin 2) := ![{0, 1}, {0}]

private abbrev badSharp : Finset (Fin 2 × Fin 2) := {(1, 0)}

private abbrev costSharp : (Fin 2 → Fin 2) → ℝ := fun g => if g 0 = 0 then 1 else 0

-- The theorem applies at `σ = μ = 1/2` and yields a good selection of cost ≤ 1…
example : ∃ g ∈ Fintype.piFinset tSharp,
    (∀ _e : Unit, (g 0, g 1) ∉ badSharp) ∧ costSharp g ≤ (1 / 2 : ℝ) / (1 - 1 / 2) := by
  have hpi : Fintype.piFinset tSharp = {![0, 0], ![1, 0]} := by decide
  refine exists_piFinset_forall_not_mem_bad_cost_le (σ := 1 / 2) (μ := 1 / 2) tSharp
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun _ : Unit => 0) (fun _ => 1)
    (fun _ => by decide) (fun _ => badSharp) costSharp
    (fun g => by dsimp only [costSharp]; split <;> norm_num) (by norm_num) ?_ ?_ ?_
  · -- total weight `2 > 0`
    rw [Fin.prod_univ_two]
    norm_num
  · -- bad mass `= 1 = σ · 2` with `σ = 1/2`, exactly
    rw [Fin.prod_univ_two]
    have hinter : badSharp ∩ (tSharp 0 ×ˢ tSharp 1) = {(1, 0)} := by decide
    have hempty : ((Finset.univ.erase (0 : Fin 2)).erase 1) = ∅ := by decide
    rw [Finset.sum_const, Finset.card_univ, hinter, hempty]
    norm_num
  · -- expected cost `= 1 = μ · 2` with `μ = 1/2`, exactly
    rw [hpi, Fin.prod_univ_two]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [costSharp]

-- …and the factor is ATTAINED: every good selection has cost exactly
-- `μ/(1 − σ) = 1`, strictly above `μ = 1/2`.
example : ∀ g ∈ Fintype.piFinset tSharp, (g 0, g 1) ∉ badSharp →
    costSharp g = (1 / 2 : ℝ) / (1 - 1 / 2) := by
  intro g hg hgood
  have h1 : g 1 = 0 := by
    have := Fintype.mem_piFinset.mp hg 1
    simpa [tSharp] using this
  have h0 : g 0 = 0 := by
    have hne : g 0 ≠ 1 := fun h => hgood (by simp [badSharp, h, h1])
    omega
  rw [costSharp, if_pos h0]
  norm_num

end Sharpness

-- The conditioned cost bound at the degenerate parameters: no events, zero cost,
-- `σ = 0` — the conclusion specializes to the plain union bound with cost `≤ μ`.
example (t : Fin 2 → Finset (Fin 3)) (wt : Fin 3 → ℝ) (hwt : ∀ x, 0 ≤ wt x)
    (hpos : 0 < ∏ j, ∑ x ∈ t j, wt x) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ g ∈ Fintype.piFinset t, (∀ e : Empty,
        (g (Empty.elim e), g (Empty.elim e)) ∉ (Empty.elim e : Finset (Fin 3 × Fin 3)))
      ∧ (fun _ : Fin 2 → Fin 3 => (0 : ℝ)) g ≤ μ / (1 - 0) :=
  exists_piFinset_forall_not_mem_bad_cost_le t wt hwt Empty.elim Empty.elim
    (fun e => e.elim) Empty.elim _ (fun _ => le_refl 0) (by norm_num) hpos
    (by simp) (by simpa using mul_nonneg hμ hpos.le)

end Tests
