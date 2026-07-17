/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
  have hswap : ∑ e : E, ∑ g ∈ (Fintype.piFinset t).filter
        (fun g => (g (i₁ e), g (i₂ e)) ∈ Bad e), ∏ j, wt (g j)
      = ∑ g ∈ Fintype.piFinset t,
          ((Finset.univ.filter
            (fun e : E => (g (i₁ e), g (i₂ e)) ∈ Bad e)).card : ℝ)
            * ∏ j, wt (g j) := by
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

end Tests
