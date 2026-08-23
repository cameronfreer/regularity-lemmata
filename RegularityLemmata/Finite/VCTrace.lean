/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RelationFiber
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite traces and VC bounds

This file builds a support-sensitive trace API on Mathlib's finite set-family definitions.
Mathlib already supplies `Finset.Shatters`, `Finset.shatterer`, `Finset.vcDim`, Pajor's
inequality `Finset.card_le_card_shatterer`, and the Sauer–Shelah theorem. No parallel VC
dimension is defined here.

The added content is the finite restriction interface and the estimates whose ambient size
is the tracing support `s.card`, even when the ambient type is infinite. The latter uses
Mathlib's Pajor inequality, `powersetCard` enumeration, and the full binomial-sum identity.
-/

open Finset
open scoped FinsetFamily

namespace RegularityLemmata

section VCTrace

variable {α : Type*} [DecidableEq α]

/-- The family obtained by tracing every member of `𝒜` on `s`. -/
def traceFamily (𝒜 : Finset (Finset α)) (s : Finset α) : Finset (Finset α) :=
  𝒜.image fun t => s ∩ t

@[simp] theorem traceFamily_empty_left (s : Finset α) :
    traceFamily (∅ : Finset (Finset α)) s = ∅ := by
  simp [traceFamily]

/-- A nonempty family traced on `∅` consists of the single trace `∅`. -/
theorem traceFamily_empty_right {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜.Nonempty) :
    traceFamily 𝒜 ∅ = {∅} := by
  simpa [traceFamily] using (Finset.image_const h𝒜 (∅ : Finset α))

@[simp] theorem mem_traceFamily {𝒜 : Finset (Finset α)} {s t : Finset α} :
    t ∈ traceFamily 𝒜 s ↔ ∃ u ∈ 𝒜, s ∩ u = t := by
  simp [traceFamily]

/-- Every trace is a subset of the support on which it was taken. -/
theorem mem_traceFamily_subset {𝒜 : Finset (Finset α)} {s t : Finset α}
    (ht : t ∈ traceFamily 𝒜 s) : t ⊆ s := by
  obtain ⟨u, _, rfl⟩ := mem_traceFamily.1 ht
  exact Finset.inter_subset_left

/-- Enlarging the source family can only enlarge its family of traces. -/
theorem traceFamily_mono_left {𝒜 ℬ : Finset (Finset α)} (h𝒜ℬ : 𝒜 ⊆ ℬ)
    (s : Finset α) : traceFamily 𝒜 s ⊆ traceFamily ℬ s := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := mem_traceFamily.1 ht
  exact mem_traceFamily.2 ⟨u, h𝒜ℬ hu, rfl⟩

/-- Tracing a family already supported on `s` changes nothing. -/
theorem traceFamily_eq_self_of_subset {𝒜 : Finset (Finset α)} {s : Finset α}
    (h𝒜 : ∀ t ∈ 𝒜, t ⊆ s) : traceFamily 𝒜 s = 𝒜 := by
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := mem_traceFamily.1 ht
    simpa [Finset.inter_eq_right.2 (h𝒜 u hu)] using hu
  · intro t ht
    exact mem_traceFamily.2 ⟨t, ht, Finset.inter_eq_right.2 (h𝒜 t ht)⟩

/-- Successive traces compose by intersecting their supports. -/
theorem traceFamily_traceFamily (𝒜 : Finset (Finset α)) (s t : Finset α) :
    traceFamily (traceFamily 𝒜 s) t = traceFamily 𝒜 (t ∩ s) := by
  simp only [traceFamily, Finset.image_image]
  apply Finset.image_congr
  intro u _
  simp only [Function.comp_apply]
  rw [Finset.inter_assoc]

/-- A family shatters `s` exactly when its traces on `s` are all subsets of `s`. -/
theorem traceFamily_eq_powerset_iff {𝒜 : Finset (Finset α)} {s : Finset α} :
    traceFamily 𝒜 s = s.powerset ↔ 𝒜.Shatters s := by
  simpa [traceFamily] using (Finset.shatters_iff (𝒜 := 𝒜) (s := s)).symm

/-- Restricting a finite set family to a tracing support cannot increase VC dimension. -/
theorem vcDim_traceFamily_le (𝒜 : Finset (Finset α)) (s : Finset α) :
    (traceFamily 𝒜 s).vcDim ≤ 𝒜.vcDim := by
  unfold Finset.vcDim
  apply Finset.sup_mono
  intro t ht
  rw [Finset.mem_shatterer] at ht ⊢
  have hts : t ⊆ s := by
    obtain ⟨u, hu, htu⟩ := ht.exists_superset
    exact htu.trans (mem_traceFamily_subset hu)
  intro v hv
  obtain ⟨u, hu, huv⟩ := ht hv
  obtain ⟨w, hw, huw⟩ := mem_traceFamily.1 hu
  refine ⟨w, hw, ?_⟩
  rw [← huv, ← huw]
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxt, hxw⟩
    exact ⟨hxt, hts hxt, hxw⟩
  · rintro ⟨hxt, _, hxw⟩
    exact ⟨hxt, hxw⟩

/-- Image/intersection form of `vcDim_traceFamily_le`. -/
theorem vcDim_image_inter_le (𝒜 : Finset (Finset α)) (s : Finset α) :
    (𝒜.image fun t => s ∩ t).vcDim ≤ 𝒜.vcDim :=
  vcDim_traceFamily_le 𝒜 s

/-- The subsets of `s` of cardinality at most `d` are bounded by the corresponding
binomial sum. This is the neutral counting statement behind applications that enumerate
bounded-size sets of coordinate flips. -/
theorem card_powerset_filter_card_le_sum_choose (s : Finset α) (d : ℕ) :
    #(s.powerset.filter fun t => t.card ≤ d) ≤
      ∑ k ∈ Finset.Iic d, s.card.choose k := by
  calc
    #(s.powerset.filter fun t => t.card ≤ d) ≤
        #((Finset.Iic d).biUnion fun k => s.powersetCard k) := by
      apply Finset.card_mono
      intro t ht
      rw [Finset.mem_filter] at ht
      exact Finset.mem_biUnion.2 ⟨t.card, Finset.mem_Iic.2 ht.2,
        Finset.mem_powersetCard.2 ⟨Finset.mem_powerset.1 ht.1, rfl⟩⟩
    _ ≤ ∑ k ∈ Finset.Iic d, #(s.powersetCard k) := Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.Iic d, s.card.choose k := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.card_powersetCard k s

/-- Support-sensitive Sauer–Shelah bound for a family all of whose members lie in `s`.

Mathlib's `Finset.card_shatterer_le_sum_vcDim` counts against an entire finite ambient type.
This adapter works on an arbitrary ambient type and counts only the supplied finite support:
Pajor's inequality embeds `𝒜` into its shatterer, and every shattered set lies in the union
of the appropriate `powersetCard` slices of `s`. -/
theorem card_setFamily_le_sum_choose_of_subset (𝒜 : Finset (Finset α)) (s : Finset α)
    (h𝒜 : ∀ t ∈ 𝒜, t ⊆ s) :
    #𝒜 ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, s.card.choose k := by
  calc
    #𝒜 ≤ #𝒜.shatterer := Finset.card_le_card_shatterer 𝒜
    _ ≤ #((Finset.Iic 𝒜.vcDim).biUnion (fun k => s.powersetCard k)) := by
      apply Finset.card_mono
      intro t ht
      rw [Finset.mem_shatterer] at ht
      have hts : t ⊆ s := by
        obtain ⟨u, hu, htu⟩ := ht.exists_superset
        exact htu.trans (h𝒜 u hu)
      exact Finset.mem_biUnion.2 ⟨t.card, Finset.mem_Iic.2 ht.card_le_vcDim,
        Finset.mem_powersetCard.2 ⟨hts, rfl⟩⟩
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, #(s.powersetCard k) := Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, s.card.choose k := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.card_powersetCard k s

/-- Sauer–Shelah bound for the number of distinct traces on `s`. -/
theorem card_traceFamily_le_sum_choose (𝒜 : Finset (Finset α)) (s : Finset α) :
    #(traceFamily 𝒜 s) ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, s.card.choose k := by
  calc
    #(traceFamily 𝒜 s) ≤
        ∑ k ∈ Finset.Iic (traceFamily 𝒜 s).vcDim, s.card.choose k :=
      card_setFamily_le_sum_choose_of_subset _ _ fun _ ht => mem_traceFamily_subset ht
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, s.card.choose k := by
      exact Finset.sum_le_sum_of_subset
        (Finset.Iic_subset_Iic.2 (vcDim_traceFamily_le 𝒜 s))

/-- Image/intersection form of `card_traceFamily_le_sum_choose`. -/
theorem card_image_inter_le_sum_choose (𝒜 : Finset (Finset α)) (s : Finset α) :
    #(𝒜.image fun t => s ∩ t) ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, s.card.choose k :=
  card_traceFamily_le_sum_choose 𝒜 s

/-- A partial binomial sum through degree `d` is bounded polynomially by `(n + 1) ^ d`. -/
theorem sum_choose_le_pow (n d : ℕ) :
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ (n + 1) ^ d := by
  rw [← Nat.range_succ_eq_Iic, add_pow]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    n.choose k ≤ n ^ k := Nat.choose_le_pow n k
    _ ≤ n ^ k * 1 ^ (d - k) * d.choose k := by
      simp only [one_pow, mul_one]
      exact Nat.le_mul_of_pos_right (n ^ k) (Nat.choose_pos hkd)

/-- A partial binomial sum is also bounded by the full sum `2 ^ n`. -/
theorem sum_choose_le_two_pow (n d : ℕ) :
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ 2 ^ n := by
  rw [← Nat.sum_range_choose n]
  apply Finset.sum_le_sum_of_ne_zero
  intro k _ hk
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (Nat.le_of_not_lt fun h => hk (Nat.choose_eq_zero_of_lt h))

/-- Every trace family has at most all subsets of its support. -/
theorem card_traceFamily_le_pow (𝒜 : Finset (Finset α)) (s : Finset α) :
    #(traceFamily 𝒜 s) ≤ 2 ^ s.card :=
  (card_traceFamily_le_sum_choose 𝒜 s).trans (sum_choose_le_two_pow s.card 𝒜.vcDim)

end VCTrace

section FiberFamilyVC

variable {α β : Type*} [DecidableEq β]

/-- Sauer–Shelah bound for the number of distinct relation fibers on a finite support. -/
theorem card_fiberFamily_le_sum_choose (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    #(fiberFamily R A B) ≤
      ∑ k ∈ Finset.Iic (fiberFamily R A B).vcDim, B.card.choose k :=
  card_setFamily_le_sum_choose_of_subset _ _ fun _ ht => mem_fiberFamily_subset R A B ht

/-- Crude powerset bound for the number of distinct relation fibers on `B`. -/
theorem card_fiberFamily_le_pow (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    #(fiberFamily R A B) ≤ 2 ^ B.card :=
  (card_fiberFamily_le_sum_choose R A B).trans
    (sum_choose_le_two_pow B.card (fiberFamily R A B).vcDim)

end FiberFamilyVC

/-! ### Executable endpoint tests -/

namespace VCTraceTests

example :
    traceFamily ({{0, 1}, {1, 2}} : Finset (Finset (Fin 3))) {0, 2} = {{0}, {2}} := by
  decide

example : traceFamily (∅ : Finset (Finset (Fin 2))) ∅ = ∅ := by
  decide

example : traceFamily ({{0}} : Finset (Finset (Fin 2))) ∅ = {∅} := by
  decide

example : ({{0}, {1}} : Finset (Finset (Fin 2))).vcDim = 1 := by
  decide

example : (∑ k ∈ Finset.Iic 1, (3 : ℕ).choose k) = 4 := by
  decide

example :
    #((Finset.univ : Finset (Fin 3)).powerset.filter fun t => t.card ≤ 1) = 4 := by
  decide

example : (∑ k ∈ Finset.Iic 2, (5 : ℕ).choose k) ≤ (5 + 1) ^ 2 :=
  sum_choose_le_pow 5 2

end VCTraceTests

end RegularityLemmata
