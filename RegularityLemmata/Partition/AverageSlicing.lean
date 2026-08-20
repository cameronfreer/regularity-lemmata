/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.BalancedSlicing
import RegularityLemmata.Finite.AlmostConstant

/-!
# Average slicing: block-average control from balanced slicing

Splitting a set into blocks of exact size `s` on which **every** function of a finite
`[0,1]`-valued family keeps its average within `2ν + (1 + ν)β` of the global average. The
composition is two existing pieces:

* `exists_balanced_slicing` — per-block **set-density** control for a finite trace family
  (the sampling stack, no new concentration);
* `abs_averageOn_sub_averageOn_le_of_levelSets` — the level-set staircase, reducing
  `[0,1]`-average control to density control of the `⌈1/ν⌉` level sets per function.

The trace family therefore has at most `q · ⌈1/ν⌉` sets for `q` functions; this factor
enters only the geometric ratio hypothesis (see `Partition/SlicingThreshold.lean` for the
named thresholds discharging it). The control is **two-sided** (`|·| ≤`).
-/

namespace RegularityLemmata

variable {α : Type*}

/-- **Average slicing**: under the balanced-slicing ratio hypothesis for the
`q · ⌈1/ν⌉`-member level-set trace family, a nonempty set splits into `A.card / s` pairwise
disjoint blocks of exact size `s`, on each of which every function of the family keeps its
average within `2ν + (1 + ν)β` of its `A`-average. -/
theorem exists_average_slicing [DecidableEq α] (A : Finset α) {q : ℕ} (φ : Fin q → α → ℝ)
    {s t : ℕ} {β ν : ℝ}
    (hA : A.Nonempty) (hs : 0 < s) (ht : t < s) (htβ : (t : ℝ) ≤ β * s) (hβ : 0 ≤ β)
    (hν : 0 < ν)
    (hrange : ∀ i, ∀ x ∈ A, φ i x ∈ Set.Icc (0 : ℝ) 1)
    (hratio : (A.card / s) * (2 * (q * ⌈1 / ν⌉₊)) * (2 * s - t) ^ (t / 8)
      < (2 * s) ^ (t / 8)) :
    ∃ block : Fin (A.card / s) → Finset α,
      (∀ j, (block j).card = s) ∧
      (∀ j, block j ⊆ A) ∧
      (∀ {j j'}, j ≠ j' → Disjoint (block j) (block j')) ∧
      ∀ i j, |averageOn (block j) (φ i) - averageOn A (φ i)| ≤ 2 * ν + (1 + ν) * β := by
  classical
  -- The level-set trace family.
  set F : Finset (Finset α) :=
    ((Finset.univ : Finset (Fin q)) ×ˢ Finset.Icc 1 ⌈1 / ν⌉₊).image
      (fun p ↦ A.filter fun x ↦ (p.2 : ℝ) * ν ≤ φ p.1 x) with hF
  have hFcard : F.card ≤ q * ⌈1 / ν⌉₊ := by
    calc F.card ≤ ((Finset.univ : Finset (Fin q)) ×ˢ Finset.Icc 1 ⌈1 / ν⌉₊).card :=
          Finset.card_image_le
      _ = q * ⌈1 / ν⌉₊ := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hratio' : (A.card / s) * (2 * F.card) * (2 * s - t) ^ (t / 8)
      < (2 * s) ^ (t / 8) := by
    refine lt_of_le_of_lt ?_ hratio
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hFcard))
  obtain ⟨cert, hcert⟩ := exists_balanced_slicing A F hA hs ht htβ hratio'
  refine ⟨cert.block, cert.block_card, cert.block_subset,
    fun hjj ↦ cert.block_disjoint hjj, ?_⟩
  intro i j
  have hQne : (cert.block j).Nonempty := by
    rw [← Finset.card_pos, cert.block_card j]
    exact hs
  refine abs_averageOn_sub_averageOn_le_of_levelSets hν hβ (cert.block_subset j) hQne
    (hrange i) ?_
  intro r hr1 hrν
  -- The level set is a member of the trace family: `r ≤ ⌈1/ν⌉` since `r · ν ≤ 1`.
  have hrceil : r ≤ ⌈1 / ν⌉₊ := by
    have h1 : (r : ℝ) ≤ 1 / ν := (le_div_iff₀ hν).mpr hrν
    have h2 : (r : ℝ) ≤ (⌈1 / ν⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hmem : (A.filter fun x ↦ (r : ℝ) * ν ≤ φ i x) ∈ F := by
    rw [hF]
    exact Finset.mem_image.mpr ⟨(i, r),
      Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_Icc.mpr ⟨hr1, hrceil⟩⟩, rfl⟩
  have h := hcert _ hmem j
  rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ A)] at h
  rw [cert.block_card j]
  exact h

end RegularityLemmata
