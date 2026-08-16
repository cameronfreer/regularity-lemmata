/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fintype.BigOperators
import RegularityLemmata.Partition.EqualBlockEncoding
import RegularityLemmata.Partition.HypergeometricTail

/-!
# Simultaneous equal-block sampling

The composition of the equal-block sampling infrastructure: one equivalence `e : Fin n ≃ α`
whose equal blocks split EVERY member of a finite set family within prescribed windows,
simultaneously across all blocks.

This module is deliberately CONDITIONAL: the hypothesis is the exact counting inequality
`m * ∑_{A ∈ F} (#upper-violations + #lower-violations) < C(n, s)`, whose discharge — choosing
the binomial-moment order `r` in the tails of `HypergeometricTail` and comparing against the
size of the trace family (the family of test sets) — belongs to the schedule layer, where the
accuracy, the block count, and the host floor are fixed.  Keeping the composition conditional
makes it reusable for any window shape (one-sided, two-sided, asymmetric).

The proof is pure plumbing: index the bad events by (member, block, side), observe that the
violation families do not depend on the block, and feed the total into
`RegularityLemmata.exists_equiv_avoids_all`.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `s`-subsets violating the upper window `hi` for `A`. -/
def upperViolations (A : Finset α) (s hi : ℕ) : Finset (Finset α) :=
  ((Finset.univ : Finset α).powersetCard s).filter fun S ↦ hi < (A ∩ S).card

/-- The `s`-subsets violating the lower window `lo` for `A`. -/
def lowerViolations (A : Finset α) (s lo : ℕ) : Finset (Finset α) :=
  ((Finset.univ : Finset α).powersetCard s).filter fun S ↦ (A ∩ S).card < lo

/-- **Simultaneous equal-block sampling, conditional form.**  If the total violation count,
over all members of `F` and both window sides, multiplied by the block count `m`, is strictly
below `C(n, s)`, then some equivalence `e : Fin n ≃ α` splits every `A ∈ F` within its window
`[lo A, hi A]` on every one of the `m` equal blocks simultaneously. -/
theorem exists_equiv_forall_blocks_window {n s m : ℕ}
    (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (lo hi : Finset α → ℕ)
    (hsum : m * ∑ A ∈ F,
        ((upperViolations A s (hi A)).card + (lowerViolations A s (lo A)).card)
      < n.choose s) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      lo A ≤ (A ∩ sampleBlock e s j).card ∧ (A ∩ sampleBlock e s j).card ≤ hi A := by
  classical
  have hs : s ≤ n := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.zero_mul] at hnm
      subst hnm
      cases s with
      | zero => exact le_rfl
      | succ t =>
        rw [Nat.choose_zero_succ] at hsum
        omega
    · calc s = 1 * s := (one_mul s).symm
        _ ≤ m * s := Nat.mul_le_mul_right s hm
        _ = n := hnm.symm
  -- Bad events: (member, block, side).
  set I := {A // A ∈ F} × Fin m × Bool with hI
  set fam : I → Finset (Finset α) := fun i ↦
    Bool.rec (lowerViolations i.1.1 s (lo i.1.1)) (upperViolations i.1.1 s (hi i.1.1)) i.2.2
    with hfamdef
  have hblk : ∀ i : I, ((i.2.1 : ℕ) + 1) * s ≤ n := by
    intro i
    calc ((i.2.1 : ℕ) + 1) * s ≤ m * s := Nat.mul_le_mul_right s i.2.1.isLt
      _ = n := hnm.symm
  have hfam : ∀ i : I, ∀ S ∈ fam i, S.card = s := by
    rintro ⟨A, j, b⟩ S hS
    have hpow : S ∈ ((Finset.univ : Finset α).powersetCard s) := by
      cases b
      · exact (Finset.mem_filter.mp hS).1
      · exact (Finset.mem_filter.mp hS).1
    exact (Finset.mem_powersetCard.mp hpow).2
  have htotal : ∑ i : I, (fam i).card < n.choose s := by
    calc
      ∑ i : I, (fam i).card
          = ∑ A : {A // A ∈ F}, ∑ j : Fin m, ∑ b : Bool, (fam (A, j, b)).card := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun A _ ↦ Fintype.sum_prod_type _
      _ = ∑ A : {A // A ∈ F},
            m * ((upperViolations A.1 s (hi A.1)).card
              + (lowerViolations A.1 s (lo A.1)).card) := by
        refine Finset.sum_congr rfl fun A _ ↦ ?_
        have hb : ∀ j : Fin m, ∑ b : Bool, (fam (A, j, b)).card
            = (upperViolations A.1 s (hi A.1)).card
              + (lowerViolations A.1 s (lo A.1)).card := by
          intro j
          rw [Fintype.sum_bool]
        rw [Finset.sum_congr rfl fun j _ ↦ hb j, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      _ = m * ∑ A ∈ F,
            ((upperViolations A s (hi A)).card + (lowerViolations A s (lo A)).card) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort F
          (fun A ↦ (upperViolations A s (hi A)).card + (lowerViolations A s (lo A)).card)
      _ < n.choose s := hsum
  obtain ⟨e, he⟩ := exists_equiv_avoids_all hn hs (fun i : I ↦ (i.2.1 : ℕ)) fam hblk hfam htotal
  refine ⟨e, fun A hA j hj ↦ ?_⟩
  have hjs : (j + 1) * s ≤ n := by
    calc (j + 1) * s ≤ m * s := Nat.mul_le_mul_right s hj
      _ = n := hnm.symm
  have hSmem : sampleBlock e s j ∈ ((Finset.univ : Finset α).powersetCard s) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, card_sampleBlock e hjs⟩
  constructor
  · have hnotlow := he (⟨A, hA⟩, ⟨j, hj⟩, false)
    by_contra hlt
    push Not at hlt
    exact hnotlow (Finset.mem_filter.mpr ⟨hSmem, hlt⟩)
  · have hnothigh := he (⟨A, hA⟩, ⟨j, hj⟩, true)
    by_contra hlt
    push Not at hlt
    exact hnothigh (Finset.mem_filter.mpr ⟨hSmem, hlt⟩)

end RegularityLemmata
