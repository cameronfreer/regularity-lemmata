/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Tauto

/-!
# Without-replacement concentration: exact hypergeometric tail counts

The without-replacement concentration bound for equal-block sampling, in exact finite-counting
form.  For an ambient set `U`, a distinguished subset `A`, and the family of `s`-subsets `S` of
`U`, the intersection size `(A ∩ S).card` concentrates around its proportional value
`s * A.card / U.card`.  Everything is stated as pure `ℕ` counting — no probability, no
division, no real numbers.

The route is the binomial-moment (double-counting) method:

* `card_powersetCard_filter_superset` — exactly `(|U|-r).choose (s-r)` of the `s`-subsets of `U`
  contain a fixed `r`-subset;
* `sum_choose_inter_card` — the exact `r`-th binomial moment
  `∑_{|S|=s} C(|A∩S|, r) = C(|A|, r) * C(|U|-r, s-r)`, by counting pairs `R ⊆ A ∩ S` with
  `|R| = r` both ways;
* `card_filter_le_inter_card_mul_choose_le` — the upper tail: Markov at the `r`-th binomial
  moment, using only monotonicity of `Nat.choose` in its first argument;
* `card_filter_inter_card_le_mul_choose_le` — the lower tail, by complementing `A` inside `U`.

Choosing `r` of the order of the deviation makes the moment/`C(K,r)` ratio geometrically small;
that quantitative comparison is deliberately NOT made here — it belongs to the schedule layer,
where the sampling parameters are fixed.  The tails here are the `fam` inputs of
`RegularityLemmata.exists_equiv_avoids_all` after filtering `powersetCard`.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-! ### Supersets of a fixed set among `s`-subsets -/

/-- Exactly `(|U| - |R|).choose (s - |R|)` of the `s`-subsets of `U` contain a fixed subset
`R ⊆ U` (for `|R| ≤ s`; both sides vanish when `s` exceeds `|U|`). -/
theorem card_powersetCard_filter_superset (U R : Finset α) (hR : R ⊆ U) {s : ℕ}
    (hrs : R.card ≤ s) :
    ((U.powersetCard s).filter fun S ↦ R ⊆ S).card = (U.card - R.card).choose (s - R.card) := by
  have hUR : (U \ R).card = U.card - R.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR]
  rw [← hUR, ← Finset.card_powersetCard (s - R.card) (U \ R)]
  refine Finset.card_bij' (fun S _ ↦ S \ R) (fun T _ ↦ T ∪ R) ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨hSpow, hRS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.sdiff_subset_sdiff hSU Finset.Subset.rfl,
        by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRS, hScard]⟩
  · intro T hT
    obtain ⟨hTU, hTcard⟩ := Finset.mem_powersetCard.mp hT
    have hdisj : Disjoint T R := Finset.disjoint_of_subset_left hTU Finset.sdiff_disjoint
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.subset_union_right⟩
    · exact Finset.union_subset (hTU.trans (Finset.sdiff_subset)) hR
    · rw [Finset.card_union_of_disjoint hdisj, hTcard]
      omega
  · intro S hS
    exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp hS).2
  · intro T hT
    have hTU := (Finset.mem_powersetCard.mp hT).1
    exact Finset.union_sdiff_cancel_right (Finset.disjoint_of_subset_left hTU
      Finset.sdiff_disjoint)

/-! ### The exact binomial moment -/

/-- **The `r`-th binomial moment of the hypergeometric count, exactly.**  Summing
`C((A ∩ S).card, r)` over all `s`-subsets `S` of `U` counts the pairs `(R, S)` with `R ⊆ A`,
`|R| = r`, `R ⊆ S`; grouping by `R` gives `C(|A|, r) * C(|U| - r, s - r)`. -/
theorem sum_choose_inter_card (U A : Finset α) (hA : A ⊆ U) {s r : ℕ} (hrs : r ≤ s) :
    ∑ S ∈ U.powersetCard s, ((A ∩ S).card).choose r
      = A.card.choose r * (U.card - r).choose (s - r) := by
  have hterm : ∀ S, ((A ∩ S).card).choose r
      = ∑ R ∈ A.powersetCard r, if R ⊆ S then 1 else 0 := by
    intro S
    have hset : (A ∩ S).powersetCard r = (A.powersetCard r).filter fun R ↦ R ⊆ S := by
      ext R
      simp only [Finset.mem_powersetCard, Finset.subset_inter_iff, Finset.mem_filter]
      tauto
    rw [← Finset.card_powersetCard r (A ∩ S), hset, Finset.card_filter]
  calc
    ∑ S ∈ U.powersetCard s, ((A ∩ S).card).choose r
        = ∑ S ∈ U.powersetCard s, ∑ R ∈ A.powersetCard r, if R ⊆ S then 1 else 0 :=
      Finset.sum_congr rfl fun S _ ↦ hterm S
    _ = ∑ R ∈ A.powersetCard r, ∑ S ∈ U.powersetCard s, if R ⊆ S then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ R ∈ A.powersetCard r, ((U.powersetCard s).filter fun S ↦ R ⊆ S).card :=
      Finset.sum_congr rfl fun R _ ↦ (Finset.card_filter _ _).symm
    _ = ∑ R ∈ A.powersetCard r, (U.card - r).choose (s - r) := by
      refine Finset.sum_congr rfl fun R hR ↦ ?_
      obtain ⟨hRA, hRcard⟩ := Finset.mem_powersetCard.mp hR
      rw [card_powersetCard_filter_superset U R (hRA.trans hA) (hRcard ▸ hrs), hRcard]
    _ = A.card.choose r * (U.card - r).choose (s - r) := by
      rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-- The mean identity (the `r = 1` binomial moment): the total intersection mass of a subset
`A ⊆ U` over all `s`-subsets of `U` is exactly `|A| * C(|U| - 1, s - 1)`. -/
theorem sum_inter_card (U A : Finset α) (hA : A ⊆ U) {s : ℕ} (hs : 1 ≤ s) :
    ∑ S ∈ U.powersetCard s, (A ∩ S).card = A.card * (U.card - 1).choose (s - 1) := by
  have h := sum_choose_inter_card U A hA (r := 1) hs
  simpa only [Nat.choose_one_right] using h

/-! ### The upper tail -/

/-- **Upper tail (Markov at the `r`-th binomial moment).**  The number of `s`-subsets `S` of `U`
with `K ≤ (A ∩ S).card`, multiplied by `C(K, r)`, is at most the `r`-th binomial moment
`C(|A|, r) * C(|U| - r, s - r)`.  Choosing `r ≈ K - s|A|/|U|` makes the ratio geometrically
small; that comparison is left to the schedule layer. -/
theorem card_filter_le_inter_card_mul_choose_le (U A : Finset α) (hA : A ⊆ U) {s r K : ℕ}
    (hrs : r ≤ s) :
    ((U.powersetCard s).filter fun S ↦ K ≤ (A ∩ S).card).card * K.choose r
      ≤ A.card.choose r * (U.card - r).choose (s - r) := by
  calc
    ((U.powersetCard s).filter fun S ↦ K ≤ (A ∩ S).card).card * K.choose r
        = ∑ _S ∈ (U.powersetCard s).filter fun S ↦ K ≤ (A ∩ S).card, K.choose r := by
      rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ S ∈ (U.powersetCard s).filter fun S ↦ K ≤ (A ∩ S).card,
          ((A ∩ S).card).choose r :=
      Finset.sum_le_sum fun S hS ↦
        Nat.choose_le_choose r (Finset.mem_filter.mp hS).2
    _ ≤ ∑ S ∈ U.powersetCard s, ((A ∩ S).card).choose r :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = A.card.choose r * (U.card - r).choose (s - r) := sum_choose_inter_card U A hA hrs

/-! ### The lower tail, by complementation -/

/-- For `A, S ⊆ U`, the intersection masses of `A` and of `U \ A` on `S` add up to `|S|`. -/
theorem inter_card_add_compl_inter_card (U A S : Finset α) (hA : A ⊆ U) (hS : S ⊆ U) :
    (A ∩ S).card + ((U \ A) ∩ S).card = S.card := by
  have hdisj : Disjoint (A ∩ S) ((U \ A) ∩ S) :=
    Finset.disjoint_sdiff.mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.union_inter_distrib_right,
    Finset.union_sdiff_of_subset hA, Finset.inter_eq_right.mpr hS]

/-- **Lower tail.**  The number of `s`-subsets `S` of `U` with `(A ∩ S).card ≤ L`, multiplied by
`C(s - L, r)`, is at most `C(|U| - |A|, r) * C(|U| - r, s - r)`: a low intersection with `A` is
a high intersection with `U \ A`, and the upper tail applies to the complement. -/
theorem card_filter_inter_card_le_mul_choose_le (U A : Finset α) (hA : A ⊆ U) {s r L : ℕ}
    (hrs : r ≤ s) :
    ((U.powersetCard s).filter fun S ↦ (A ∩ S).card ≤ L).card * (s - L).choose r
      ≤ (U.card - A.card).choose r * (U.card - r).choose (s - r) := by
  have hsub : ((U.powersetCard s).filter fun S ↦ (A ∩ S).card ≤ L)
      ⊆ (U.powersetCard s).filter fun S ↦ s - L ≤ ((U \ A) ∩ S).card := by
    intro S hS
    obtain ⟨hSpow, hSle⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hSpow
    have hadd := inter_card_add_compl_inter_card U A S hA hSU
    exact Finset.mem_filter.mpr ⟨hSpow, by omega⟩
  calc
    ((U.powersetCard s).filter fun S ↦ (A ∩ S).card ≤ L).card * (s - L).choose r
        ≤ ((U.powersetCard s).filter fun S ↦ s - L ≤ ((U \ A) ∩ S).card).card
            * (s - L).choose r :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (U \ A).card.choose r * (U.card - r).choose (s - r) :=
      card_filter_le_inter_card_mul_choose_le U (U \ A) (Finset.sdiff_subset) hrs
    _ = (U.card - A.card).choose r * (U.card - r).choose (s - r) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA]

/-! ### Tests and adversarial examples

Exact-count sanity checks: the `r = 0` moment degenerates to the subset count, the mean
identity on a tiny instance, and both tails checked concretely by kernel `decide`. -/

-- `r = 0`: the zeroth moment is the number of `s`-subsets.
example : ∑ S ∈ (Finset.range 4).powersetCard 2, ((Finset.range 2 ∩ S).card).choose 0
    = Nat.choose 4 2 := by decide

-- The mean identity on `|U| = 4`, `|A| = 2`, `s = 2`: total mass `2 * C(3, 1) = 6`.
example : ∑ S ∈ (Finset.range 4).powersetCard 2, ((Finset.range 2 ∩ S).card) = 6 := by decide

-- Upper tail, concretely: exactly one `2`-subset of `range 4` has intersection `≥ 2` with
-- `range 2`, and the bound at `r = 2` is exact: `1 * C(2,2) = C(2,2) * C(2,0)`.
example : (((Finset.range 4).powersetCard 2).filter
    fun S ↦ 2 ≤ (Finset.range 2 ∩ S).card).card = 1 := by decide

-- Lower tail, concretely: exactly one `2`-subset has intersection `0` with `range 2`.
example : (((Finset.range 4).powersetCard 2).filter
    fun S ↦ (Finset.range 2 ∩ S).card ≤ 0).card = 1 := by decide

end RegularityLemmata
