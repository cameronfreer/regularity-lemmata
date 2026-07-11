/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Tuple
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Density on finite supports

`densityOn S p` is the fraction of elements of the finite support `S` satisfying `p`,
defined by real division so that the empty support has density `0` (`x / 0 = 0`).
Substantive identities (complement, count extraction from a density lower bound) require
explicit `Nonempty` hypotheses — the complement identity `d(p) + d(¬p) = 1` is **false**
on the empty support and is not stated without the hypothesis.

Density is *not* monotone under restricting or enlarging the support; the file provides
only the three honest monotonicity notions: predicate monotonicity on a fixed support,
count monotonicity under support inclusion, and count/density conversions.

The tuple layer specializes to boxes `Fintype.piFinset A`.
-/

namespace RegularityLemmata

variable {α β : Type*}

/-! ### Generic density -/

/-- Fraction of `S` satisfying `p`; `0` on the empty support via `x / 0 = 0`. -/
noncomputable def densityOn (S : Finset β) (p : β → Prop) [DecidablePred p] : ℝ :=
  ((S.filter p).card : ℝ) / S.card

variable {S T : Finset β} {p q : β → Prop} [DecidablePred p] [DecidablePred q] {c : ℝ}

@[simp] theorem densityOn_empty : densityOn (∅ : Finset β) p = 0 := by
  simp [densityOn]

theorem densityOn_nonneg : 0 ≤ densityOn S p := by
  unfold densityOn; positivity

theorem densityOn_le_one : densityOn S p ≤ 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · rw [densityOn, div_le_one (by exact_mod_cast S.card_pos.mpr hS)]
    exact_mod_cast Finset.card_filter_le S p

/-- Complement identity. **Requires** `S.Nonempty`: on `∅` both densities are `0`. -/
theorem densityOn_add_not (hS : S.Nonempty) :
    densityOn S p + densityOn S (fun x => ¬ p x) = 1 := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast S.card_pos.mpr hS
  rw [densityOn, densityOn, ← add_div, div_eq_one_iff_eq hcard.ne']
  exact_mod_cast S.card_filter_add_card_filter_not p

/-- Complement density. **Requires** `S.Nonempty` (false on `∅`). -/
theorem densityOn_not (hS : S.Nonempty) :
    densityOn S (fun x => ¬ p x) = 1 - densityOn S p := by
  have := densityOn_add_not (p := p) hS
  linarith

/-- Predicate monotonicity on a fixed support. (Density is NOT monotone in the
support; no such lemma is stated.) -/
theorem densityOn_mono_pred (h : ∀ x ∈ S, p x → q x) : densityOn S p ≤ densityOn S q := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have hsub : S.filter p ⊆ S.filter q := fun x hx => by
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, h x hx.1 hx.2⟩
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast S.card_pos.mpr hS
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hsub) hcard.le

/-- Count monotonicity under support inclusion (the honest form of "restriction"). -/
theorem card_filter_mono_subset (p : β → Prop) [DecidablePred p] (h : S ⊆ T) :
    (S.filter p).card ≤ (T.filter p).card :=
  Finset.card_le_card (Finset.filter_subset_filter p h)

/-- Count from a density upper bound. Holds for all `S` (on `∅` it reads `0 ≤ 0`). -/
theorem card_filter_le_of_densityOn_le (h : densityOn S p ≤ c) :
    ((S.filter p).card : ℝ) ≤ c * S.card := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast S.card_pos.mpr hS
    calc ((S.filter p).card : ℝ) = densityOn S p * S.card := by
          rw [densityOn, div_mul_cancel₀]; exact hcard.ne'
      _ ≤ c * S.card := mul_le_mul_of_nonneg_right h hcard.le

/-- Count from a density lower bound. Holds for all `S`: on `∅` the conclusion reads
`c · 0 ≤ 0`, which is true for every `c`. -/
theorem le_card_filter_of_le_densityOn (h : c ≤ densityOn S p) :
    c * S.card ≤ ((S.filter p).card : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast S.card_pos.mpr hS
    calc c * S.card ≤ densityOn S p * S.card := mul_le_mul_of_nonneg_right h hcard.le
      _ = ((S.filter p).card : ℝ) := by rw [densityOn, div_mul_cancel₀]; exact hcard.ne'

/-! ### Tuple densities over boxes -/

variable {k : ℕ} {R R' : (Fin k → α) → Prop} [DecidablePred R] [DecidablePred R']
  {A : Fin k → Finset α}

/-- Number of tuples in the box `A` satisfying `R`. -/
def tupleCount (R : (Fin k → α) → Prop) [DecidablePred R] (A : Fin k → Finset α) : ℕ :=
  ((Fintype.piFinset A).filter R).card

/-- Density of `R` on the box `A`; `0` if some coordinate set is empty. -/
noncomputable def tupleDensity (R : (Fin k → α) → Prop) [DecidablePred R]
    (A : Fin k → Finset α) : ℝ :=
  densityOn (Fintype.piFinset A) R

theorem tupleDensity_eq_count_div :
    tupleDensity R A = (tupleCount R A : ℝ) / (Fintype.piFinset A).card := rfl

theorem tupleDensity_nonneg : 0 ≤ tupleDensity R A := densityOn_nonneg

theorem tupleDensity_le_one : tupleDensity R A ≤ 1 := densityOn_le_one

/-- Complement identity on a box with all sides nonempty. -/
theorem tupleDensity_add_neg (hne : ∀ i, (A i).Nonempty) :
    tupleDensity R A + tupleDensity (fun x => ¬ R x) A = 1 :=
  densityOn_add_not (Fintype.piFinset_nonempty.mpr hne)

theorem tupleDensity_neg (hne : ∀ i, (A i).Nonempty) :
    tupleDensity (fun x => ¬ R x) A = 1 - tupleDensity R A :=
  densityOn_not (Fintype.piFinset_nonempty.mpr hne)

/-- Count from a density upper bound, `k`-ary form. Holds for all boxes. -/
theorem card_filter_le_of_tupleDensity_le {c : ℝ} (h : tupleDensity R A ≤ c) :
    (tupleCount R A : ℝ) ≤ c * ∏ i, ((A i).card : ℝ) := by
  have := card_filter_le_of_densityOn_le h
  rwa [Fintype.card_piFinset, Nat.cast_prod] at this

/-! ### `Fin 2` boxes -/

variable [DecidableEq α] {A₂ : Fin 2 → Finset α} {R₂ : (Fin 2 → α) → Prop} [DecidablePred R₂]

/-- Binary tuple density as a product-filter ratio. Holds for all boxes: with an empty
side both sides are `0` by the division convention. -/
theorem tupleDensity_two_eq :
    tupleDensity R₂ A₂ =
      (((A₂ 0 ×ˢ A₂ 1).filter fun p => R₂ ![p.1, p.2]).card : ℝ)
        / (((A₂ 0).card : ℝ) * (A₂ 1).card) := by
  rw [tupleDensity, densityOn, card_filter_piFinset_two, card_piFinset_two]
  push_cast
  rfl

/-- Count from a binary density upper bound. Holds for all boxes. -/
theorem card_filter_product_le_of_tupleDensity_le {c : ℝ} (h : tupleDensity R₂ A₂ ≤ c) :
    (((A₂ 0 ×ˢ A₂ 1).filter fun p => R₂ ![p.1, p.2]).card : ℝ)
      ≤ c * (((A₂ 0).card : ℝ) * (A₂ 1).card) := by
  have := card_filter_le_of_densityOn_le h
  rwa [card_filter_piFinset_two, card_piFinset_two, Nat.cast_mul] at this

/-- Count from a binary density lower bound. Holds for all boxes (empty sides give
`c · 0 ≤ 0`). -/
theorem le_card_filter_product_of_le_tupleDensity {c : ℝ} (h : c ≤ tupleDensity R₂ A₂) :
    c * (((A₂ 0).card : ℝ) * (A₂ 1).card)
      ≤ (((A₂ 0 ×ˢ A₂ 1).filter fun p => R₂ ![p.1, p.2]).card : ℝ) := by
  have := le_card_filter_of_le_densityOn h
  rwa [card_filter_piFinset_two, card_piFinset_two, Nat.cast_mul] at this

/-! ### Tests and adversarial examples -/

-- Diagonal count on the full `Fin 2` box over `Fin 3`: 3 of 9 tuples.
example : tupleCount (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ) = 3 := by
  decide

-- The corresponding density is 1/3.
example :
    tupleDensity (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ) = 1 / 3 := by
  rw [tupleDensity_eq_count_div,
    show tupleCount (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ) = 3 from by
      decide,
    show (Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))).card = 9 from by
      decide]
  norm_num

-- Adversarial: the empty support has density 0 …
example : densityOn (∅ : Finset (Fin 3)) (fun _ => True) = 0 := by simp

-- … and so does any box with an empty side, even for the always-true relation.
example :
    tupleDensity (fun _ : Fin 2 → Fin 3 => True) ![Finset.univ, ∅] = 0 := by
  rw [tupleDensity_two_eq]
  simp

-- NOTE (adversarial, documented): the complement identity FAILS on the empty support —
-- `densityOn ∅ p + densityOn ∅ (¬ p ·) = 0 ≠ 1` — which is why `densityOn_add_not`
-- carries `S.Nonempty`. The unguarded statement is deliberately not part of the API.
example :
    densityOn (∅ : Finset (Fin 3)) (fun _ => True)
      + densityOn (∅ : Finset (Fin 3)) (fun _ => ¬ True) = 0 := by simp

-- Count extraction, upper bound, on a concrete instance.
example :
    ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin 3 × Fin 3 => (![p.1, p.2] : Fin 2 → Fin 3) 0 = ![p.1, p.2] 1)).card = 3 := by
  decide

end RegularityLemmata
