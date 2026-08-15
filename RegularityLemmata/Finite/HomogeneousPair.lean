/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.PairDensity

/-!
# Approximate homogeneity of a rectangle

A rectangle is `ε`-**homogeneous** for `R` when its density is within `ε` of one of the two
extremes: almost no related pairs, or almost all of them. Carriers are heterogeneous
(`R : α → β → Prop`), matching `Finite/PairDensity.lean`.

The argument order is `R A B ε`, matching `IsUniformPair` rather than putting the tolerance
first — homogeneity is a property *of a rectangle*, parametrized by a tolerance.

Three symmetries hold unconditionally, including on empty rectangles: monotonicity in `ε`,
invariance under transposing to `swapRel R`, and invariance under complementing `R`. The
last is worth noting: on an empty rectangle `R` and its complement both have density `0`, so
`pairDensity_not` does not apply there — but homogeneity is nevertheless preserved, because
the two sides of the equivalence become the *same* proposition.

Restriction is where the quantitative content lives. Homogeneity degrades under passing to a
subrectangle, by the **inverse relative masses of the two sides separately**: an
exceptional set of density `ε` can concentrate into a subrectangle occupying a `ρA · ρB`
fraction. The exact-homogeneity case `ε = 0` degrades not at all, and is stated separately.

This file imports only `PairDensity`. There is deliberately no partition-level predicate
here: importing `Finpartition` into the finite layer would invert the library's dependency
direction. A `AreHomogeneousPartitions` living above both layers is the right home for that,
if a consumer needs it.
-/

namespace RegularityLemmata

variable {α β : Type*} {R : α → β → Prop} [DecidableRel R]
variable {A A' : Finset α} {B B' : Finset β} {ε ε' : ℝ}

/-- The rectangle `A ×ˢ B` is `ε`-homogeneous for `R`: its density is within `ε` of `0` or
of `1`. -/
def IsHomogeneousPair (R : α → β → Prop) [DecidableRel R] (A : Finset α) (B : Finset β)
    (ε : ℝ) : Prop :=
  pairDensity R A B ≤ ε ∨ 1 - ε ≤ pairDensity R A B

/-! ### Unconditional symmetries -/

theorem IsHomogeneousPair.mono (h : IsHomogeneousPair R A B ε) (hε : ε ≤ ε') :
    IsHomogeneousPair R A B ε' := by
  rcases h with h | h
  · exact Or.inl (h.trans hε)
  · exact Or.inr (by linarith)

/-- Transposing swaps the carriers and preserves homogeneity. -/
theorem isHomogeneousPair_swapRel_iff :
    IsHomogeneousPair (swapRel R) B A ε ↔ IsHomogeneousPair R A B ε := by
  rw [IsHomogeneousPair, IsHomogeneousPair, pairDensity_swapRel]

/-- Complementing the relation preserves homogeneity — **including on empty rectangles**,
where `pairDensity_not` is unavailable because both densities are `0`. There the two sides
are literally the same proposition; on a nonempty rectangle they exchange the two
disjuncts. -/
theorem isHomogeneousPair_not_iff :
    IsHomogeneousPair (fun a b => ¬ R a b) A B ε ↔ IsHomogeneousPair R A B ε := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    rw [IsHomogeneousPair, IsHomogeneousPair, pairDensity_empty_left,
      pairDensity_empty_left]
  · rcases B.eq_empty_or_nonempty with hB | hB
    · subst hB
      rw [IsHomogeneousPair, IsHomogeneousPair, pairDensity_empty_right,
        pairDensity_empty_right]
    · rw [IsHomogeneousPair, IsHomogeneousPair, pairDensity_not hA hB]
      constructor
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)

/-! ### Restriction -/

/-- The shared estimate behind both branches of `IsHomogeneousPair.restrict`: a raw-mass
bound on a relation over `A ×ˢ B` descends to a density bound on a subrectangle, degraded by
the two sides' inverse relative masses.

Guard-free in the subrectangle: if `A'` or `B'` is empty the density is `0`, which is below
the (nonnegative) right-hand side. -/
theorem pairDensity_restrict_le {S : α → β → Prop} [DecidableRel S] {c ρA ρB : ℝ}
    (hc : 0 ≤ c) (hρA : 0 < ρA) (hρB : 0 < ρB) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hAc : ρA * (A.card : ℝ) ≤ (A'.card : ℝ)) (hBc : ρB * (B.card : ℝ) ≤ (B'.card : ℝ))
    (hS : (pairCount S A B : ℝ) ≤ c * (A.card : ℝ) * B.card) :
    pairDensity S A' B' ≤ c / (ρA * ρB) := by
  have hρ : (0 : ℝ) < ρA * ρB := mul_pos hρA hρB
  have hmass' : (0 : ℝ) ≤ (A'.card : ℝ) * B'.card := by positivity
  rcases eq_or_lt_of_le hmass' with hzero | hpos
  · rw [pairDensity_eq_count_div, ← hzero, div_zero]
    positivity
  · -- The subrectangle is realized, so both sides of the ambient rectangle are too.
    have hAp : (0 : ℝ) < (A'.card : ℝ) := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) A'.card) with h | h
      · exfalso; rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
      · exact h
    have hBp : (0 : ℝ) < (B'.card : ℝ) := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) B'.card) with h | h
      · exfalso; rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
      · exact h
    have hcount : (pairCount S A' B' : ℝ) ≤ c * (A.card : ℝ) * B.card :=
      le_trans (Nat.cast_le.mpr (pairCount_mono hA hB)) hS
    -- `ρAρB·|A||B| ≤ |A'||B'|`, so the ambient mass is controlled by the shrunken one.
    have hAn : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    have hBn : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    have hprod : (ρA * ρB) * ((A.card : ℝ) * B.card) ≤ (A'.card : ℝ) * B'.card := by
      calc (ρA * ρB) * ((A.card : ℝ) * B.card)
          = (ρA * (A.card : ℝ)) * (ρB * (B.card : ℝ)) := by ring
        _ ≤ (A'.card : ℝ) * (B'.card : ℝ) :=
            mul_le_mul hAc hBc (by positivity) (le_of_lt hAp)
    rw [pairDensity_eq_count_div, div_le_div_iff₀ hpos hρ]
    calc (pairCount S A' B' : ℝ) * (ρA * ρB)
        ≤ (c * (A.card : ℝ) * B.card) * (ρA * ρB) :=
          mul_le_mul_of_nonneg_right hcount hρ.le
      _ = c * ((ρA * ρB) * ((A.card : ℝ) * B.card)) := by ring
      _ ≤ c * ((A'.card : ℝ) * B'.card) := mul_le_mul_of_nonneg_left hprod hc

/-- **Exact homogeneity is closed under subrectangles.** At `ε = 0` there is no degradation:
a rectangle with no related pairs, or with every pair related, keeps that property on every
subrectangle. (An empty subrectangle lands in the first disjunct, since its density is `0`.)
-/
theorem IsHomogeneousPair.subset_zero (h : IsHomogeneousPair R A B 0)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : IsHomogeneousPair R A' B' 0 := by
  have hmass : (0 : ℝ) ≤ (A.card : ℝ) * B.card := by positivity
  rcases h with h | h
  · -- No related pairs upstairs, hence none downstairs.
    left
    have hzero : (pairCount R A B : ℝ) ≤ 0 := by
      rw [pairCount_eq_pairDensity_mul]
      exact mul_nonpos_of_nonpos_of_nonneg h hmass
    have hzero' : pairCount R A B = 0 := by
      have := Nat.cast_nonneg (α := ℝ) (pairCount R A B)
      exact_mod_cast le_antisymm hzero this
    have : pairCount R A' B' = 0 :=
      Nat.le_zero.mp (hzero' ▸ pairCount_mono hA hB)
    rw [pairDensity_eq_count_div, this]
    simp
  · -- Every pair related upstairs, so the complement is empty downstairs too.
    rw [sub_zero] at h
    have hall : (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) := by
      rw [pairCount_eq_pairDensity_mul]
      nlinarith [pairDensity_le_one (R := R) (A := A) (B := B)]
    have hnot : pairCount (fun a b => ¬ R a b) A B = 0 := by
      have hsum := pairCount_add_not (R := R) (A := A) (B := B)
      have hle : (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) := hall
      have : pairCount R A B = A.card * B.card := by
        have h1 : pairCount R A B ≤ A.card * B.card := by omega
        have h2 : A.card * B.card ≤ pairCount R A B := by exact_mod_cast hle
        omega
      omega
    have hnot' : pairCount (fun a b => ¬ R a b) A' B' = 0 :=
      Nat.le_zero.mp (hnot ▸ pairCount_mono (R := fun a b => ¬ R a b) hA hB)
    rcases A'.eq_empty_or_nonempty with hAe | hAe
    · left; rw [hAe, pairDensity_empty_left]
    rcases B'.eq_empty_or_nonempty with hBe | hBe
    · left; rw [hBe, pairDensity_empty_right]
    right
    rw [sub_zero]
    have hd : pairDensity (fun a b => ¬ R a b) A' B' = 0 := by
      rw [pairDensity_eq_count_div, hnot']
      simp
    rw [pairDensity_not hAe hBe] at hd
    linarith

/-- **Quantitative restriction.** Homogeneity passes to a subrectangle occupying at least a
`ρA` fraction of the left side and a `ρB` fraction of the right, with the tolerance degraded
by `ρA · ρB` — the exceptional mass can concentrate by the inverse relative rectangle mass.

The two proportions are tracked **separately** rather than as a single rectangle fraction,
because a consumer that shrinks only one side should pay only that side's factor. -/
theorem IsHomogeneousPair.restrict {ρA ρB : ℝ} (h : IsHomogeneousPair R A B ε)
    (hε : 0 ≤ ε) (hρA : 0 < ρA) (hρB : 0 < ρB) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hAc : ρA * (A.card : ℝ) ≤ (A'.card : ℝ)) (hBc : ρB * (B.card : ℝ) ≤ (B'.card : ℝ)) :
    IsHomogeneousPair R A' B' (ε / (ρA * ρB)) := by
  rcases h with h | h
  · left
    exact pairDensity_restrict_le hε hρA hρB hA hB hAc hBc
      (pairCount_le_of_pairDensity_le h)
  · -- Sparse complement upstairs: bound its count, restrict, then convert back.
    have hnotcount : (pairCount (fun a b => ¬ R a b) A B : ℝ)
        ≤ ε * (A.card : ℝ) * B.card := by
      have hsum := pairCount_add_not (R := R) (A := A) (B := B)
      have hR : (1 - ε) * (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) :=
        le_pairCount_of_le_pairDensity h
      have hcast : (pairCount R A B : ℝ) + (pairCount (fun a b => ¬ R a b) A B : ℝ)
          = (A.card : ℝ) * B.card := by exact_mod_cast congrArg (Nat.cast (R := ℝ)) hsum
      nlinarith [hR, hcast]
    have hnotd : pairDensity (fun a b => ¬ R a b) A' B' ≤ ε / (ρA * ρB) :=
      pairDensity_restrict_le hε hρA hρB hA hB hAc hBc hnotcount
    rcases A'.eq_empty_or_nonempty with hAe | hAe
    · left
      rw [hAe, pairDensity_empty_left]
      positivity
    rcases B'.eq_empty_or_nonempty with hBe | hBe
    · left
      rw [hBe, pairDensity_empty_right]
      positivity
    right
    rw [pairDensity_not hAe hBe] at hnotd
    linarith

/-! ### Tests and adversarial examples -/

section Tests

-- `a ≤ b` on `Fin 2 → Fin 3` has density `5/6`, so it is `1/6`-homogeneous (dense side) and
-- not `1/12`-homogeneous.
example : IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
    Finset.univ Finset.univ (1 / 6) := by
  right
  rw [show pairDensity (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
      Finset.univ Finset.univ = 5 / 6 from by
    rw [pairDensity_eq_count_div,
      show pairCount (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
        Finset.univ Finset.univ = 5 from by decide]
    simp
    norm_num]
  norm_num

-- **Exact homogeneity, subset closure**, at genuinely rectangular carriers: the empty
-- relation is `0`-homogeneous and stays so on every subrectangle.
example (A' : Finset (Fin 2)) (B' : Finset (Fin 3)) :
    IsHomogeneousPair (fun (_ : Fin 2) (_ : Fin 3) => False) A' B' 0 :=
  IsHomogeneousPair.subset_zero
    (A := Finset.univ) (B := Finset.univ)
    (Or.inl (by rw [pairDensity_eq_count_div, show
      pairCount (fun (_ : Fin 2) (_ : Fin 3) => False) Finset.univ Finset.univ = 0 from by
        decide]; simp))
    (Finset.subset_univ _) (Finset.subset_univ _)

-- **A concrete quantitative restriction**: halving each side degrades the tolerance by 4.
example (h : IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
      Finset.univ Finset.univ (1 / 6))
    {A' : Finset (Fin 2)} {B' : Finset (Fin 3)}
    (hA : A' ⊆ Finset.univ) (hB : B' ⊆ Finset.univ)
    (hAc : (1 / 2 : ℝ) * (Finset.univ : Finset (Fin 2)).card ≤ (A'.card : ℝ))
    (hBc : (1 / 2 : ℝ) * (Finset.univ : Finset (Fin 3)).card ≤ (B'.card : ℝ)) :
    IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val) A' B'
      ((1 / 6) / ((1 / 2 : ℝ) * (1 / 2 : ℝ))) :=
  h.restrict (by norm_num) (by norm_num) (by norm_num) hA hB hAc hBc

-- The transpose and complement symmetries, at rectangular carriers.
example (A : Finset (Fin 2)) (B : Finset (Fin 3)) (ε : ℝ) :
    IsHomogeneousPair (swapRel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)) B A ε
      ↔ IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val) A B ε :=
  isHomogeneousPair_swapRel_iff

-- Complement invariance survives the empty rectangle, where `pairDensity_not` does not
-- apply because both densities are `0`.
example (B : Finset (Fin 3)) (ε : ℝ) :
    IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => ¬ (a.val ≤ b.val)) ∅ B ε
      ↔ IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val) ∅ B ε :=
  isHomogeneousPair_not_iff

end Tests

end RegularityLemmata
