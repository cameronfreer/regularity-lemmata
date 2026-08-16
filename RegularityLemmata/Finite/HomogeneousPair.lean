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

**The predicate is instance-free.** `IsHomogeneousPair` elaborates for an arbitrary
`R : α → β → Prop` with no decidability, `DecidableEq`, or `Fintype` assumptions: the
decidability instance that `pairDensity` requires is supplied classically *inside* the
definition. Any ambient instance gives the same proposition — that is `isHomogeneousPair_def`,
which is also the interface every proof below uses (no proof unfolds the classical instance
directly). The zero-instance test at the end of the file pins this contract.

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

variable {α β : Type*} {R : α → β → Prop}
variable {A A' : Finset α} {B B' : Finset β} {ε ε' : ℝ}

/-- The rectangle `A ×ˢ B` is `ε`-homogeneous for `R`: its density is within `ε` of `0` or
of `1`. Instance-free: the decidability that `pairDensity` needs is supplied classically
inside; read the definition through `isHomogeneousPair_def` under any ambient instance. -/
def IsHomogeneousPair (R : α → β → Prop) (A : Finset α) (B : Finset β) (ε : ℝ) : Prop :=
  letI : DecidableRel R := fun a b => Classical.dec (R a b)
  pairDensity R A B ≤ ε ∨ 1 - ε ≤ pairDensity R A B

/-- The definitional reading, valid over **any** ambient decidability instance: the
classical instance inside `IsHomogeneousPair` is propositionally irrelevant. -/
theorem isHomogeneousPair_def [inst : DecidableRel R] :
    IsHomogeneousPair R A B ε ↔ pairDensity R A B ≤ ε ∨ 1 - ε ≤ pairDensity R A B := by
  unfold IsHomogeneousPair
  rw [show (fun a b => Classical.dec (R a b) : DecidableRel R) = inst from
    funext fun a => funext fun b => Subsingleton.elim _ _]

/-! ### Unconditional symmetries -/

theorem IsHomogeneousPair.mono (h : IsHomogeneousPair R A B ε) (hε : ε ≤ ε') :
    IsHomogeneousPair R A B ε' := by
  classical
  rw [isHomogeneousPair_def] at h ⊢
  rcases h with h | h
  · exact Or.inl (h.trans hε)
  · exact Or.inr (by linarith)

/-- Transposing swaps the carriers and preserves homogeneity. -/
theorem isHomogeneousPair_swapRel_iff :
    IsHomogeneousPair (swapRel R) B A ε ↔ IsHomogeneousPair R A B ε := by
  classical
  rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_swapRel]

/-- Complementing the relation preserves homogeneity — **including on empty rectangles**,
where `pairDensity_not` is unavailable because both densities are `0`. There the two sides
are literally the same proposition; on a nonempty rectangle they exchange the two
disjuncts. -/
theorem isHomogeneousPair_not_iff :
    IsHomogeneousPair (fun a b => ¬ R a b) A B ε ↔ IsHomogeneousPair R A B ε := by
  classical
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_empty_left,
      pairDensity_empty_left]
  · rcases B.eq_empty_or_nonempty with hB | hB
    · subst hB
      rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_empty_right,
        pairDensity_empty_right]
    · rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_not hA hB]
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
  classical
  rw [isHomogeneousPair_def] at h ⊢
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
  classical
  rw [isHomogeneousPair_def] at h ⊢
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

/-! ### Perturbation -/

/-- Homogeneity is stable under density perturbation: if two rectangles have densities within
`γ`, homogeneity of one at `ε` gives homogeneity of the other at `ε + γ`. -/
theorem IsHomogeneousPair.of_abs_pairDensity_sub_le [DecidableRel R] {γ : ℝ}
    (h : IsHomogeneousPair R A' B' ε)
    (hclose : |pairDensity R A B - pairDensity R A' B'| ≤ γ) :
    IsHomogeneousPair R A B (ε + γ) := by
  rw [isHomogeneousPair_def] at h ⊢
  rw [abs_le] at hclose
  rcases h with h | h
  · exact Or.inl (by linarith [hclose.2])
  · exact Or.inr (by linarith [hclose.1])

/-- Division form of the sub-rectangle comparison: growing each side by at most one element
moves the density by at most `2 * (s + 1) / s ^ 2` when the smaller rectangle has both sides of
size at least `s`. This is the exact cost of absorbing one leftover element per block. -/
theorem abs_pairDensity_sub_le_of_grow_one [DecidableRel R] [DecidableEq α] [DecidableEq β]
    {s : ℕ} (hs : 0 < s)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hA'c : s ≤ A'.card) (hB'c : s ≤ B'.card)
    (hAc : A.card ≤ A'.card + 1) (hBc : B.card ≤ B'.card + 1) :
    |pairDensity R A B - pairDensity R A' B'| ≤ 2 * ((s : ℝ) + 1) / s ^ 2 := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have haR : (s : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast hA'c
  have hbR : (s : ℝ) ≤ (B'.card : ℝ) := by exact_mod_cast hB'c
  have hap : (0 : ℝ) < (A'.card : ℝ) := hsR.trans_le haR
  have hbp : (0 : ℝ) < (B'.card : ℝ) := hsR.trans_le hbR
  have hmass : (0 : ℝ) < (A'.card : ℝ) * (B'.card : ℝ) := mul_pos hap hbp
  have hdA : ((A \ A').card : ℝ) ≤ 1 := by
    have h1 : (A \ A').card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hA]
      omega
    exact_mod_cast h1
  have hdB : ((B \ B').card : ℝ) ≤ 1 := by
    have h1 : (B \ B').card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hB]
      omega
    exact_mod_cast h1
  have hAcR : (A.card : ℝ) ≤ (A'.card : ℝ) + 1 := by exact_mod_cast hAc
  have hBcR : (B.card : ℝ) ≤ (B'.card : ℝ) + 1 := by exact_mod_cast hBc
  -- Each discarded strip has mass at most one full row or column of the small rectangle.
  have hstripA : ((A \ A').card : ℝ) * (B.card : ℝ) ≤ (B'.card : ℝ) + 1 :=
    calc ((A \ A').card : ℝ) * (B.card : ℝ)
        ≤ 1 * ((B'.card : ℝ) + 1) := mul_le_mul hdA hBcR (Nat.cast_nonneg _) zero_le_one
      _ = (B'.card : ℝ) + 1 := one_mul _
  have hstripB : (A.card : ℝ) * ((B \ B').card : ℝ) ≤ (A'.card : ℝ) + 1 :=
    calc (A.card : ℝ) * ((B \ B').card : ℝ)
        ≤ ((A'.card : ℝ) + 1) * 1 := mul_le_mul hAcR hdB (Nat.cast_nonneg _) (by positivity)
      _ = (A'.card : ℝ) + 1 := mul_one _
  -- Divide the multiplication-form comparison by the small rectangle's mass.
  have hstep : |pairDensity R A' B' - pairDensity R A B|
      ≤ ((A'.card : ℝ) + (B'.card : ℝ) + 2) / ((A'.card : ℝ) * (B'.card : ℝ)) := by
    rw [le_div_iff₀ hmass]
    calc |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
        ≤ ((A \ A').card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B \ B').card : ℝ) :=
          abs_pairDensity_sub_mul_le hA hB
      _ ≤ (A'.card : ℝ) + (B'.card : ℝ) + 2 := by linarith
  -- Worsen the bound to depend only on `s`: both sides are at least `s`.
  have hdiv : ((A'.card : ℝ) + (B'.card : ℝ) + 2) / ((A'.card : ℝ) * (B'.card : ℝ))
      ≤ 2 * ((s : ℝ) + 1) / (s : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hmass (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hsR.le hap.le) (sub_nonneg.mpr hbR),
      mul_nonneg (mul_nonneg hsR.le hbp.le) (sub_nonneg.mpr haR),
      mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hbR),
      mul_nonneg hsR.le (sub_nonneg.mpr haR), mul_nonneg hsR.le (sub_nonneg.mpr hbR)]
  calc |pairDensity R A B - pairDensity R A' B'|
      = |pairDensity R A' B' - pairDensity R A B| := abs_sub_comm _ _
    _ ≤ 2 * ((s : ℝ) + 1) / (s : ℝ) ^ 2 := hstep.trans hdiv

/-! ### Tests and adversarial examples -/

section Tests

-- **Zero-instance smoke test**: the public statement elaborates for an arbitrary relation
-- with no `Fintype`, `DecidableEq`, or decidability assumptions whatsoever. This example is
-- the frozen contract; do not add instances to make a change to the definition compile.
example {X Y : Type*} (R : X → Y → Prop) (ε : ℝ) (A : Finset X) (B : Finset Y) : Prop :=
  IsHomogeneousPair R A B ε

-- `a ≤ b` on `Fin 2 → Fin 3` has density `5/6`, so it is `1/6`-homogeneous (dense side) and
-- not `1/12`-homogeneous.
example : IsHomogeneousPair (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
    Finset.univ Finset.univ (1 / 6) := by
  rw [isHomogeneousPair_def]
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
    (isHomogeneousPair_def.mpr (Or.inl (by
      rw [pairDensity_eq_count_div, show
        pairCount (fun (_ : Fin 2) (_ : Fin 3) => False) Finset.univ Finset.univ = 0 from by
          decide]
      simp)))
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

-- Density perturbation at `γ = 0` transfers homogeneity between rectangles of literally
-- equal density; the tolerance picks up only a harmless `+ 0`.
example [DecidableRel R] (h : IsHomogeneousPair R A' B' ε)
    (hEq : pairDensity R A B = pairDensity R A' B') :
    IsHomogeneousPair R A B (ε + 0) :=
  h.of_abs_pairDensity_sub_le (by simp [hEq])

-- NOTE (adversarial, documented): at `s = 1` the growth bound is `2 * 2 / 1 = 4` — vacuously
-- large, since two densities can differ by at most `1`. The theorem must nevertheless apply
-- at this extreme; only from `s = 3` on does the bound `2 * (s + 1) / s ^ 2` dip below `1`.
example :
    |pairDensity (fun (a b : Fin 2) => a = b) Finset.univ Finset.univ
        - pairDensity (fun (a b : Fin 2) => a = b) {0} {0}|
      ≤ 2 * ((1 : ℝ) + 1) / 1 ^ 2 := by
  exact_mod_cast abs_pairDensity_sub_le_of_grow_one (R := fun (a b : Fin 2) => a = b) (s := 1)
    (A' := ({0} : Finset (Fin 2))) (B' := ({0} : Finset (Fin 2))) one_pos
    (Finset.subset_univ _) (Finset.subset_univ _)
    (by decide) (by decide) (by decide) (by decide)

end Tests

end RegularityLemmata
