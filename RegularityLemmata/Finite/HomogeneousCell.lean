/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.HomogeneousPair
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Approximate homogeneity of a cell

A **cell** is a box `Fintype.piFinset A` for `A : ι → Finset α` over an arbitrary finite index
type `ι`. It is `ε`-homogeneous for `R` when its tuple density is within `ε` of one of the two
extremes: almost no related tuples, or almost all of them. This is the `n`-ary analogue of
`RegularityLemmata.Finite.HomogeneousPair`, and the arity is deliberately *not* fixed at two.

The argument order is `R A ε`, matching `IsHomogeneousPair`: homogeneity is a property *of a
cell*, parametrized by a tolerance.

**The predicate is instance-free in the relation and in the carrier.** `IsHomogeneousCell`
elaborates for an arbitrary `R : (ι → α) → Prop` with no decidability, `DecidableEq α`, or
`Fintype α` assumptions, and it does not even need `DecidableEq ι`: both instances that
`tupleDensity` requires are supplied classically *inside* the definition. `[Fintype ι]` is the
one hypothesis that survives, and it is structural — there is no box over an infinite index.
Any ambient instances give the same proposition; that is `isHomogeneousCell_def`, which is the
interface every proof below uses (no proof unfolds the classical instances directly). The
zero-instance test at the end of the file pins this contract.

## Frozen conventions

* **Empty side.** A box with an empty coordinate set is the empty box, whose density is `0` by
  `densityOn`'s `x / 0 = 0`. Such a cell is therefore `ε`-homogeneous for every `ε ≥ 0`, via
  the *sparse* disjunct — never the dense one (unless `ε ≥ 1`). This is why every restriction
  lemma below is guard-free downstairs but has to case on emptiness in its dense branch.
* **Empty index.** Over an empty index type the box is the singleton containing the empty
  tuple, so density is `0` or `1` and every cell is `0`-homogeneous. The `n`-box perturbation
  bound degenerates to `0 * γ = 0`, correctly: there is nothing to perturb.
* **Degenerate tolerance.** No sign condition is imposed on `ε` in the definition. At `ε < 0`
  the predicate is simply strong; the lemmas that need `0 ≤ ε` say so.

## Not claimed

* No partition-level predicate. Importing `Finpartition` into the finite layer would invert
  the library's dependency direction, exactly as recorded in `HomogeneousPair`.
* No monotonicity of `tupleDensity` under box inclusion — it is false, and only the *count* is
  monotone (`tupleCount_mono`).
* The `n = 2` growth transfer `IsHomogeneousPair.transfer_of_grow`, which lives above this
  layer, is **not** restated here and **not** migrated: only the density-level perturbation
  bound is generalized.

## Placement of the `n`-box perturbation bound

`abs_tupleDensity_sub_le_of_grow` and its telescoping ingredient live in this file rather than
in `Finite/Density.lean` or `Finite/HomogeneousPair.lean`. Imports stay honest either way — the
bound needs nothing beyond `Density` — but its only consumer is
`IsHomogeneousCell.of_abs_tupleDensity_sub_le` directly below it, and `HomogeneousPair.lean` is
about `pairDensity`, a different (heterogeneous, two-carrier) object that the `n`-ary bound
does not specialize to on the nose.
-/

namespace RegularityLemmata

variable {α : Type*} {ι : Type*} [Fintype ι]
variable {R : (ι → α) → Prop} {A A' : ι → Finset α} {ε ε' : ℝ}

/-- The cell `Fintype.piFinset A` is `ε`-homogeneous for `R`: its tuple density is within `ε`
of `0` or of `1`. Instance-free in `R`, in `α`, and in the decidable equality of `ι`: the
instances `tupleDensity` needs are supplied classically inside. Read the definition through
`isHomogeneousCell_def` under any ambient instances. -/
def IsHomogeneousCell (R : (ι → α) → Prop) (A : ι → Finset α) (ε : ℝ) : Prop :=
  letI : DecidableEq ι := fun i j ↦ Classical.dec (i = j)
  letI : DecidablePred R := fun x ↦ Classical.dec (R x)
  tupleDensity R A ≤ ε ∨ 1 - ε ≤ tupleDensity R A

/-- The definitional reading, valid over **any** ambient instances: the classical instances
inside `IsHomogeneousCell` are propositionally irrelevant. -/
theorem isHomogeneousCell_def [instι : DecidableEq ι] [instR : DecidablePred R] :
    IsHomogeneousCell R A ε ↔ tupleDensity R A ≤ ε ∨ 1 - ε ≤ tupleDensity R A := by
  unfold IsHomogeneousCell
  rw [show (fun i j ↦ Classical.dec (i = j) : DecidableEq ι) = instι from
      funext fun i ↦ funext fun j ↦ Subsingleton.elim _ _,
    show (fun x ↦ Classical.dec (R x) : DecidablePred R) = instR from
      funext fun x ↦ Subsingleton.elim _ _]

/-! ### Monotonicity in the tolerance -/

/-- Homogeneity only weakens as the tolerance grows. -/
theorem IsHomogeneousCell.mono (h : IsHomogeneousCell R A ε) (hε : ε ≤ ε') :
    IsHomogeneousCell R A ε' := by
  classical
  rw [isHomogeneousCell_def] at h ⊢
  rcases h with h | h
  · exact Or.inl (h.trans hε)
  · exact Or.inr (by linarith)

/-- An empty coordinate set makes the cell sparse, hence `ε`-homogeneous for every `ε ≥ 0`.
This is the empty-box convention, stated so that consumers do not re-derive it. -/
theorem isHomogeneousCell_of_side_empty [DecidableEq ι] {i : ι} (hi : A i = ∅) (hε : 0 ≤ ε) :
    IsHomogeneousCell R A ε := by
  classical
  rw [isHomogeneousCell_def]
  exact Or.inl (by rw [tupleDensity_eq_zero_of_side_empty (R := R) hi]; exact hε)

/-! ### The `ι = Fin 2` bridge

The binary case of a cell is a rectangle, and the two predicates agree on the nose once the
`Fin 2`-tuple relation is curried. Carriers here are homogeneous (`α` on both sides), which is
the shape a `Fin 2`-indexed box forces; `IsHomogeneousPair` is stated for genuinely
heterogeneous carriers and is strictly more general in that direction. -/

/-- A `Fin 2` tuple density is the pair density of the curried relation. -/
theorem tupleDensity_eq_pairDensity [DecidableEq α] (R₂ : (Fin 2 → α) → Prop)
    [DecidablePred R₂] (A₂ : Fin 2 → Finset α) :
    tupleDensity R₂ A₂ = pairDensity (fun a b ↦ R₂ ![a, b]) (A₂ 0) (A₂ 1) := by
  rw [tupleDensity_two_eq, pairDensity_eq_count_div, pairCount]

/-- **The binary bridge**: a `Fin 2`-indexed cell is homogeneous exactly when the corresponding
rectangle is. -/
theorem isHomogeneousCell_two_iff [DecidableEq α] {R₂ : (Fin 2 → α) → Prop}
    {A₂ : Fin 2 → Finset α} :
    IsHomogeneousCell R₂ A₂ ε ↔ IsHomogeneousPair (fun a b ↦ R₂ ![a, b]) (A₂ 0) (A₂ 1) ε := by
  classical
  rw [isHomogeneousCell_def, isHomogeneousPair_def, tupleDensity_eq_pairDensity]

/-! ### Exact homogeneity is closed under subcells -/

/-- **Exact homogeneity is closed under passing to a subcell.** At `ε = 0` there is no
degradation: a cell with no related tuples, or with every tuple related, keeps that property on
every subcell. (An empty subcell lands in the first disjunct, since its density is `0`.) -/
theorem IsHomogeneousCell.subset_zero (h : IsHomogeneousCell R A 0) (hA : ∀ i, A' i ⊆ A i) :
    IsHomogeneousCell R A' 0 := by
  classical
  rw [isHomogeneousCell_def] at h ⊢
  have hmass : (0 : ℝ) ≤ ∏ i, ((A i).card : ℝ) := Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
  rcases h with h | h
  · -- No related tuples upstairs, hence none downstairs.
    left
    have hzero : tupleCount R A = 0 := by
      have hle : (tupleCount R A : ℝ) ≤ 0 := by
        have := card_filter_le_of_tupleDensity_le h
        nlinarith
      exact_mod_cast le_antisymm hle (Nat.cast_nonneg (α := ℝ) _)
    have hzero' : tupleCount R A' = 0 := Nat.le_zero.mp (hzero ▸ tupleCount_mono hA)
    rw [tupleDensity_eq_count_div, hzero']
    simp
  · -- Every tuple related upstairs, so the complement is empty downstairs too.
    rw [sub_zero] at h
    have hnot : tupleCount (fun x ↦ ¬ R x) A = 0 := by
      have hR : (1 : ℝ) * ∏ i, ((A i).card : ℝ) ≤ (tupleCount R A : ℝ) :=
        le_card_filter_of_le_tupleDensity h
      have hsum := tupleCount_add_neg (R := R) (A := A)
      have hcard : ((Fintype.piFinset A).card : ℝ) = ∏ i, ((A i).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
      have hle : ((Fintype.piFinset A).card : ℝ) ≤ (tupleCount R A : ℝ) := by
        rw [hcard]; linarith
      have h1 : (Fintype.piFinset A).card ≤ tupleCount R A := by exact_mod_cast hle
      have h2 : tupleCount R A ≤ (Fintype.piFinset A).card := tupleCount_le_card
      omega
    have hnot' : tupleCount (fun x ↦ ¬ R x) A' = 0 :=
      Nat.le_zero.mp (hnot ▸ tupleCount_mono (R := fun x ↦ ¬ R x) hA)
    rcases Finset.eq_empty_or_nonempty (Fintype.piFinset A') with hemp | hne
    · left
      rw [tupleDensity_eq_zero_of_box_empty hemp]
    · right
      rw [sub_zero]
      have hd : tupleDensity (fun x ↦ ¬ R x) A' = 0 := by
        rw [tupleDensity_eq_count_div, hnot']
        simp
      rw [tupleDensity_neg (Fintype.piFinset_nonempty.mp hne)] at hd
      linarith

/-! ### Degraded restriction -/

/-- The shared estimate behind both branches of `IsHomogeneousCell.restrict`: a raw-mass bound
on a relation over the cell `A` descends to a density bound on a subcell, degraded by the
**product of the coordinatewise inverse relative masses**.

Guard-free downstairs: if some `A' i` is empty the density is `0`, which is below the
(nonnegative) right-hand side. -/
theorem tupleDensity_restrict_le [DecidableEq ι] {S : (ι → α) → Prop} [DecidablePred S]
    {c : ℝ} {ρ : ι → ℝ} (hc : 0 ≤ c) (hρ : ∀ i, 0 < ρ i) (hA : ∀ i, A' i ⊆ A i)
    (hcard : ∀ i, ρ i * ((A i).card : ℝ) ≤ ((A' i).card : ℝ))
    (hS : (tupleCount S A : ℝ) ≤ c * ∏ i, ((A i).card : ℝ)) :
    tupleDensity S A' ≤ c / ∏ i, ρ i := by
  have hP : (0 : ℝ) < ∏ i, ρ i := Finset.prod_pos fun i _ ↦ hρ i
  have hmass' : (0 : ℝ) ≤ ∏ i, ((A' i).card : ℝ) := Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
  rcases eq_or_lt_of_le hmass' with hzero | hpos
  · rw [tupleDensity_eq_count_div, Fintype.card_piFinset, Nat.cast_prod, ← hzero, div_zero]
    exact div_nonneg hc hP.le
  · -- The subcell is realized, so the relative-mass comparison can be divided through.
    have hprod : (∏ i, ρ i) * ∏ i, ((A i).card : ℝ) ≤ ∏ i, ((A' i).card : ℝ) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun i _ ↦ mul_nonneg (hρ i).le (Nat.cast_nonneg _))
        fun i _ ↦ hcard i
    have hcount : (tupleCount S A' : ℝ) ≤ c * ∏ i, ((A i).card : ℝ) :=
      le_trans (Nat.cast_le.mpr (tupleCount_mono hA)) hS
    rw [tupleDensity_eq_count_div, Fintype.card_piFinset, Nat.cast_prod,
      div_le_div_iff₀ hpos hP]
    calc (tupleCount S A' : ℝ) * ∏ i, ρ i
        ≤ (c * ∏ i, ((A i).card : ℝ)) * ∏ i, ρ i := mul_le_mul_of_nonneg_right hcount hP.le
      _ = c * ((∏ i, ρ i) * ∏ i, ((A i).card : ℝ)) := by ring
      _ ≤ c * ∏ i, ((A' i).card : ℝ) := mul_le_mul_of_nonneg_left hprod hc

/-- **Quantitative restriction.** Homogeneity passes to a subcell occupying at least a `ρ i`
fraction of coordinate `i`, with the tolerance degraded by `∏ i, ρ i` — the exceptional mass
can concentrate by the inverse relative cell mass.

The proportions are tracked **coordinatewise** rather than as a single cell fraction, so that a
consumer shrinking only some coordinates pays only those coordinates' factors. -/
theorem IsHomogeneousCell.restrict {ρ : ι → ℝ} (h : IsHomogeneousCell R A ε) (hε : 0 ≤ ε)
    (hρ : ∀ i, 0 < ρ i) (hA : ∀ i, A' i ⊆ A i)
    (hcard : ∀ i, ρ i * ((A i).card : ℝ) ≤ ((A' i).card : ℝ)) :
    IsHomogeneousCell R A' (ε / ∏ i, ρ i) := by
  classical
  have hP : (0 : ℝ) < ∏ i, ρ i := Finset.prod_pos fun i _ ↦ hρ i
  rw [isHomogeneousCell_def] at h ⊢
  rcases h with h | h
  · exact Or.inl (tupleDensity_restrict_le hε hρ hA hcard (card_filter_le_of_tupleDensity_le h))
  · -- Sparse complement upstairs: bound its count, restrict, then convert back.
    have hcardA : ((Fintype.piFinset A).card : ℝ) = ∏ i, ((A i).card : ℝ) := by
      rw [Fintype.card_piFinset, Nat.cast_prod]
    have hnotcount : (tupleCount (fun x ↦ ¬ R x) A : ℝ) ≤ ε * ∏ i, ((A i).card : ℝ) := by
      have hR : (1 - ε) * ∏ i, ((A i).card : ℝ) ≤ (tupleCount R A : ℝ) :=
        le_card_filter_of_le_tupleDensity h
      have hsum : (tupleCount R A : ℝ) + (tupleCount (fun x ↦ ¬ R x) A : ℝ)
          = ∏ i, ((A i).card : ℝ) := by
        rw [← hcardA]
        exact_mod_cast congrArg (Nat.cast (R := ℝ)) (tupleCount_add_neg (R := R) (A := A))
      linarith
    have hnotd : tupleDensity (fun x ↦ ¬ R x) A' ≤ ε / ∏ i, ρ i :=
      tupleDensity_restrict_le hε hρ hA hcard hnotcount
    rcases Finset.eq_empty_or_nonempty (Fintype.piFinset A') with hemp | hne
    · left
      rw [tupleDensity_eq_zero_of_box_empty hemp]
      positivity
    · right
      rw [tupleDensity_neg (Fintype.piFinset_nonempty.mp hne)] at hnotd
      linarith

/-! ### `n`-box density perturbation

Growing every coordinate of a box by a relative factor at most `1 + γ` moves the tuple density
by at most `(Fintype.card ι) * γ`. The constant is **exactly the arity**, and it is first-order
sharp: the honest bound is `1 - (1 + γ)⁻ⁿ`, and `n * γ` is its tangent at `γ = 0`.

The route is a one-coordinate-at-a-time telescoping of the product of side lengths — each
coordinate contributes one factor of `γ` against the *larger* box — packaged as
`prod_sub_prod_le_card_mul_of_le`. -/

omit [Fintype ι] in
/-- **Telescoping product comparison.** If every `b i` is nonnegative, below `p i`, and within a
factor `1 + γ` of it, then the two products differ by at most `|s| · γ` times the larger one.

The proof deletes one coordinate at a time; each deletion costs a single factor of `γ` against
the larger product, which is where the linear-in-arity constant comes from. -/
theorem prod_sub_prod_le_card_mul_of_le {s : Finset ι} {b p : ι → ℝ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hbp : ∀ i ∈ s, b i ≤ p i)
    (hgrow : ∀ i ∈ s, p i ≤ (1 + γ) * b i) :
    (∏ i ∈ s, p i) - ∏ i ∈ s, b i ≤ (s.card : ℝ) * γ * ∏ i ∈ s, p i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hb' : ∀ i ∈ s, 0 ≤ b i := fun i hi ↦ hb i (Finset.mem_insert_of_mem hi)
    have hbp' : ∀ i ∈ s, b i ≤ p i := fun i hi ↦ hbp i (Finset.mem_insert_of_mem hi)
    have hgrow' : ∀ i ∈ s, p i ≤ (1 + γ) * b i := fun i hi ↦ hgrow i (Finset.mem_insert_of_mem hi)
    have hrec := ih hb' hbp' hgrow'
    have hBs : (0 : ℝ) ≤ ∏ i ∈ s, b i := Finset.prod_nonneg hb'
    have hPs : (0 : ℝ) ≤ ∏ i ∈ s, p i :=
      Finset.prod_nonneg fun i hi ↦ (hb' i hi).trans (hbp' i hi)
    have hba : 0 ≤ b a := hb a (Finset.mem_insert_self a s)
    have hbpa : b a ≤ p a := hbp a (Finset.mem_insert_self a s)
    have hga : p a ≤ (1 + γ) * b a := hgrow a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    -- `p a · P - b a · B = (p a - b a) · P + b a · (P - B)`, and each summand costs one `γ`.
    nlinarith [mul_nonneg hba hPs, mul_le_mul_of_nonneg_left hrec hba,
      mul_le_mul_of_nonneg_right (sub_nonneg.mpr hbpa) hPs,
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hbpa) hγ) hPs,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) s.card) hγ) hPs,
      mul_nonneg hγ hPs]

/-- The mass of the larger box exceeds that of the smaller one by at most `n · γ` times the
larger mass, where `n = Fintype.card ι`. -/
theorem prod_card_sub_le_of_grow [DecidableEq ι] {γ : ℝ} (hγ : 0 ≤ γ) (hA : ∀ i, A' i ⊆ A i)
    (hgrow : ∀ i, ((A i).card : ℝ) ≤ (1 + γ) * ((A' i).card : ℝ)) :
    (∏ i, ((A i).card : ℝ)) - ∏ i, ((A' i).card : ℝ)
      ≤ (Fintype.card ι : ℝ) * γ * ∏ i, ((A i).card : ℝ) :=
  prod_sub_prod_le_card_mul_of_le hγ (fun _ _ ↦ Nat.cast_nonneg _)
    (fun i _ ↦ Nat.cast_le.mpr (Finset.card_le_card (hA i))) fun i _ ↦ hgrow i

/-- **`n`-box density perturbation.** If `A'` sits inside `A` coordinatewise and every side of
`A` is at most a factor `1 + γ` longer than the corresponding side of `A'`, then the two tuple
densities differ by at most `(Fintype.card ι) * γ`.

The constant `c(n) = n` is the arity itself — no auxiliary named constant is needed. It is
first-order sharp: the exact bound produced by the argument is `1 - (1 + γ)⁻ⁿ ≤ n · γ`.

Guard-free: if some side of `A'` is empty then the growth hypothesis forces the corresponding
side of `A` to be empty too, both densities are `0`, and the bound reads `0 ≤ n · γ`. -/
theorem abs_tupleDensity_sub_le_of_grow [DecidableEq ι] [DecidablePred R] {γ : ℝ} (hγ : 0 ≤ γ)
    (hA : ∀ i, A' i ⊆ A i) (hgrow : ∀ i, ((A i).card : ℝ) ≤ (1 + γ) * ((A' i).card : ℝ)) :
    |tupleDensity R A - tupleDensity R A'| ≤ (Fintype.card ι : ℝ) * γ := by
  classical
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hmA' : (0 : ℝ) ≤ ∏ i, ((A' i).card : ℝ) := Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
  rcases eq_or_lt_of_le hmA' with hzero | hpos
  · -- Some side of `A'` is empty; the growth hypothesis empties the same side of `A`.
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hzero.symm
    have hi' : (A' i).card = 0 := by exact_mod_cast hi
    have hAi : (A i).card = 0 := by
      have := hgrow i
      rw [hi] at this
      have h0 : ((A i).card : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
    rw [tupleDensity_eq_zero_of_side_empty (R := R) (Finset.card_eq_zero.mp hAi),
      tupleDensity_eq_zero_of_side_empty (R := R) (Finset.card_eq_zero.mp hi')]
    simpa using mul_nonneg hn0 hγ
  · have hmAle : (∏ i, ((A' i).card : ℝ)) ≤ ∏ i, ((A i).card : ℝ) :=
      Finset.prod_le_prod (fun i _ ↦ Nat.cast_nonneg _)
        fun i _ ↦ Nat.cast_le.mpr (Finset.card_le_card (hA i))
    have hposA : (0 : ℝ) < ∏ i, ((A i).card : ℝ) := lt_of_lt_of_le hpos hmAle
    have htel := prod_card_sub_le_of_grow (A := A) (A' := A') hγ hA hgrow
    -- Counts: monotone, at most the box, and short of the larger count by at most the gap.
    have hmono : (tupleCount R A' : ℝ) ≤ (tupleCount R A : ℝ) :=
      Nat.cast_le.mpr (tupleCount_mono hA)
    have hsmall : (tupleCount R A' : ℝ) ≤ ∏ i, ((A' i).card : ℝ) := by
      have := tupleCount_le_card (R := R) (A := A')
      rw [Fintype.card_piFinset] at this
      exact_mod_cast this
    have hgap : (tupleCount R A : ℝ) + ∏ i, ((A' i).card : ℝ)
        ≤ (tupleCount R A' : ℝ) + ∏ i, ((A i).card : ℝ) := by
      have hnat : tupleCount R A + (Fintype.piFinset A').card
          ≤ tupleCount R A' + (Fintype.piFinset A).card := by
        have hsub : Fintype.piFinset A' ⊆ Fintype.piFinset A := Fintype.piFinset_subset _ _ hA
        have hcover : (Fintype.piFinset A).filter R
            ⊆ ((Fintype.piFinset A').filter R) ∪ (Fintype.piFinset A \ Fintype.piFinset A') := by
          intro x hx
          rw [Finset.mem_filter] at hx
          by_cases hxa : x ∈ Fintype.piFinset A'
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxa, hx.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx.1, hxa⟩)
        have h1 : tupleCount R A
            ≤ tupleCount R A' + (Fintype.piFinset A \ Fintype.piFinset A').card :=
          le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
        have h2 : (Fintype.piFinset A \ Fintype.piFinset A').card + (Fintype.piFinset A').card
            = (Fintype.piFinset A).card := Finset.card_sdiff_add_card_eq_card hsub
        omega
      have hcA : ((Fintype.piFinset A).card : ℝ) = ∏ i, ((A i).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
      have hcA' : ((Fintype.piFinset A').card : ℝ) = ∏ i, ((A' i).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this
      rw [hcA, hcA'] at this
      linarith
    have hN0 : (0 : ℝ) ≤ (tupleCount R A' : ℝ) := Nat.cast_nonneg _
    rw [tupleDensity_eq_count_div, tupleDensity_eq_count_div, Fintype.card_piFinset,
      Fintype.card_piFinset, Nat.cast_prod, Nat.cast_prod, abs_sub_le_iff]
    constructor
    · rw [div_sub_div _ _ hposA.ne' hpos.ne', div_le_iff₀ (mul_pos hposA hpos)]
      nlinarith [mul_le_mul_of_nonneg_right htel hmA',
        mul_nonneg (sub_nonneg.mpr hmAle) hN0]
    · rw [div_sub_div _ _ hpos.ne' hposA.ne', div_le_iff₀ (mul_pos hpos hposA)]
      nlinarith [mul_le_mul_of_nonneg_left htel hmA',
        mul_le_mul_of_nonneg_right (sub_nonneg.mpr hmAle) (sub_nonneg.mpr hsmall)]

/-- Homogeneity is stable under density perturbation: if two cells have densities within `γ`,
homogeneity of one at `ε` gives homogeneity of the other at `ε + γ`. -/
theorem IsHomogeneousCell.of_abs_tupleDensity_sub_le [DecidableEq ι] [DecidablePred R] {γ : ℝ}
    (h : IsHomogeneousCell R A' ε)
    (hclose : |tupleDensity R A - tupleDensity R A'| ≤ γ) :
    IsHomogeneousCell R A (ε + γ) := by
  rw [isHomogeneousCell_def] at h ⊢
  rw [abs_le] at hclose
  rcases h with h | h
  · exact Or.inl (by linarith [hclose.2])
  · exact Or.inr (by linarith [hclose.1])

/-- The packaged transfer: homogeneity of a subcell moves to the cell that grew each coordinate
by a factor at most `1 + γ`, at tolerance `ε + n · γ`. -/
theorem IsHomogeneousCell.of_grow [DecidableEq ι] [DecidablePred R] {γ : ℝ} (hγ : 0 ≤ γ)
    (h : IsHomogeneousCell R A' ε) (hA : ∀ i, A' i ⊆ A i)
    (hgrow : ∀ i, ((A i).card : ℝ) ≤ (1 + γ) * ((A' i).card : ℝ)) :
    IsHomogeneousCell R A (ε + (Fintype.card ι : ℝ) * γ) :=
  h.of_abs_tupleDensity_sub_le (abs_tupleDensity_sub_le_of_grow hγ hA hgrow)

/-! ### Tests and adversarial examples -/

section Tests

-- **Zero-instance smoke test**: the public statement elaborates for an arbitrary relation over
-- an arbitrary carrier and an arbitrary finite index, with no `DecidableEq` (on either the
-- index or the carrier), no `Fintype α`, and no decidability of the relation. This example is
-- the frozen contract; do not add instances to make a change to the definition compile.
example {X J : Type*} [Fintype J] (R : (J → X) → Prop) (A : J → Finset X) (ε : ℝ) : Prop :=
  IsHomogeneousCell R A ε

-- The diagonal of `Fin 3` over a `Fin 2`-indexed box has density `1/3`, so the cell is
-- `1/3`-homogeneous (sparse side) but nothing better on that side.
example : IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ)
    (1 / 3) := by
  rw [isHomogeneousCell_def]
  left
  rw [tupleDensity_eq_count_div,
    show tupleCount (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ) = 3 from by
      decide,
    show (Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))).card = 9 from by
      decide]
  norm_num

-- Monotonicity in the tolerance.
example (h : IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ)
      (1 / 3)) :
    IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ) (1 / 2) :=
  h.mono (by norm_num)

-- **Empty box.** A cell with an empty side is `ε`-homogeneous for every `ε ≥ 0`, via the
-- sparse disjunct — even for the always-true relation, which is *not* dense there.
example (ε : ℝ) (hε : 0 ≤ ε) :
    IsHomogeneousCell (fun _ : Fin 2 → Fin 3 => True) ![Finset.univ, ∅] ε :=
  isHomogeneousCell_of_side_empty (i := 1) rfl hε

-- **Degenerate index.** Over an empty index type the box is a singleton, so every relation is
-- exactly `0`-homogeneous: density is `0` or `1` on the nose.
example : IsHomogeneousCell (fun _ : Empty → Fin 3 => True) (fun _ => Finset.univ) 0 := by
  rw [isHomogeneousCell_def]
  right
  rw [tupleDensity_eq_count_div,
    show tupleCount (fun _ : Empty → Fin 3 => True) (fun _ => Finset.univ) = 1 from by decide,
    show (Fintype.piFinset fun _ : Empty => (Finset.univ : Finset (Fin 3))).card = 1 from by
      decide]
  norm_num

-- **Index-generic.** Nothing above is tied to `Fin k`: here the index is `Bool`.
example : IsHomogeneousCell (fun x : Bool → Fin 2 => x true = x false) (fun _ => Finset.univ)
    (1 / 2) := by
  rw [isHomogeneousCell_def]
  left
  rw [tupleDensity_eq_count_div,
    show tupleCount (fun x : Bool → Fin 2 => x true = x false) (fun _ => Finset.univ) = 2 from by
      decide,
    show (Fintype.piFinset fun _ : Bool => (Finset.univ : Finset (Fin 2))).card = 4 from by
      decide]
  norm_num

-- **The binary bridge**, at a concrete relation: the `Fin 2`-indexed cell and the rectangle
-- are the same statement.
example (A₂ : Fin 2 → Finset (Fin 3)) (ε : ℝ) :
    IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) A₂ ε
      ↔ IsHomogeneousPair (fun a b : Fin 3 => (![a, b] : Fin 2 → Fin 3) 0 = ![a, b] 1)
          (A₂ 0) (A₂ 1) ε :=
  isHomogeneousCell_two_iff

-- **Exact homogeneity, subcell closure**: the empty relation is `0`-homogeneous and stays so
-- on every subcell, including empty ones.
example (A' : Fin 2 → Finset (Fin 3)) :
    IsHomogeneousCell (fun _ : Fin 2 → Fin 3 => False) A' 0 :=
  IsHomogeneousCell.subset_zero (A := fun _ => Finset.univ)
    (by
      rw [isHomogeneousCell_def]
      left
      rw [tupleDensity_eq_count_div,
        show tupleCount (fun _ : Fin 2 → Fin 3 => False) (fun _ => Finset.univ) = 0 from by
          decide]
      simp)
    fun _ => Finset.subset_univ _

-- **A concrete quantitative restriction**: halving each of two coordinates degrades the
-- tolerance by `1/4`.
example (h : IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun _ => Finset.univ)
      (1 / 3))
    {A' : Fin 2 → Finset (Fin 3)} (hA : ∀ i, A' i ⊆ (fun _ => Finset.univ) i)
    (hcard : ∀ i, (1 / 2 : ℝ) * (((fun _ => Finset.univ : Fin 2 → Finset (Fin 3)) i).card : ℝ)
      ≤ ((A' i).card : ℝ)) :
    IsHomogeneousCell (fun x : Fin 2 → Fin 3 => x 0 = x 1) A'
      ((1 / 3) / ∏ _i : Fin 2, (1 / 2 : ℝ)) :=
  h.restrict (by norm_num) (fun _ => by norm_num) hA hcard

-- **`γ = 0`**: the growth hypothesis forces equal side lengths, and the perturbation bound
-- degenerates to `0` — the densities must then be literally equal, which must still typecheck.
example :
    |tupleDensity (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun _ => Finset.univ)
        - tupleDensity (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun _ => Finset.univ)|
      ≤ (Fintype.card (Fin 2) : ℝ) * 0 :=
  abs_tupleDensity_sub_le_of_grow (R := fun x : Fin 2 → Fin 2 => x 0 = x 1)
    (A := fun _ => Finset.univ) (A' := fun _ => Finset.univ) le_rfl
    (fun _ => Finset.subset_univ _) fun _ => by norm_num

-- **Degenerate index in the perturbation bound**: over an empty index type the constant is
-- `Fintype.card Empty = 0`, so the bound asserts equality — and it holds, both boxes being the
-- singleton containing the empty tuple.
example (γ : ℝ) (hγ : 0 ≤ γ) :
    |tupleDensity (fun _ : Empty → Fin 3 => True) (fun _ => Finset.univ)
        - tupleDensity (fun _ : Empty → Fin 3 => True) (fun _ => Finset.univ)|
      ≤ (Fintype.card Empty : ℝ) * γ :=
  abs_tupleDensity_sub_le_of_grow (R := fun _ : Empty → Fin 3 => True)
    (A := fun _ => Finset.univ) (A' := fun _ => Finset.univ) hγ
    (fun i => i.elim) fun i => i.elim

-- **Adversarial, documented**: at `γ = 1` (each side may double) the arity-`2` bound is `2`,
-- vacuously large — two densities differ by at most `1`. The theorem must nevertheless apply
-- at this extreme; only for `γ < 1 / n` is the bound informative.
example :
    |tupleDensity (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun _ => Finset.univ)
        - tupleDensity (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun _ => ({0} : Finset (Fin 2)))|
      ≤ (Fintype.card (Fin 2) : ℝ) * 1 :=
  abs_tupleDensity_sub_le_of_grow (R := fun x : Fin 2 → Fin 2 => x 0 = x 1)
    (A := fun _ => Finset.univ) (A' := fun _ => ({0} : Finset (Fin 2))) zero_le_one
    (fun _ => Finset.subset_univ _) fun _ => by norm_num

-- The telescoping product estimate on its own, at a concrete two-coordinate instance:
-- sides `2 ↦ 3` grow by a factor `1 + 1/2`, and `9 - 4 = 5 ≤ 2 * (1/2) * 9 = 9`.
example :
    (∏ _i : Fin 2, (3 : ℝ)) - ∏ _i : Fin 2, (2 : ℝ)
      ≤ ((Finset.univ : Finset (Fin 2)).card : ℝ) * (1 / 2) * ∏ _i : Fin 2, (3 : ℝ) :=
  prod_sub_prod_le_card_mul_of_le (by norm_num) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) fun _ _ => by norm_num

end Tests

end RegularityLemmata
