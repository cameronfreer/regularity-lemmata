/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Average
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Almost-constant functions and rectangles

The analytic analogue of `ε`-homogeneity, following Conant–Terry
([arXiv:2607.21762](https://arxiv.org/abs/2607.21762), Definitions 1.6 and 2.1): a function is
**`δ`-constant** on a set when its values pairwise differ by strictly less than `δ`, and
**`ε`-almost `δ`-constant** when a subset carrying strictly more than a `(1 − ε)`-fraction is
`δ`-constant. The pair form on a rectangle is the one-variable predicate on the product —
one definition, not a parallel notion.

## Frozen conventions

* **Strict inequalities** in the closeness and exceptional-mass clauses (`< δ`, `>` mass),
  weak inequalities are reserved for ladder/tree witnesses upstairs. Strictness is
  load-bearing for indicator specializations: with `≤ δ` at `δ = 1`, "1-constant" would be
  vacuously true of every `[0,1]`-valued function.
* **Totalization**: the empty set is almost constant (`V = ∅ ∨ …`), matching the library's
  guard-free homogeneity conventions. On nonempty sets this **agrees with the paper under its
  `[0,1]` range and positive-parameter assumptions**; it is not a verbatim transcription. What
  is formalized here is a **real-valued, empty-totalized extension**: `φ` is an arbitrary
  `α → ℝ`, and the definitions place no range or sign constraint of their own. Range and
  positivity hypotheses appear on the theorems that need them, never in the predicates.
* **No stability**: nothing here mentions ladders, trees, goodness, or ranks; those live
  upstairs.

## The two theorems

* `exists_separation_of_not_isAlmostConstantOn` (Conant–Terry Proposition 2.2): a function
  that is not `2ε`-almost `δ`-constant admits a threshold `r` with `ε`-fractions both at or
  below `r` and at or above `r + δ`. The proof extracts the `⌈ε·|V|⌉`-th smallest value as
  the least element of the set of points whose lower level set is large — no sorting
  machinery is needed.
* `abs_averageOn_sub_averageOn_le_of_levelSets` (the **level-set staircase**): whenever every
  level set `{x ∈ A : r·ν ≤ φ x}` keeps its density on `Q` within `β` of its density on `A`,
  the averages differ by at most `2ν + (1 + ν)β` — with the `2ν + 2β` reading under `ν ≤ 1`
  and a trivial regime at `1 < ν`. This is what reduces `[0,1]`-valued average control to the
  finite-family *set*-density control of `Partition/BalancedSlicing.lean`, replacing any new
  real-valued concentration.
-/

namespace RegularityLemmata

variable {α X Y : Type*} {φ : α → ℝ} {δ δ' ε ε' : ℝ} {V W : Finset α}

/-! ### The predicates -/

/-- `φ` is `δ`-constant on `W`: values pairwise differ by strictly less than `δ`. -/
def IsDeltaConstantOn (φ : α → ℝ) (δ : ℝ) (W : Finset α) : Prop :=
  ∀ v ∈ W, ∀ v' ∈ W, |φ v - φ v'| < δ

/-- `φ` is `ε`-almost `δ`-constant on `V`: some subset carrying strictly more than a
`(1 − ε)`-fraction of `V` is `δ`-constant. Totalized: the empty set qualifies outright. -/
def IsAlmostConstantOn (φ : α → ℝ) (δ ε : ℝ) (V : Finset α) : Prop :=
  V = ∅ ∨ ∃ W ⊆ V, (1 - ε) * (V.card : ℝ) < (W.card : ℝ) ∧ IsDeltaConstantOn φ δ W

/-- The pair form on a rectangle **is** the one-variable predicate on the product. -/
def IsAlmostConstantPair (f : RectKernel X Y) (δ ε : ℝ) (A : Finset X) (B : Finset Y) :
    Prop :=
  IsAlmostConstantOn (fun p ↦ f p.1 p.2) δ ε (A ×ˢ B)

/-! ### Monotonicity and trivial regimes -/

theorem IsDeltaConstantOn.mono (h : IsDeltaConstantOn φ δ W) (hδ : δ ≤ δ') :
    IsDeltaConstantOn φ δ' W :=
  fun v hv v' hv' ↦ lt_of_lt_of_le (h v hv v' hv') hδ

theorem IsDeltaConstantOn.subset {W' : Finset α} (h : IsDeltaConstantOn φ δ W)
    (hW' : W' ⊆ W) : IsDeltaConstantOn φ δ W' :=
  fun v hv v' hv' ↦ h v (hW' hv) v' (hW' hv')

theorem isDeltaConstantOn_empty (φ : α → ℝ) (δ : ℝ) :
    IsDeltaConstantOn φ δ (∅ : Finset α) :=
  fun v hv ↦ absurd hv (by simp)

/-- Singletons are `δ`-constant for every positive `δ`. -/
theorem isDeltaConstantOn_singleton (hδ : 0 < δ) (v : α) :
    IsDeltaConstantOn φ δ ({v} : Finset α) := by
  intro w hw w' hw'
  rw [Finset.mem_singleton] at hw hw'
  subst hw; subst hw'
  simpa using hδ

/-- … and **only** for positive `δ`: strictness makes even the one-point diagonal fail at
`δ ≤ 0`. -/
theorem isDeltaConstantOn_singleton_iff (v : α) :
    IsDeltaConstantOn φ δ ({v} : Finset α) ↔ 0 < δ := by
  refine ⟨fun h ↦ ?_, fun hδ ↦ isDeltaConstantOn_singleton hδ v⟩
  have := h v (Finset.mem_singleton_self v) v (Finset.mem_singleton_self v)
  simpa using this

theorem IsAlmostConstantOn.mono_delta (h : IsAlmostConstantOn φ δ ε V) (hδ : δ ≤ δ') :
    IsAlmostConstantOn φ δ' ε V := by
  rcases h with rfl | ⟨W, hWV, hcard, hconst⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨W, hWV, hcard, hconst.mono hδ⟩

theorem IsAlmostConstantOn.mono_eps (h : IsAlmostConstantOn φ δ ε V) (hε : ε ≤ ε') :
    IsAlmostConstantOn φ δ ε' V := by
  rcases h with rfl | ⟨W, hWV, hcard, hconst⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨W, hWV, lt_of_le_of_lt ?_ hcard, hconst⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

theorem isAlmostConstantOn_empty (φ : α → ℝ) (δ ε : ℝ) :
    IsAlmostConstantOn φ δ ε (∅ : Finset α) :=
  Or.inl rfl

/-- A globally `δ`-constant function is `ε`-almost `δ`-constant for every positive `ε`. -/
theorem IsDeltaConstantOn.isAlmostConstantOn (h : IsDeltaConstantOn φ δ V) (hε : 0 < ε) :
    IsAlmostConstantOn φ δ ε V := by
  rcases V.eq_empty_or_nonempty with rfl | hV
  · exact Or.inl rfl
  · refine Or.inr ⟨V, subset_refl V, ?_, h⟩
    have hpos : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hV
    nlinarith

/-- The trivial regime `1 ≤ ε`: a singleton witness suffices, for any positive `δ`. -/
theorem isAlmostConstantOn_of_one_le (hδ : 0 < δ) (hε : 1 ≤ ε) :
    IsAlmostConstantOn φ δ ε V := by
  rcases V.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨{v}, Finset.singleton_subset_iff.mpr hv, ?_,
      isDeltaConstantOn_singleton hδ v⟩
    have h1 : (1 - ε) * (V.card : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    simpa using lt_of_le_of_lt h1 one_pos

theorem IsAlmostConstantPair.mono_delta {f : RectKernel X Y} {A : Finset X} {B : Finset Y}
    (h : IsAlmostConstantPair f δ ε A B) (hδ : δ ≤ δ') :
    IsAlmostConstantPair f δ' ε A B :=
  IsAlmostConstantOn.mono_delta h hδ

theorem IsAlmostConstantPair.mono_eps {f : RectKernel X Y} {A : Finset X} {B : Finset Y}
    (h : IsAlmostConstantPair f δ ε A B) (hε : ε ≤ ε') :
    IsAlmostConstantPair f δ ε' A B :=
  IsAlmostConstantOn.mono_eps h hε

/-! ### Singleton bridges

A rectangle with a singleton side is the one-variable predicate on the other side. These are
the specializations a fibrewise argument needs: they turn control of `φ` along one fiber into
control of the pair form, with no stability content whatsoever. -/

/-- A singleton **left** side: almost-constancy of the fiber `f a` transfers to the pair. -/
theorem IsAlmostConstantOn.isAlmostConstantPair_singleton_left [DecidableEq X] [DecidableEq Y]
    {f : RectKernel X Y} {a : X} {B : Finset Y} (h : IsAlmostConstantOn (f a) δ ε B) :
    IsAlmostConstantPair f δ ε {a} B := by
  classical
  rcases h with hB | ⟨W, hWB, hcard, hconst⟩
  · exact Or.inl (by rw [hB, Finset.product_empty])
  · refine Or.inr ⟨{a} ×ˢ W, Finset.product_subset_product Finset.Subset.rfl hWB, ?_, ?_⟩
    · rw [Finset.card_product, Finset.card_product, Finset.card_singleton]
      simpa using hcard
    · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy'
      rw [Finset.mem_product, Finset.mem_singleton] at hxy hxy'
      obtain ⟨rfl, hy⟩ := hxy
      obtain ⟨rfl, hy'⟩ := hxy'
      exact hconst _ hy _ hy'

/-- A singleton **right** side: almost-constancy of the co-fiber `f · b` transfers to the
pair. -/
theorem IsAlmostConstantOn.isAlmostConstantPair_singleton_right [DecidableEq X] [DecidableEq Y]
    {f : RectKernel X Y} {A : Finset X} {b : Y}
    (h : IsAlmostConstantOn (fun x ↦ f x b) δ ε A) :
    IsAlmostConstantPair f δ ε A {b} := by
  classical
  rcases h with hA | ⟨W, hWA, hcard, hconst⟩
  · exact Or.inl (by rw [hA, Finset.empty_product])
  · refine Or.inr ⟨W ×ˢ {b}, Finset.product_subset_product hWA Finset.Subset.rfl, ?_, ?_⟩
    · rw [Finset.card_product, Finset.card_product, Finset.card_singleton]
      simpa using hcard
    · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy'
      rw [Finset.mem_product, Finset.mem_singleton] at hxy hxy'
      obtain ⟨hx, rfl⟩ := hxy
      obtain ⟨hx', rfl⟩ := hxy'
      exact hconst _ hx _ hx'

/-- **A one-point rectangle is almost constant** for every positive `δ`: the product carries a
single pair, so it is `δ`-constant outright.

`0 < ε` is required and cannot be weakened to `0 ≤ ε`: the exceptional-mass clause is strict,
and at `ε = 0` it reads `1 < 1`. The whole rectangle is still `δ`-constant — that is
`isDeltaConstantOn_singleton` — but it does not witness *almost*-constancy at zero tolerance. -/
theorem isAlmostConstantPair_singleton [DecidableEq X] [DecidableEq Y] (f : RectKernel X Y)
    (hδ : 0 < δ) (hε : 0 < ε) (a : X) (b : Y) : IsAlmostConstantPair f δ ε {a} {b} := by
  classical
  refine Or.inr ⟨{a} ×ˢ {b}, Finset.Subset.rfl, ?_, ?_⟩
  · rw [Finset.card_product, Finset.card_singleton]
    norm_num
    linarith
  · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy'
    rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_singleton] at hxy hxy'
    obtain ⟨rfl, rfl⟩ := hxy
    obtain ⟨rfl, rfl⟩ := hxy'
    simpa using hδ

/-! ### Separation (Conant–Terry Proposition 2.2) -/

/-- **Separation.** A function that is not `2ε`-almost `δ`-constant admits a threshold with
`ε`-fractions at or below it and at or above it plus `δ`. The threshold produced is the
`⌈ε·|V|⌉`-th smallest value of `φ` on `V`.

This **generalizes** Conant–Terry Proposition 2.2: the paper assumes a `[0,1]`-valued
function and returns `r ∈ [0,1]`, while this statement permits an arbitrary real-valued `φ`;
the constants and strict inequalities otherwise match. The range-aware companion
`exists_separation_mem_Icc_of_not_isAlmostConstantOn` is the paper's exact consumer shape. -/
theorem exists_separation_of_not_isAlmostConstantOn [DecidableEq α]
    (hδ : 0 < δ) (hε : 0 < ε) (h : ¬ IsAlmostConstantOn φ δ (2 * ε) V) :
    ∃ r : ℝ, (ε * V.card ≤ ((V.filter fun x ↦ φ x ≤ r).card : ℝ)) ∧
      (ε * V.card ≤ ((V.filter fun x ↦ r + δ ≤ φ x).card : ℝ)) := by
  classical
  -- The failure forces a nonempty host and `2ε < 1` (else a singleton witnesses).
  have hVne : V.Nonempty := by
    rcases V.eq_empty_or_nonempty with rfl | h'
    · exact absurd (isAlmostConstantOn_empty φ δ (2 * ε)) h
    · exact h'
  have hNpos : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hVne
  have hhalf : 2 * ε < 1 := by
    by_contra hge
    exact h (isAlmostConstantOn_of_one_le hδ (le_of_not_gt hge))
  set N := V.card with hNdef
  set m := ⌈ε * (N : ℝ)⌉₊ with hmdef
  have hmR : (m : ℝ) < ε * N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hεm : ε * (N : ℝ) ≤ m := Nat.le_ceil _
  -- The qualifying set: points whose lower level set is `m`-large; its minimum value is `r`.
  set Qual := V.filter (fun x ↦ m ≤ (V.filter fun y ↦ φ y ≤ φ x).card) with hQdef
  have hQne : Qual.Nonempty := by
    obtain ⟨z, hz, hzmax⟩ := V.exists_max_image φ hVne
    refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩⟩
    have hall : V.filter (fun y ↦ φ y ≤ φ z) = V :=
      Finset.filter_true_of_mem fun y hy ↦ hzmax y hy
    rw [hall]
    have : ε * (N : ℝ) < N := by nlinarith
    have hmN : m ≤ N := by
      rw [hmdef]
      exact_mod_cast Nat.ceil_le.mpr this.le
    exact hmN
  obtain ⟨x₀, hx₀Q, hx₀min⟩ := Qual.exists_min_image φ hQne
  set r := φ x₀ with hrdef
  have hx₀ := Finset.mem_filter.mp hx₀Q
  refine ⟨r, ?_, ?_⟩
  · -- The lower level set of `r` is `m`-large by membership in `Qual`.
    refine le_trans hεm ?_
    exact_mod_cast hx₀.2
  · -- Points strictly below `r` number at most `m − 1` …
    have hlt : (V.filter fun x ↦ φ x < r).card + 1 ≤ m := by
      by_contra hcon
      push Not at hcon
      -- … else the largest of them would qualify below the minimum.
      have hge : m ≤ (V.filter fun x ↦ φ x < r).card := by omega
      have hne : (V.filter fun x ↦ φ x < r).Nonempty := by
        rw [← Finset.card_pos]
        have hm1 : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
        omega
      obtain ⟨z, hz, hzmax⟩ := (V.filter fun x ↦ φ x < r).exists_max_image φ hne
      have hzV := (Finset.mem_filter.mp hz).1
      have hzr : φ z < r := (Finset.mem_filter.mp hz).2
      have hsub : (V.filter fun x ↦ φ x < r) ⊆ V.filter (fun y ↦ φ y ≤ φ z) := by
        intro w hw
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, hzmax w hw⟩
      have hzQ : z ∈ Qual := Finset.mem_filter.mpr
        ⟨hzV, le_trans hge (Finset.card_le_card hsub)⟩
      exact absurd (hx₀min z hzQ) (not_le.mpr hzr)
    -- The middle band is small, else it witnesses almost-constancy.
    have hU : ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ).card : ℝ) ≤ (1 - 2 * ε) * N := by
      by_contra hcon
      push Not at hcon
      refine h (Or.inr ⟨V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ,
        Finset.filter_subset _ _, hcon, ?_⟩)
      intro v hv v' hv'
      have h1 := (Finset.mem_filter.mp hv).2
      have h2 := (Finset.mem_filter.mp hv').2
      rw [abs_lt]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    -- The three bands cover `V`.
    have hcover : (N : ℝ) ≤ ((V.filter fun x ↦ φ x < r).card : ℝ)
        + ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ).card : ℝ)
        + ((V.filter fun x ↦ r + δ ≤ φ x).card : ℝ) := by
      have hsub : V ⊆ (V.filter fun x ↦ φ x < r)
          ∪ ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ)
            ∪ (V.filter fun x ↦ r + δ ≤ φ x)) := by
        intro x hx
        rcases lt_or_ge (φ x) r with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
        · rcases lt_or_ge (φ x) (r + δ) with h2 | h2
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hx, h1, h2⟩))
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hx, h2⟩))
      have hcard := Finset.card_le_card hsub
      have hu2 := Finset.card_union_le
        ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ)) (V.filter fun x ↦ r + δ ≤ φ x)
      have hu1 := Finset.card_union_le (V.filter fun x ↦ φ x < r)
        ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ) ∪ (V.filter fun x ↦ r + δ ≤ φ x))
      have hthis : N ≤ (V.filter fun x ↦ φ x < r).card
          + ((V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ).card
            + (V.filter fun x ↦ r + δ ≤ φ x).card) := by
        calc N = V.card := rfl
          _ ≤ _ := hcard
          _ ≤ _ := hu1
          _ ≤ _ := Nat.add_le_add_left hu2 _
      have hthis' : N ≤ (V.filter fun x ↦ φ x < r).card
          + (V.filter fun x ↦ r ≤ φ x ∧ φ x < r + δ).card
          + (V.filter fun x ↦ r + δ ≤ φ x).card := by omega
      exact_mod_cast hthis'
    have hltR : ((V.filter fun x ↦ φ x < r).card : ℝ) ≤ (m : ℝ) - 1 := by
      have : ((V.filter fun x ↦ φ x < r).card : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast hlt
      linarith
    linarith

/-- **Range-aware separation** — the exact Conant–Terry Proposition 2.2 shape: for a
`[0,1]`-valued function the threshold can be taken in `[0,1]`, since both level sets it
produces are nonempty and pin it between attained values. -/
theorem exists_separation_mem_Icc_of_not_isAlmostConstantOn [DecidableEq α]
    (hδ : 0 < δ) (hε : 0 < ε) (hrange : ∀ x ∈ V, φ x ∈ Set.Icc (0 : ℝ) 1)
    (h : ¬ IsAlmostConstantOn φ δ (2 * ε) V) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1,
      (ε * V.card ≤ ((V.filter fun x ↦ φ x ≤ r).card : ℝ)) ∧
      (ε * V.card ≤ ((V.filter fun x ↦ r + δ ≤ φ x).card : ℝ)) := by
  obtain ⟨r, h1, h2⟩ := exists_separation_of_not_isAlmostConstantOn hδ hε h
  have hVne : V.Nonempty := by
    rcases V.eq_empty_or_nonempty with rfl | h'
    · exact absurd (isAlmostConstantOn_empty φ δ (2 * ε)) h
    · exact h'
  have hNpos : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hVne
  have hlow : (V.filter fun x ↦ φ x ≤ r).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hc
    push Not at hc
    have h0 : ((V.filter fun x ↦ φ x ≤ r).card : ℝ) = 0 := by
      exact_mod_cast Nat.le_zero.mp hc
    nlinarith
  have hhigh : (V.filter fun x ↦ r + δ ≤ φ x).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hc
    push Not at hc
    have h0 : ((V.filter fun x ↦ r + δ ≤ φ x).card : ℝ) = 0 := by
      exact_mod_cast Nat.le_zero.mp hc
    nlinarith
  obtain ⟨a, ha⟩ := hlow
  obtain ⟨b, hb⟩ := hhigh
  have haV := (Finset.mem_filter.mp ha).1
  have har := (Finset.mem_filter.mp ha).2
  have hbV := (Finset.mem_filter.mp hb).1
  have hbr := (Finset.mem_filter.mp hb).2
  refine ⟨r, ⟨?_, ?_⟩, h1, h2⟩
  · exact le_trans (hrange a haV).1 har
  · have := (hrange b hbV).2
    linarith

/-! ### The level-set staircase -/

/-- **The level-set staircase.** If every level set `{x ∈ A : r·ν ≤ φ x}` (at positive levels
up to `1`) keeps its density on `Q` within `β` of its density on `A`, then the `[0,1]`-valued
averages differ by at most `2ν + (1 + ν)β`. This reduces average control to finite-family
set-density control (`exists_balanced_slicing`), with the level count priced at `⌈1/ν⌉`. -/
theorem abs_averageOn_sub_averageOn_le_of_levelSets [DecidableEq α] {φ : α → ℝ}
    {A Q : Finset α} {β ν : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (hQ : Q ⊆ A) (hQne : Q.Nonempty)
    (hrange : ∀ x ∈ A, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hlevels : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * ν ≤ 1 →
      |(((A.filter fun x ↦ (r : ℝ) * ν ≤ φ x) ∩ Q).card : ℝ) / Q.card
        - ((A.filter fun x ↦ (r : ℝ) * ν ≤ φ x).card : ℝ) / A.card| ≤ β) :
    |averageOn Q φ - averageOn A φ| ≤ 2 * ν + (1 + ν) * β := by
  classical
  have hAne : A.Nonempty := hQne.mono hQ
  -- The active levels: positive multiples of `ν` up to `1`.
  set L := (Finset.Icc 1 ⌈1 / ν⌉₊).filter (fun p : ℕ ↦ (p : ℝ) * ν ≤ 1) with hLdef
  -- Per point, the number of levels cleared is `⌊φ x / ν⌋`.
  have hcount : ∀ x ∈ A, ((L.filter fun p : ℕ ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)
      = (⌊φ x / ν⌋₊ : ℝ) := by
    intro x hx
    obtain ⟨h0, h1⟩ := hrange x hx
    have hfloor_le : ⌊φ x / ν⌋₊ ≤ ⌈1 / ν⌉₊ :=
      le_trans (Nat.floor_le_floor (div_le_div_of_nonneg_right h1 hν.le))
        (Nat.floor_le_ceil _)
    have heq : L.filter (fun p : ℕ ↦ (p : ℝ) * ν ≤ φ x) = Finset.Icc 1 ⌊φ x / ν⌋₊ := by
      ext p
      simp only [hLdef, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp1, hpK⟩, hp1'⟩, hpφ⟩
        exact ⟨hp1, Nat.le_floor ((le_div_iff₀ hν).mpr (by linarith [hpφ]))⟩
      · rintro ⟨hp1, hpfl⟩
        have hpφ : (p : ℝ) * ν ≤ φ x := by
          have := (Nat.le_floor_iff (by positivity)).mp hpfl
          calc (p : ℝ) * ν ≤ (φ x / ν) * ν := by
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hν.le
            _ = φ x := div_mul_cancel₀ _ (ne_of_gt hν)
        exact ⟨⟨⟨hp1, le_trans (Nat.le_floor ((le_div_iff₀ hν).mpr (by linarith)))
          hfloor_le⟩, le_trans hpφ h1⟩, hpφ⟩
    rw [heq, Nat.card_Icc]
    simp
  -- The staircase sandwich, for any nonempty `S ⊆ A`.
  have hsandwich : ∀ S : Finset α, S ⊆ A → S.Nonempty →
      |averageOn S φ - ν * ((∑ p ∈ L, ((S.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ))
        / S.card)| ≤ ν := by
    intro S hSA hSne
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
    -- Swap the double count: levels cleared, summed over points.
    have hswap : ∑ p ∈ L, ((S.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)
        = ∑ x ∈ S, (⌊φ x / ν⌋₊ : ℝ) := by
      have h1 : ∀ p ∈ L, ((S.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)
          = ∑ x ∈ S, (if (p : ℝ) * ν ≤ φ x then (1 : ℝ) else 0) := by
        intro p _
        rw [Finset.sum_boole]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact hcount x (hSA hx)
    -- Pointwise: `ν·⌊φx/ν⌋ ∈ (φx − ν, φx]`.
    have hlow : ∀ x ∈ S, ν * (⌊φ x / ν⌋₊ : ℝ) ≤ φ x := by
      intro x hx
      obtain ⟨h0, _⟩ := hrange x (hSA hx)
      calc ν * (⌊φ x / ν⌋₊ : ℝ) ≤ ν * (φ x / ν) :=
            mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hν.le
        _ = φ x := mul_div_cancel₀ _ (ne_of_gt hν)
    have hhigh : ∀ x ∈ S, φ x < ν * (⌊φ x / ν⌋₊ : ℝ) + ν := by
      intro x hx
      obtain ⟨h0, _⟩ := hrange x (hSA hx)
      have := Nat.lt_floor_add_one (φ x / ν)
      calc φ x = ν * (φ x / ν) := (mul_div_cancel₀ _ (ne_of_gt hν)).symm
        _ < ν * ((⌊φ x / ν⌋₊ : ℝ) + 1) := by
            exact mul_lt_mul_of_pos_left this hν
        _ = ν * (⌊φ x / ν⌋₊ : ℝ) + ν := by ring
    -- Sum and divide.
    rw [hswap, abs_le]
    have hsum_low : ∑ x ∈ S, ν * (⌊φ x / ν⌋₊ : ℝ) ≤ ∑ x ∈ S, φ x :=
      Finset.sum_le_sum hlow
    have hsum_high : ∑ x ∈ S, φ x ≤ ∑ x ∈ S, (ν * (⌊φ x / ν⌋₊ : ℝ) + ν) :=
      Finset.sum_le_sum fun x hx ↦ (hhigh x hx).le
    have hmul : ν * ((∑ x ∈ S, (⌊φ x / ν⌋₊ : ℝ)) / S.card)
        = (∑ x ∈ S, ν * (⌊φ x / ν⌋₊ : ℝ)) / S.card := by
      rw [← mul_div_assoc, Finset.mul_sum]
    have havg : averageOn S φ = (∑ x ∈ S, φ x) / S.card := rfl
    have hplus : ∑ x ∈ S, (ν * (⌊φ x / ν⌋₊ : ℝ) + ν)
        = (∑ x ∈ S, ν * (⌊φ x / ν⌋₊ : ℝ)) + ν * S.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
    constructor
    · rw [havg, hmul]
      rw [div_sub_div_same, le_div_iff₀ hSpos] at *
      nlinarith [hsum_high, hplus]
    · rw [havg, hmul]
      rw [div_sub_div_same, div_le_iff₀ hSpos]
      nlinarith [hsum_low]
  -- Apply the sandwich on `Q` and on `A`, and pay `β` per level.
  have hQside := hsandwich Q hQ hQne
  have hAside := hsandwich A (subset_refl A) hAne
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hAne
  have hQpos : (0 : ℝ) < (Q.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hQne
  -- The level sums differ by at most `|L| · β`, and `ν · |L| ≤ 1 + ν`.
  have hLcard : ν * (L.card : ℝ) ≤ 1 + ν := by
    have h1 : L.card ≤ ⌈1 / ν⌉₊ := by
      calc L.card ≤ (Finset.Icc 1 ⌈1 / ν⌉₊).card := Finset.card_le_card
            (Finset.filter_subset _ _)
        _ = ⌈1 / ν⌉₊ := by rw [Nat.card_Icc]; omega
    have h2 : (⌈1 / ν⌉₊ : ℝ) < 1 / ν + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : ν * (L.card : ℝ) ≤ ν * (⌈1 / ν⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hν.le
    have h4 : ν * (1 / ν + 1) = 1 + ν := by field_simp
    nlinarith
  have hlevel_sum : |(∑ p ∈ L, ((Q.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)) / Q.card
      - (∑ p ∈ L, ((A.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)) / A.card|
      ≤ (L.card : ℝ) * β := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbound : ∀ p ∈ L, |((Q.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ) / Q.card
        - ((A.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ) / A.card| ≤ β := by
      intro p hp
      obtain ⟨hpIcc, hp1⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1', -⟩ := Finset.mem_Icc.mp hpIcc
      have hQfilter : Q.filter (fun x ↦ (p : ℝ) * ν ≤ φ x)
          = (A.filter fun x ↦ (p : ℝ) * ν ≤ φ x) ∩ Q := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_inter]
        exact ⟨fun ⟨hxQ, hxφ⟩ ↦ ⟨⟨hQ hxQ, hxφ⟩, hxQ⟩, fun ⟨⟨hxA, hxφ⟩, hxQ⟩ ↦ ⟨hxQ, hxφ⟩⟩
      rw [hQfilter]
      exact hlevels p hp1' hp1
    calc ∑ p ∈ L, |((Q.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ) / Q.card
          - ((A.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ) / A.card|
        ≤ ∑ _p ∈ L, β := Finset.sum_le_sum hbound
      _ = (L.card : ℝ) * β := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Combine: two triangle inequalities, then price the level count.
  set q1 := ν * ((∑ p ∈ L, ((Q.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)) / Q.card)
    with hq1def
  set a1 := ν * ((∑ p ∈ L, ((A.filter fun x ↦ (p : ℝ) * ν ≤ φ x).card : ℝ)) / A.card)
    with ha1def
  have hmid : |q1 - a1| ≤ ν * ((L.card : ℝ) * β) := by
    rw [hq1def, ha1def, ← mul_sub, abs_mul, abs_of_pos hν]
    exact mul_le_mul_of_nonneg_left hlevel_sum hν.le
  have htri : |averageOn Q φ - averageOn A φ|
      ≤ |averageOn Q φ - q1| + (|q1 - a1| + |a1 - averageOn A φ|) := by
    calc |averageOn Q φ - averageOn A φ| ≤ |averageOn Q φ - q1| + |q1 - averageOn A φ| :=
          abs_sub_le _ _ _
      _ ≤ |averageOn Q φ - q1| + (|q1 - a1| + |a1 - averageOn A φ|) := by
          have := abs_sub_le q1 a1 (averageOn A φ)
          linarith
  have hAside' : |a1 - averageOn A φ| ≤ ν := by
    rw [abs_sub_comm]
    exact hAside
  have hprice : ν * ((L.card : ℝ) * β) ≤ (1 + ν) * β := by
    have := mul_le_mul_of_nonneg_right hLcard hβ
    nlinarith
  linarith [hQside, hmid, htri, hAside', hprice]

/-- The clean `2ν + 2β` reading, under `ν ≤ 1`. -/
theorem abs_averageOn_sub_averageOn_le_of_levelSets_of_le_one [DecidableEq α] {φ : α → ℝ}
    {A Q : Finset α} {β ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hβ : 0 ≤ β) (hQ : Q ⊆ A)
    (hQne : Q.Nonempty) (hrange : ∀ x ∈ A, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hlevels : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * ν ≤ 1 →
      |(((A.filter fun x ↦ (r : ℝ) * ν ≤ φ x) ∩ Q).card : ℝ) / Q.card
        - ((A.filter fun x ↦ (r : ℝ) * ν ≤ φ x).card : ℝ) / A.card| ≤ β) :
    |averageOn Q φ - averageOn A φ| ≤ 2 * ν + 2 * β := by
  have h := abs_averageOn_sub_averageOn_le_of_levelSets hν hβ hQ hQne hrange hlevels
  nlinarith

/-- The trivial regime `1 < ν`: `[0,1]`-valued averages differ by at most `1 < 2ν`, with no
level-set hypothesis at all. -/
theorem abs_averageOn_sub_averageOn_le_of_one_lt {φ : α → ℝ} {A Q : Finset α} {ν : ℝ}
    (hν : 1 < ν) (hQ : Q ⊆ A) (hrange : ∀ x ∈ A, φ x ∈ Set.Icc (0 : ℝ) 1) :
    |averageOn Q φ - averageOn A φ| ≤ 2 * ν := by
  have hQr : averageOn Q φ ∈ Set.Icc (0 : ℝ) 1 :=
    averageOn_mem_Icc fun x hx ↦ hrange x (hQ hx)
  have hAr : averageOn A φ ∈ Set.Icc (0 : ℝ) 1 := averageOn_mem_Icc hrange
  rw [abs_le]
  obtain ⟨h1, h2⟩ := hQr
  obtain ⟨h3, h4⟩ := hAr
  constructor <;> linarith

/-! ### Tests and adversarial examples -/

section Tests

-- The empty set is almost constant at every tolerance — negative ones included
-- (totalization).
example : IsAlmostConstantOn (fun x : Fin 3 ↦ (x : ℝ)) (-1) (-1) (∅ : Finset (Fin 3)) :=
  isAlmostConstantOn_empty _ _ _

-- An empty rectangle side makes the pair almost constant outright.
example (f : RectKernel (Fin 2) (Fin 2)) (δ ε : ℝ) :
    IsAlmostConstantPair f δ ε ∅ Finset.univ := by
  unfold IsAlmostConstantPair
  rw [Finset.empty_product]
  exact isAlmostConstantOn_empty _ _ _

-- NOTE (adversarial, documented): **strictness of `< δ` is load-bearing.** The two-point
-- `0/1` indicator range is NOT `1`-constant — `|1 - 0| < 1` fails — so "1-constant" has
-- content; with a weak inequality it would be vacuous for every `[0,1]`-valued function.
example : ¬ IsDeltaConstantOn (fun x : Fin 2 ↦ (x.val : ℝ)) 1 Finset.univ := by
  intro h
  have := h 1 (Finset.mem_univ 1) 0 (Finset.mem_univ 0)
  norm_num at this

-- The `0/1`-valued function on two points is not `(1/4)`-almost `(1/2)`-constant: any subset
-- past three quarters of the mass contains both points.
example : ¬ IsAlmostConstantOn (fun x : Fin 2 ↦ (x.val : ℝ)) (1/2) (1/4) Finset.univ := by
  rintro (habs | ⟨W, hWV, hcard, hconst⟩)
  · exact absurd habs (by decide)
  · have h2 : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
    rw [h2] at hcard
    norm_num at hcard
    have hle : W.card ≤ 2 := le_trans (Finset.card_le_card hWV) (le_of_eq h2)
    have h2' : 2 ≤ W.card := by
      by_contra hlt
      push Not at hlt
      have : (W.card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
      linarith
    have hW2 : W = Finset.univ := Finset.eq_univ_of_card W (by simpa using le_antisymm hle h2')
    subst hW2
    have := hconst 1 (Finset.mem_univ 1) 0 (Finset.mem_univ 0)
    norm_num at this

end Tests

end RegularityLemmata
