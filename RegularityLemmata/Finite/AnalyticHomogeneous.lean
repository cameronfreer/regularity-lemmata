/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.AlmostConstant

/-!
# Analytic homogeneity

The `(δ, ε)`-homogeneous rectangle of Chavarria–Conant–Pillay, as restated by Conant–Terry
(*Quantitative analytic stable regularity*,
[arXiv:2607.21762](https://arxiv.org/abs/2607.21762), Definition A.1): `(A, B)` is
`(δ, ε)`-homogeneous for `f` when there are values `r, s ∈ [0,1]` such that, for `ε`-almost
all `a ∈ A`, the row `f a ·` is within `δ` of `r` on `ε`-almost all of `B`, and symmetrically
for columns at `s`. Their Proposition A.5 relates this to almost-constancy in both directions,
with a doubling of the `δ`-constant parameter:

* `RectKernel.isHomogeneousPair_of_isAlmostConstantPair` (A.5(a)): `ε²`-almost `2δ`-constant
  implies `(δ, ε)`-homogeneous;
* `RectKernel.isAlmostConstantPair_of_isHomogeneousPair` (A.5(b)): `(δ, ε)`-homogeneous
  implies `2ε`-almost `2δ`-constant.

## Frozen conventions

All predicates follow `Finite/AlmostConstant.lean`: **subset form**, **no decidability
instances**, **strict `<`** in the closeness and mass clauses, **totalized on the empty set**,
and **no range or sign constraint inside the predicates**. In particular:

* `IsAlmostNearOn φ r δ ε V` reads "for `ε`-almost all `v ∈ V`, `φ v ≈_δ r`"; here
  `x ≈_δ r` is `|x - r| < δ` (strict, the paper's footnote 8 convention).
* `RectKernel.IsRowConcentrated f r δ ε A B` totalizes **both** empty sides: with only
  `A = ∅` totalized, `B = ∅` with `A ≠ ∅` would fail the mass clause at `ε ≤ 0`.
* `RectKernel.IsHomogeneousPair` is the kernel notion, namespaced under `RectKernel` so it
  is never confused with the relational `IsHomogeneousPair`; no indicator adapter between
  the two is stated here.

## Provenance

Definition A.1 and both directions of Proposition A.5 are **reformulated variants**, not exact
formalizations: the constants are preserved (`ε²`/`2δ` in (a), `2ε`/`2δ` in (b)), but the
statements extend the domains (real-valued kernels, arbitrary real parameters, and (b) with
no hypothesis at all — for `ε > 1` the conclusion is the trivial regime), localize the range
assumption (to the rectangle, in (a) only, where it places the common value in `[0,1]`), and
totalize empty rectangles. The paper's "main observation" (a `δ`-constant function is within
`δ / 2` of a common center) is `isDeltaConstantOn_iff_exists_center` in
`Finite/AlmostConstant.lean`; (a) is then a row-wise Markov count and (b) a union-of-fibers
count.
-/

namespace RegularityLemmata

variable {α X Y : Type*} {φ : α → ℝ} {f : RectKernel X Y} {r δ δ' ε ε' : ℝ} {V : Finset α}
  {A : Finset X} {B : Finset Y}

/-! ### The predicates -/

/-- "For `ε`-almost all `v ∈ V`, `φ v ≈_δ r`": some subset carrying strictly more than a
`(1 − ε)`-fraction of `V` lies in the open `δ`-ball around `r`. Totalized on `V = ∅`. -/
def IsAlmostNearOn (φ : α → ℝ) (r δ ε : ℝ) (V : Finset α) : Prop :=
  V = ∅ ∨ ∃ W ⊆ V, (1 - ε) * (V.card : ℝ) < (W.card : ℝ) ∧ ∀ v ∈ W, |φ v - r| < δ

/-- Clause (i) of Definition A.1 at a fixed value `r`: for `ε`-almost all `a ∈ A`, the row
`f a ·` is `ε`-almost within `δ` of `r` on `B`. Totalized on **both** empty sides. -/
def RectKernel.IsRowConcentrated (f : RectKernel X Y) (r δ ε : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  A = ∅ ∨ B = ∅ ∨ ∃ A' ⊆ A, (1 - ε) * (A.card : ℝ) < (A'.card : ℝ) ∧
    ∀ a ∈ A', IsAlmostNearOn (fun b ↦ f a b) r δ ε B

/-- **Definition A.1**: `(A, B)` is `(δ, ε)`-homogeneous for `f` — row concentration at some
`r ∈ [0,1]`, and column concentration (row concentration of the transpose) at some
`s ∈ [0,1]`. -/
def RectKernel.IsHomogeneousPair (f : RectKernel X Y) (δ ε : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  (∃ r ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated f r δ ε A B) ∧
  (∃ s ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated (RectKernel.op f) s δ ε B A)

/-! ### Monotonicity and totalization -/

theorem IsAlmostNearOn.mono_delta (h : IsAlmostNearOn φ r δ ε V) (hδ : δ ≤ δ') :
    IsAlmostNearOn φ r δ' ε V := by
  rcases h with rfl | ⟨W, hWV, hcard, hnear⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨W, hWV, hcard, fun v hv ↦ lt_of_lt_of_le (hnear v hv) hδ⟩

theorem IsAlmostNearOn.mono_eps (h : IsAlmostNearOn φ r δ ε V) (hε : ε ≤ ε') :
    IsAlmostNearOn φ r δ ε' V := by
  rcases h with rfl | ⟨W, hWV, hcard, hnear⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨W, hWV, lt_of_le_of_lt ?_ hcard, hnear⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

theorem isAlmostNearOn_empty (φ : α → ℝ) (r δ ε : ℝ) : IsAlmostNearOn φ r δ ε (∅ : Finset α) :=
  Or.inl rfl

theorem RectKernel.IsRowConcentrated.mono_delta (h : RectKernel.IsRowConcentrated f r δ ε A B)
    (hδ : δ ≤ δ') : RectKernel.IsRowConcentrated f r δ' ε A B := by
  rcases h with hA | hB | ⟨A', hA'A, hcard, hrows⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr ⟨A', hA'A, hcard, fun a ha ↦ (hrows a ha).mono_delta hδ⟩)

theorem RectKernel.IsRowConcentrated.mono_eps (h : RectKernel.IsRowConcentrated f r δ ε A B)
    (hε : ε ≤ ε') : RectKernel.IsRowConcentrated f r δ ε' A B := by
  rcases h with hA | hB | ⟨A', hA'A, hcard, hrows⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · refine Or.inr (Or.inr ⟨A', hA'A, lt_of_le_of_lt ?_ hcard, fun a ha ↦ (hrows a ha).mono_eps hε⟩)
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

theorem rectKernel_isRowConcentrated_empty_left (f : RectKernel X Y) (r δ ε : ℝ)
    (B : Finset Y) : RectKernel.IsRowConcentrated f r δ ε ∅ B :=
  Or.inl rfl

theorem rectKernel_isRowConcentrated_empty_right (f : RectKernel X Y) (r δ ε : ℝ)
    (A : Finset X) : RectKernel.IsRowConcentrated f r δ ε A ∅ :=
  Or.inr (Or.inl rfl)

theorem RectKernel.IsHomogeneousPair.mono_delta (h : RectKernel.IsHomogeneousPair f δ ε A B)
    (hδ : δ ≤ δ') : RectKernel.IsHomogeneousPair f δ' ε A B :=
  ⟨let ⟨r, hr, hrow⟩ := h.1; ⟨r, hr, hrow.mono_delta hδ⟩,
   let ⟨s, hs, hcol⟩ := h.2; ⟨s, hs, hcol.mono_delta hδ⟩⟩

theorem RectKernel.IsHomogeneousPair.mono_eps (h : RectKernel.IsHomogeneousPair f δ ε A B)
    (hε : ε ≤ ε') : RectKernel.IsHomogeneousPair f δ ε' A B :=
  ⟨let ⟨r, hr, hrow⟩ := h.1; ⟨r, hr, hrow.mono_eps hε⟩,
   let ⟨s, hs, hcol⟩ := h.2; ⟨s, hs, hcol.mono_eps hε⟩⟩

/-- **Exact transpose law**: swap the two clauses. -/
theorem RectKernel.isHomogeneousPair_op_iff :
    RectKernel.IsHomogeneousPair (RectKernel.op f) δ ε B A ↔
      RectKernel.IsHomogeneousPair f δ ε A B :=
  ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

theorem rectKernel_isHomogeneousPair_empty_left (f : RectKernel X Y) (δ ε : ℝ) (B : Finset Y) :
    RectKernel.IsHomogeneousPair f δ ε ∅ B :=
  ⟨⟨0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩⟩

theorem rectKernel_isHomogeneousPair_empty_right (f : RectKernel X Y) (δ ε : ℝ)
    (A : Finset X) : RectKernel.IsHomogeneousPair f δ ε A ∅ :=
  ⟨⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl⟩⟩

/-! ### Proposition A.5(a): almost constant ⇒ homogeneous -/

/-- The row half of A.5(a): from an `ε²`-almost `2δ`-constant rectangle, a value `r ∈ [0,1]`
at which the rows are concentrated. The common value is the center of the `2δ`-constant
witness; a row is good when it meets the witness in more than a `(1 − ε)`-fraction of `B`,
and the complement of the witness (fewer than `ε²|A||B|` points) contains at least `ε|B|`
points of every bad row, so fewer than `ε|A|` rows are bad. -/
private theorem RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair (hε : 0 < ε)
    (hrange : IsUnitIntervalOnRectangle f A B)
    (h : IsAlmostConstantPair f (2 * δ) (ε * ε) A B) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated f r δ ε A B := by
  classical
  rcases h with hAB | ⟨W, hWAB, hcard, hconst⟩
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rcases Finset.product_eq_empty.mp hAB with hA | hB
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩
  have hrangeW : ∀ p ∈ W, (fun p : X × Y ↦ f p.1 p.2) p ∈ Set.Icc (0 : ℝ) 1 := fun p hp ↦ by
    have hp' := Finset.mem_product.mp (hWAB hp)
    exact hrange p.1 hp'.1 p.2 hp'.2
  obtain ⟨r, hr, hnear⟩ := hconst.exists_center_mem_Icc hrangeW
  have hnear' : ∀ p ∈ W, |f p.1 p.2 - r| < δ := fun p hp ↦ by
    have := hnear p hp
    rwa [show 2 * δ / 2 = δ by ring] at this
  refine ⟨r, hr, ?_⟩
  -- the fiber of the witness over a row, and its projection to `B`
  set fib : X → Finset (X × Y) := fun a ↦ W.filter (fun p ↦ p.1 = a) with hfib
  set Wa : X → Finset Y := fun a ↦ (fib a).image Prod.snd with hWa
  have hWa_card : ∀ a, (Wa a).card = (fib a).card := fun a ↦
    Finset.card_image_of_injOn (fun p hp q hq hpq ↦ by
      have hp1 := (Finset.mem_filter.mp hp).2
      have hq1 := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hp1.trans hq1.symm) hpq)
  have hWa_sub : ∀ a, Wa a ⊆ B := fun a b hb ↦ by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_product.mp (hWAB (Finset.mem_filter.mp hp).1)).2
  have hWa_near : ∀ a, ∀ b ∈ Wa a, |f a b - r| < δ := fun a b hb ↦ by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hpW, hpa⟩ := Finset.mem_filter.mp hp
    have := hnear' p hpW
    rwa [hpa] at this
  have hfib_le : ∀ a, (fib a).card ≤ B.card := fun a ↦ by
    rw [← hWa_card]
    exact Finset.card_le_card (hWa_sub a)
  set good : X → Prop := fun a ↦ (1 - ε) * (B.card : ℝ) < ((fib a).card : ℝ) with hgood
  refine Or.inr (Or.inr ⟨A.filter good, Finset.filter_subset _ _, ?_, fun a ha ↦ ?_⟩)
  · -- Markov: the witness is covered by the good rows (at most `|B|` each) and the bad rows
    -- (at most `(1 − ε)|B|` each).
    have hsum : (W.card : ℝ) = ∑ a ∈ A, ((fib a).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)
        (fun p hp ↦ (Finset.mem_product.mp (hWAB hp)).1)]
      push_cast
      rfl
    have hsplit := Finset.sum_filter_add_sum_filter_not A good (fun a ↦ ((fib a).card : ℝ))
    have hgoodsum : ∑ a ∈ A.filter good, ((fib a).card : ℝ) ≤
        ((A.filter good).card : ℝ) * B.card := by
      have := Finset.sum_le_card_nsmul (A.filter good) (fun a ↦ ((fib a).card : ℝ)) (B.card : ℝ)
        (fun a _ ↦ by exact_mod_cast hfib_le a)
      simpa [nsmul_eq_mul] using this
    have hbadsum : ∑ a ∈ A.filter (fun a ↦ ¬ good a), ((fib a).card : ℝ) ≤
        ((A.filter (fun a ↦ ¬ good a)).card : ℝ) * ((1 - ε) * B.card) := by
      have := Finset.sum_le_card_nsmul (A.filter (fun a ↦ ¬ good a))
        (fun a ↦ ((fib a).card : ℝ)) ((1 - ε) * B.card)
        (fun a ha ↦ not_lt.mp (Finset.mem_filter.mp ha).2)
      simpa [nsmul_eq_mul] using this
    have hcount : ((A.filter good).card : ℝ) + ((A.filter (fun a ↦ ¬ good a)).card : ℝ) =
        A.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not good
    have hbad : ((A.filter (fun a ↦ ¬ good a)).card : ℝ) = A.card - (A.filter good).card := by
      linarith
    rw [hbad] at hbadsum
    rw [Finset.card_product] at hcard
    push_cast at hcard
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
    have key : ε * B.card * ((1 - ε) * A.card) < ε * B.card * ((A.filter good).card : ℝ) := by
      nlinarith
    exact lt_of_mul_lt_mul_left key (by positivity)
  · exact Or.inr ⟨Wa a, hWa_sub a, by rw [hWa_card]; exact (Finset.mem_filter.mp ha).2,
      hWa_near a⟩

/-- **Proposition A.5(a)** (reformulated variant): an `ε²`-almost `2δ`-constant rectangle is
`(δ, ε)`-homogeneous. The range hypothesis places the common values in `[0,1]`; the column
clause is the row clause of the transpose, through `isAlmostConstantPair_op_iff`. -/
theorem RectKernel.isHomogeneousPair_of_isAlmostConstantPair (hε : 0 < ε)
    (hrange : IsUnitIntervalOnRectangle f A B)
    (h : IsAlmostConstantPair f (2 * δ) (ε * ε) A B) :
    RectKernel.IsHomogeneousPair f δ ε A B :=
  ⟨RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair hε hrange h,
   RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair hε
    (fun y hy x hx ↦ hrange x hx y hy) (isAlmostConstantPair_op_iff.mpr h)⟩

/-! ### Proposition A.5(b): homogeneous ⇒ almost constant -/

/-- **Proposition A.5(b)** (reformulated variant, no hypotheses): a `(δ, ε)`-homogeneous
rectangle is `2ε`-almost `2δ`-constant. Only the row clause is used: the union over the good
rows of their good column sets has more than `(1 − ε)²|A||B| ≥ (1 − 2ε)|A||B|` points when
`ε ≤ 1`, and for `ε > 1` the conclusion is the trivial regime. -/
theorem RectKernel.isAlmostConstantPair_of_isHomogeneousPair
    (h : RectKernel.IsHomogeneousPair f δ ε A B) :
    IsAlmostConstantPair f (2 * δ) (2 * ε) A B := by
  classical
  obtain ⟨⟨r, -, hrow⟩, -⟩ := h
  rcases hrow with hA | hB | ⟨A', hA'A, hcardA, hrows⟩
  · exact Or.inl (by rw [hA, Finset.empty_product])
  · exact Or.inl (by rw [hB, Finset.product_empty])
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact Or.inl (Finset.product_empty A)
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact Or.inl (Finset.empty_product B)
  have hchoice : ∀ a : X, ∃ Wa : Finset Y, a ∈ A' →
      Wa ⊆ B ∧ (1 - ε) * (B.card : ℝ) < (Wa.card : ℝ) ∧ ∀ b ∈ Wa, |f a b - r| < δ := fun a ↦ by
    by_cases ha : a ∈ A'
    · rcases hrows a ha with hB' | ⟨Wa, hWaB, hcard, hnear⟩
      · exact absurd hB' hB.ne_empty
      · exact ⟨Wa, fun _ ↦ ⟨hWaB, hcard, hnear⟩⟩
    · exact ⟨∅, fun h ↦ absurd h ha⟩
  choose Wa hWa using hchoice
  refine Or.inr ⟨A'.biUnion (fun a ↦ {a} ×ˢ Wa a), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    rw [Finset.mem_product, Finset.mem_singleton] at hp
    obtain ⟨rfl, hb⟩ := hp
    exact Finset.mem_product.mpr ⟨hA'A ha, (hWa _ ha).1 hb⟩
  · have hdisj : (A' : Set X).PairwiseDisjoint (fun a ↦ ({a} : Finset X) ×ˢ Wa a) := by
      intro a _ a' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      rw [Finset.mem_product, Finset.mem_singleton] at hp hp'
      exact hne (hp.1.symm.trans hp'.1)
    rw [Finset.card_biUnion hdisj, Finset.card_product]
    push_cast
    simp only [Finset.card_product, Finset.card_singleton, one_mul]
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
    by_cases hε1 : ε ≤ 1
    · have hA'ne : A'.Nonempty := by
        rw [← Finset.card_pos]
        have h0 : (0 : ℝ) ≤ (1 - ε) * A.card := mul_nonneg (by linarith) hA0
        exact_mod_cast lt_of_le_of_lt h0 hcardA
      have hsum : (A'.card : ℝ) * ((1 - ε) * B.card) < ∑ a ∈ A', ((Wa a).card : ℝ) := by
        have := Finset.sum_lt_sum_of_nonempty hA'ne (fun a ha ↦ (hWa a ha).2.1)
        simpa [Finset.sum_const, nsmul_eq_mul] using this
      have hB1 : (0 : ℝ) ≤ (1 - ε) * B.card := mul_nonneg (by linarith) hB0
      have h1 : (1 - ε) * A.card * ((1 - ε) * B.card) ≤ A'.card * ((1 - ε) * B.card) :=
        mul_le_mul_of_nonneg_right hcardA.le hB1
      nlinarith [mul_nonneg (mul_nonneg hA0 hB0) (sq_nonneg ε)]
    · have hε1 := not_le.mp hε1
      have hpos : (0 : ℝ) < A.card * B.card :=
        mul_pos (by exact_mod_cast Finset.card_pos.mpr hA)
          (by exact_mod_cast Finset.card_pos.mpr hB)
      have hneg : (1 - 2 * ε) * (A.card * B.card) < 0 := by nlinarith
      exact lt_of_lt_of_le hneg (Finset.sum_nonneg fun a _ ↦ Nat.cast_nonneg _)
  · intro p hp p' hp'
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a', ha', hp'⟩ := Finset.mem_biUnion.mp hp'
    rw [Finset.mem_product, Finset.mem_singleton] at hp hp'
    obtain ⟨rfl, hb⟩ := hp
    obtain ⟨rfl, hb'⟩ := hp'
    have h1 := (hWa _ ha).2.2 _ hb
    have h2 := (hWa _ ha').2.2 _ hb'
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Tests and adversarial examples -/

section Tests

-- Totalization: all three predicates hold on empty sides, unconditionally in the parameters.
example (φ : α → ℝ) (r δ ε : ℝ) : IsAlmostNearOn φ r δ ε (∅ : Finset α) :=
  isAlmostNearOn_empty φ r δ ε

-- The case a one-sided totalization would get wrong: `B = ∅`, `A ≠ ∅`, `ε = 0`.
example (f : RectKernel (Fin 2) (Fin 2)) (r δ : ℝ) :
    RectKernel.IsRowConcentrated f r δ 0 Finset.univ ∅ :=
  rectKernel_isRowConcentrated_empty_right f r δ 0 Finset.univ

example (f : RectKernel X Y) (δ ε : ℝ) (B : Finset Y) :
    RectKernel.IsHomogeneousPair f δ ε ∅ B :=
  rectKernel_isHomogeneousPair_empty_left f δ ε B

-- Transpose round trips at `op (op f) = f`.
example (f : RectKernel X Y) (δ ε : ℝ) (A : Finset X) (B : Finset Y) :
    RectKernel.IsHomogeneousPair (RectKernel.op (RectKernel.op f)) δ ε A B ↔
      RectKernel.IsHomogeneousPair f δ ε A B :=
  RectKernel.isHomogeneousPair_op_iff.trans RectKernel.isHomogeneousPair_op_iff

example (f : RectKernel X Y) (δ ε : ℝ) (A : Finset X) (B : Finset Y) :
    IsAlmostConstantPair (RectKernel.op (RectKernel.op f)) δ ε A B ↔
      IsAlmostConstantPair f δ ε A B :=
  isAlmostConstantPair_op_iff.trans isAlmostConstantPair_op_iff

-- The centered characterization on the empty set (center `0`) …
example (φ : α → ℝ) (δ : ℝ) : ∃ r : ℝ, ∀ v ∈ (∅ : Finset α), |φ v - r| < δ / 2 :=
  isDeltaConstantOn_iff_exists_center.mp (isDeltaConstantOn_empty φ δ)

-- … and on a two-point set, where the center is the midpoint.
example : IsDeltaConstantOn (fun i : Fin 2 ↦ (i : ℝ)) (3 / 2) Finset.univ :=
  isDeltaConstantOn_iff_exists_center.mpr ⟨1 / 2, by
    intro v _
    fin_cases v <;> norm_num [abs_lt]⟩

/-- The `2 × 2` sharpness kernel: three entries `0`, one outlier `1`. -/
private def outlierKernel : RectKernel (Fin 2) (Fin 2) := fun a b ↦ if a = 1 ∧ b = 1 then 1 else 0

-- It is `1/2`-almost `1/2`-constant (three of four points; `3 > (1 − 1/2)·4 = 2`, strictly) …
example : IsAlmostConstantPair outlierKernel (1 / 2) (1 / 2) Finset.univ Finset.univ := by
  refine Or.inr ⟨(Finset.univ ×ˢ Finset.univ).filter (fun p ↦ ¬ (p.1 = 1 ∧ p.2 = 1)),
    Finset.filter_subset _ _, ?_, ?_⟩
  · have h3 : ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin 2 × Fin 2 ↦ ¬ (p.1 = 1 ∧ p.2 = 1))).card = 3 := by decide
    have h4 : ((Finset.univ : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin 2))).card = 4 := by
      decide
    rw [h3, h4]
    norm_num
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hab hab'
  simp [outlierKernel, hab, hab']

-- … but not `(1/4, 1/2)`-homogeneous: with `ε = 1/2` both rows must be good and both entries
-- of a good row must lie within `1/4` of the same center, which the outlier row cannot do. So
-- `ε`-almost (rather than `ε²`-almost) `2δ`-constancy does not give `(δ, ε)`-homogeneity.
example : ¬ RectKernel.IsHomogeneousPair outlierKernel (1 / 4) (1 / 2) Finset.univ Finset.univ := by
  rintro ⟨⟨r, -, hrow⟩, -⟩
  rcases hrow with hA | hB | ⟨A', -, hcard, hrows⟩
  · exact absurd hA (by decide)
  · exact absurd hB (by decide)
  have hA' : A' = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h2 : A'.card ≤ 2 := le_trans (Finset.card_le_univ A') (by simp)
    norm_num at hcard
    have : 1 < A'.card := by exact_mod_cast hcard
    simp; omega
  subst hA'
  rcases hrows 1 (Finset.mem_univ _) with hB | ⟨W, -, hcardW, hnear⟩
  · exact absurd hB (by decide)
  have hW : W = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h2 : W.card ≤ 2 := le_trans (Finset.card_le_univ W) (by simp)
    norm_num at hcardW
    have : 1 < W.card := by exact_mod_cast hcardW
    simp; omega
  subst hW
  have h0 := hnear 0 (Finset.mem_univ _)
  have h1 := hnear 1 (Finset.mem_univ _)
  simp [outlierKernel, abs_lt] at h0 h1
  linarith [h0.1, h0.2, h1.1, h1.2]

-- A `[0,1]` witness for (b) at `ε = 1/4`: the constant kernel `1/2` is `(δ, 1/4)`-homogeneous
-- for every positive `δ`, hence `1/2`-almost `2δ`-constant.
example {δ : ℝ} (hδ : 0 < δ) :
    IsAlmostConstantPair (fun (_ : Fin 2) (_ : Fin 2) ↦ (1 / 2 : ℝ)) (2 * δ) (2 * (1 / 4))
      Finset.univ Finset.univ :=
  RectKernel.isAlmostConstantPair_of_isHomogeneousPair (by
    have hrow : RectKernel.IsRowConcentrated (fun (_ : Fin 2) (_ : Fin 2) ↦ (1 / 2 : ℝ))
        (1 / 2) δ (1 / 4) Finset.univ Finset.univ :=
      Or.inr (Or.inr ⟨Finset.univ, Finset.Subset.rfl, by norm_num, fun a _ ↦
        Or.inr ⟨Finset.univ, Finset.Subset.rfl, by norm_num, fun b _ ↦ by simpa using hδ⟩⟩)
    exact ⟨⟨1 / 2, by norm_num, hrow⟩, ⟨1 / 2, by norm_num, hrow⟩⟩)

end Tests

end RegularityLemmata
