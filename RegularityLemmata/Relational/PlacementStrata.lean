/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.RepresentativeSelection
import RegularityLemmata.Relational.ThreeVertexCounting
import RegularityLemmata.Relational.DiagonalGate

/-!
# Phase 11 unit 8: the stratum-uniform certificate on representative boxes

The final feasibility unit before the 11A→11B checkpoint (Phase 11 design freeze in
`ARCHITECTURE.md`), in the frozen order: the abstract representative-box certificate
under `ρ > 0` and `7·τ < ρ³` with an explicit host-size inequality absorbing the
collision slack; the slack bound for representative boxes (where the fine-part bound
`q` legitimately enters the LARGE-HOST CUTOFF — and nothing else); the stratum-uniform
instantiation, deliberately **generic in the boxes** so that no placement stratum
needs a disjointness or literal-box-equality hypothesis the representatives do not
supply; the relational certificate through the no-disjointness bridge
`inducedEmbeddingCountOn_three_eq_injectiveTriangleCount`, with nullaries, profiles,
and palette orientations checked explicitly (the reverse orientations are supplied by
the PROVED reversal law inside the bridge, never by an assumption); and the
viable-constants package, separate from the counting proof, with the quantifier order
visible — constants depend on the fixed language and the budget parameter only, never
on the pattern family or the carrier.

**Hard stops, checked**: `ρ = min(θ, 1/K) − η > 0` and `7τ < ρ³` hold by the
constants package; the selection tolerance remains `q`-free (this file adds `q` only
in the host cutoff `48·q < ρ³·α·n`); asymmetric diagonal palettes need no unproved
orientation assumption; and every placement stratum is covered by one generic
statement.
-/

namespace RegularityLemmata

open FirstOrder

/-! ### The abstract representative-box certificate -/

section Abstract

variable {α : Type*} [DecidableEq α]
  (R₀₁ R₀₂ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂]

/-- Density transfer: an `η`-close density inherits a coarse floor at an `η` loss. -/
theorem le_of_coarse_of_close {d D m₀ η : ℝ} (hD : m₀ ≤ D) (hclose : |d - D| ≤ η) :
    m₀ - η ≤ d := by
  have := abs_le.mp hclose
  linarith

/-- **The abstract quantitative certificate**: `ρ`-dense `τ`-uniform boxes (arbitrary,
possibly coinciding) carry at least `(ρ³ − 7τ)·|A₀||A₁||A₂| − slack` injective
realizations. -/
theorem injectiveTriangleCount_ge_of_dense_uniform {A₀ A₁ A₂ : Finset α} {ρ τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 ≤ ρ)
    (h01u : IsUniformPair R₀₁ A₀ A₁ τ) (h02u : IsUniformPair R₀₂ A₀ A₂ τ)
    (h12u : IsUniformPair R₁₂ A₁ A₂ τ)
    (h01d : ρ ≤ pairDensity R₀₁ A₀ A₁) (h02d : ρ ≤ pairDensity R₀₂ A₀ A₂)
    (h12d : ρ ≤ pairDensity R₁₂ A₁ A₂) :
    (ρ ^ 3 - 7 * τ) * (A₀.card * A₁.card * A₂.card)
        - ((A₀ ∩ A₁).card * A₂.card + (A₀ ∩ A₂).card * A₁.card
          + A₀.card * (A₁ ∩ A₂).card)
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A₀ A₁ A₂ : ℝ) := by
  have hbase := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hτ0 hτ1 h01u h02u h12u
  have hprod : ρ ^ 3 ≤ pairDensity R₀₁ A₀ A₁ * pairDensity R₀₂ A₀ A₂
      * pairDensity R₁₂ A₁ A₂ := by
    have h1 : ρ * ρ ≤ pairDensity R₀₁ A₀ A₁ * pairDensity R₀₂ A₀ A₂ :=
      mul_le_mul h01d h02d hρ (le_trans hρ h01d)
    have h2 : ρ * ρ * ρ ≤ pairDensity R₀₁ A₀ A₁ * pairDensity R₀₂ A₀ A₂
        * pairDensity R₁₂ A₁ A₂ :=
      mul_le_mul h1 h12d hρ (mul_nonneg (le_trans hρ h01d) (le_trans hρ h02d))
    calc ρ ^ 3 = ρ * ρ * ρ := by ring
      _ ≤ _ := h2
  have hvolnn : (0 : ℝ) ≤ (A₀.card : ℝ) * A₁.card * A₂.card := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hprod hvolnn]

/-- **The slack bound for representative boxes**, in multiplication form: with size
floors `α·n ≤ 2q·|Aᵢ|`, the collision slack satisfies `slack·(α·n) ≤ 6·q·vol`. This
is the ONLY place the fine-part bound `q` enters Unit 8 — the large-host cutoff, never
the witness tolerance. -/
theorem collisionSlack_mul_le {A₀ A₁ A₂ : Finset α} {q : ℕ} {a n : ℝ}
    (h0 : a * n ≤ 2 * q * A₀.card) (h1 : a * n ≤ 2 * q * A₁.card)
    (han : 0 ≤ a * n) :
    ((A₀ ∩ A₁).card * A₂.card + (A₀ ∩ A₂).card * A₁.card
        + A₀.card * (A₁ ∩ A₂).card : ℝ) * (a * n)
      ≤ 6 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by
  have hι01 : ((A₀ ∩ A₁).card : ℝ) ≤ A₁.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hι02 : ((A₀ ∩ A₂).card : ℝ) ≤ A₂.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hι12 : ((A₁ ∩ A₂).card : ℝ) ≤ A₂.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have t1 : ((A₀ ∩ A₁).card : ℝ) * A₂.card * (a * n)
      ≤ 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by
    calc ((A₀ ∩ A₁).card : ℝ) * A₂.card * (a * n)
        ≤ ((A₁.card : ℝ) * A₂.card) * (2 * q * A₀.card) := by
          have hnn : (0 : ℝ) ≤ ((A₀ ∩ A₁).card : ℝ) * A₂.card := by positivity
          have h1' : ((A₀ ∩ A₁).card : ℝ) * A₂.card ≤ (A₁.card : ℝ) * A₂.card :=
            mul_le_mul_of_nonneg_right hι01 (Nat.cast_nonneg _)
          exact mul_le_mul h1' h0 han (by positivity)
      _ = 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by ring
  have t2 : ((A₀ ∩ A₂).card : ℝ) * A₁.card * (a * n)
      ≤ 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by
    calc ((A₀ ∩ A₂).card : ℝ) * A₁.card * (a * n)
        ≤ ((A₂.card : ℝ) * A₁.card) * (2 * q * A₀.card) := by
          have h1' : ((A₀ ∩ A₂).card : ℝ) * A₁.card ≤ (A₂.card : ℝ) * A₁.card :=
            mul_le_mul_of_nonneg_right hι02 (Nat.cast_nonneg _)
          exact mul_le_mul h1' h0 han (by positivity)
      _ = 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by ring
  have t3 : (A₀.card : ℝ) * (A₁ ∩ A₂).card * (a * n)
      ≤ 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by
    calc (A₀.card : ℝ) * (A₁ ∩ A₂).card * (a * n)
        ≤ ((A₀.card : ℝ) * A₂.card) * (2 * q * A₁.card) := by
          have h1' : (A₀.card : ℝ) * (A₁ ∩ A₂).card ≤ (A₀.card : ℝ) * A₂.card :=
            mul_le_mul_of_nonneg_left hι12 (Nat.cast_nonneg _)
          exact mul_le_mul h1' h1 han (by positivity)
      _ = 2 * q * ((A₀.card : ℝ) * A₁.card * A₂.card) := by ring
  nlinarith [t1, t2, t3]

/-- **The abstract positivity certificate.** Under `ρ`-density, `τ`-uniformity, the
size floors, and the explicit host-size inequality `6·q < (ρ³ − 7τ)·α·n`, the
injective count is strictly positive — for ARBITRARY boxes: no placement stratum
needs a disjointness or literal-equality hypothesis. -/
theorem injectiveTriangleCount_pos_of_dense_uniform {A₀ A₁ A₂ : Finset α}
    {ρ τ : ℝ} {q : ℕ} {a n : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 ≤ ρ) (han : 0 < a * n)
    (h01u : IsUniformPair R₀₁ A₀ A₁ τ) (h02u : IsUniformPair R₀₂ A₀ A₂ τ)
    (h12u : IsUniformPair R₁₂ A₁ A₂ τ)
    (h01d : ρ ≤ pairDensity R₀₁ A₀ A₁) (h02d : ρ ≤ pairDensity R₀₂ A₀ A₂)
    (h12d : ρ ≤ pairDensity R₁₂ A₁ A₂)
    (h0 : a * n ≤ 2 * q * A₀.card) (h1 : a * n ≤ 2 * q * A₁.card)
    (h2 : a * n ≤ 2 * q * A₂.card)
    (hhost : 6 * q < (ρ ^ 3 - 7 * τ) * (a * n)) :
    0 < injectiveTriangleCount R₀₁ R₀₂ R₁₂ A₀ A₁ A₂ := by
  have hcard0 : (0 : ℝ) < A₀.card := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) * q * A₀.card ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    linarith
  have hcard1 : (0 : ℝ) < A₁.card := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) * q * A₁.card ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    linarith
  have hcard2 : (0 : ℝ) < A₂.card := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) * q * A₂.card ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    linarith
  have hvolpos : (0 : ℝ) < (A₀.card : ℝ) * A₁.card * A₂.card := by positivity
  have hbase := injectiveTriangleCount_ge_of_dense_uniform R₀₁ R₀₂ R₁₂
    hτ0 hτ1 hρ h01u h02u h12u h01d h02d h12d
  have hslack := collisionSlack_mul_le (A₂ := A₂) h0 h1 (le_of_lt han)
  -- `slack·(αn) ≤ 6q·vol < (ρ³−7τ)·(αn)·vol` forces `slack < (ρ³−7τ)·vol`.
  have hkey : ((A₀ ∩ A₁).card * A₂.card + (A₀ ∩ A₂).card * A₁.card
      + A₀.card * (A₁ ∩ A₂).card : ℝ)
      < (ρ ^ 3 - 7 * τ) * ((A₀.card : ℝ) * A₁.card * A₂.card) := by
    have hstep : (6 : ℝ) * q * ((A₀.card : ℝ) * A₁.card * A₂.card)
        < (ρ ^ 3 - 7 * τ) * (a * n) * ((A₀.card : ℝ) * A₁.card * A₂.card) :=
      mul_lt_mul_of_pos_right hhost hvolpos
    have := lt_of_le_of_lt hslack hstep
    have hrw : (ρ ^ 3 - 7 * τ) * (a * n) * ((A₀.card : ℝ) * A₁.card * A₂.card)
        = (ρ ^ 3 - 7 * τ) * ((A₀.card : ℝ) * A₁.card * A₂.card) * (a * n) := by
      ring
    rw [hrw] at this
    exact lt_of_mul_lt_mul_right this (le_of_lt han)
  have hpos : (0 : ℝ) < (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A₀ A₁ A₂ : ℝ) := by
    linarith
  exact_mod_cast hpos

end Abstract

/-! ### The relational certificate on representative boxes -/

section Relational

variable {V : Type*} [DecidableEq V] {s : Finset V}
variable {L : FirstOrder.Language} [FiniteRelational L]

/-- **The relational representative-box certificate.** Through the no-disjointness
bridge: for profile-matching (possibly overlapping or coinciding) boxes whose three
FORWARD required palettes are `ρ`-dense and `τ`-uniform, with the size floors and the
host-size inequality, the induced three-vertex count is strictly positive. The
nullary compatibility and the three profile matchings are explicit hypotheses; the
REVERSE palette orientations are supplied by the proved reversal law inside
`preservesAndReflects_three_iff` — no orientation assumption is made. -/
theorem inducedEmbeddingCountOn_pos_of_representatives [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A₀ A₁ A₂ : Finset V}
    {ρ τ : ℝ} {q : ℕ} {a n : ℝ}
    (hnull : NullaryCompatible P M)
    (hprof0 : ∀ v ∈ A₀, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hprof1 : ∀ v ∈ A₁, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hprof2 : ∀ v ∈ A₂, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 ≤ ρ) (han : 0 < a * n)
    (h01u : IsUniformPair
      (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A₀ A₁ τ)
    (h02u : IsUniformPair
      (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A₀ A₂ τ)
    (h12u : IsUniformPair
      (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A₁ A₂ τ)
    (h01d : ρ ≤ pairDensity
      (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A₀ A₁)
    (h02d : ρ ≤ pairDensity
      (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A₀ A₂)
    (h12d : ρ ≤ pairDensity
      (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A₁ A₂)
    (h0 : a * n ≤ 2 * q * A₀.card) (h1 : a * n ≤ 2 * q * A₁.card)
    (h2 : a * n ≤ 2 * q * A₂.card)
    (hhost : 6 * q < (ρ ^ 3 - 7 * τ) * (a * n)) :
    0 < inducedEmbeddingCountOn P M ![A₀, A₁, A₂] := by
  rw [inducedEmbeddingCountOn_three_eq_injectiveTriangleCount hnull
    hprof0 hprof1 hprof2]
  exact injectiveTriangleCount_pos_of_dense_uniform _ _ _
    hτ0 hτ1 hρ han h01u h02u h12u h01d h02d h12d h0 h1 h2 hhost

/-- **The global count decomposes exactly over the five placement strata** of coarse
cell triples — the promised glue between the Unit 6 combinatorics and the global
counting surface. -/
theorem globalInducedCount_eq_sum_placementClass [AtMostBinary L] [Fintype V]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} (Q : Finpartition s) :
    ∑ c : PlacementClass,
      ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter
          (fun T => placementClass T = c),
        inducedEmbeddingCountOn P M T
      = globalInducedCount P M Q := by
  rw [globalInducedCount]
  exact sum_placementClass_fiberwise _ _

end Relational

/-! ### The viable-constants package -/

/-- **Viable constants exist**, with the quantifier order visible: the language
enters through the palette count `K`, the budget through the free parameter `θ`; the
derived `η`, `τ`, `ρ` depend on those alone — never on a pattern family or a carrier;
and the host-size inequality is a pure large-host cutoff in which the fine-part bound
`q` legitimately appears. Witnesses: `η = θ/2`, `τ = ρ³/8`. -/
theorem exists_viable_constants (K : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθK : θ ≤ 1 / K) :
    ∃ η τ ρ : ℝ, 0 < η ∧ 0 < τ ∧ ρ = min θ (1 / K) - η ∧ 0 < ρ ∧ 7 * τ < ρ ^ 3 ∧
      ∀ (q : ℕ) (a n : ℝ), 48 * q < ρ ^ 3 * (a * n) →
        6 * q < (ρ ^ 3 - 7 * τ) * (a * n) := by
  refine ⟨θ / 2, (θ / 2) ^ 3 / 8, θ / 2, by positivity, by positivity, ?_, by positivity,
    ?_, ?_⟩
  · rw [min_eq_left hθK]
    ring
  · nlinarith [pow_pos (by positivity : (0 : ℝ) < θ / 2) 3]
  · intro q a n hq
    nlinarith [hq]

/-! ### Tests and adversarial examples -/

section Tests

-- The constants package computes at the graph language (`K = 4`): `θ = 1/4` is
-- admissible and the package delivers `ρ = 1/8` with all inequalities strict.
example : ∃ η τ ρ : ℝ, 0 < η ∧ 0 < τ ∧ ρ = min (1 / 4 : ℝ) (1 / 4) - η ∧ 0 < ρ ∧
    7 * τ < ρ ^ 3 ∧ ∀ (q : ℕ) (a n : ℝ), 48 * q < ρ ^ 3 * (a * n) →
      6 * q < (ρ ^ 3 - 7 * τ) * (a * n) :=
  exists_viable_constants 4 (by norm_num) (by norm_num)

-- **Stratum-independence, adversarially**: the abstract positivity certificate is
-- stated for arbitrary boxes — here it is consumed with all three boxes literally
-- EQUAL (the all-equal placement stratum), with no disjointness available anywhere.
example {V : Type*} [DecidableEq V] (R : V → V → Prop) [DecidableRel R] {A : Finset V}
    {ρ τ : ℝ} {q : ℕ} {a n : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 ≤ ρ)
    (han : 0 < a * n) (hu : IsUniformPair R A A τ) (hd : ρ ≤ pairDensity R A A)
    (h0 : a * n ≤ 2 * q * A.card) (hhost : 6 * q < (ρ ^ 3 - 7 * τ) * (a * n)) :
    0 < injectiveTriangleCount R R R A A A :=
  injectiveTriangleCount_pos_of_dense_uniform R R R hτ0 hτ1 hρ han
    hu hu hu hd hd hd h0 h0 h0 hhost

-- The density-transfer arithmetic, concretely: a coarse floor `1/4` on `D = 1/2`
-- transfers to the `η = 1/8`-close `d = 3/8` at an `η` loss.
example : ((1 : ℝ) / 4) - 1 / 8 ≤ 3 / 8 :=
  le_of_coarse_of_close (d := 3 / 8) (D := 1 / 2) (by norm_num) (by norm_num [abs_le])

end Tests

end RegularityLemmata
