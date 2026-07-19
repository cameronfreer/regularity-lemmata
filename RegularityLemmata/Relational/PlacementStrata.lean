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

/-! ### Palette orientation transports -/

section Orientation

variable {V : Type*} [DecidableEq V] {L : FirstOrder.Language} [FiniteRelational L]

omit [DecidableEq V] in
/-- The swapped palette, pointwise: `a, b` carry the swap of `c` exactly when `b, a`
carry `c`. -/
theorem hasBinaryPairPalette_swap_iff (M : FiniteRelModel L V)
    (c : BinaryPairPalette L) {a b : V} :
    HasBinaryPairPalette M (swapBinaryPairPalette c) a b
      ↔ HasBinaryPairPalette M c b a := by
  constructor
  · intro h
    show binaryPairPalette M b a = c
    rw [binaryPairPalette_swap M a b, h]
    exact swapBinaryPairPalette_involutive c
  · intro h
    show binaryPairPalette M a b = swapBinaryPairPalette c
    rw [binaryPairPalette_swap M b a, h]

omit [DecidableEq V] in
/-- The swapped palette, as a relation: it is the ordered reversal. -/
theorem hasBinaryPairPalette_swap_eq (M : FiniteRelModel L V)
    (c : BinaryPairPalette L) :
    HasBinaryPairPalette M (swapBinaryPairPalette c)
      = swapRel (HasBinaryPairPalette M c) := by
  funext a b
  exact propext ((hasBinaryPairPalette_swap_iff M c).trans Iff.rfl)

omit [DecidableEq V] in
/-- Density transports along orientation reversal. -/
theorem pairDensity_hasBinaryPairPalette_swap (M : FiniteRelModel L V)
    (c : BinaryPairPalette L) (A B : Finset V) :
    pairDensity (HasBinaryPairPalette M (swapBinaryPairPalette c)) A B
      = pairDensity (HasBinaryPairPalette M c) B A := by
  simp only [hasBinaryPairPalette_swap_eq, pairDensity_swapRel]

omit [DecidableEq V] in
/-- Uniformity transports along orientation reversal. -/
theorem isUniformPair_hasBinaryPairPalette_swap_iff (M : FiniteRelModel L V)
    (c : BinaryPairPalette L) {A B : Finset V} {τ : ℝ} :
    IsUniformPair (HasBinaryPairPalette M (swapBinaryPairPalette c)) A B τ
      ↔ IsUniformPair (HasBinaryPairPalette M c) B A τ := by
  simp only [hasBinaryPairPalette_swap_eq]
  exact isUniformPair_swapRel_iff _

end Orientation

/-! ### The Unit-7-to-Unit-8 composition: the representative certificate -/

section RepCertificate

variable {V : Type*} [DecidableEq V] {s : Finset V}
variable {L : FirstOrder.Language} [FiniteRelational L]
variable {M : FiniteRelModel L V} {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-- **The representative certificate** — the literal composition of Unit 7 with the
Unit 8 counting surface. The representatives are OBTAINED from
`exists_representatives`; every certificate hypothesis is then DERIVED from the
Unit 7 guarantees: the size floors from representative membership, the size clause,
and large-cell membership; the `E w.coarse.parts.card`-uniformity of the three
required palettes at their ordered orientations from the selection clause; and the
`(θ' − η)`-density floors from the coarse floors through the selection's
density-closeness via `le_of_coarse_of_close`. The certificate clause is
**pattern-uniform**: one representative system serves every pattern `P` and every
large profile-matching coarse triple. -/
theorem BinaryPaletteStrongDiagWitness.exists_rep_certificate [AtMostBinary L]
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) {q : ℕ}
    (hq : w.fine.parts.card ≤ q) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (harith : 24 * (w.coarse.parts.card : ℝ) ^ 2
        * (Fintype.card (BinaryPairPalette L) : ℝ)
        * (E w.coarse.parts.card + δ / η ^ 2) < α ^ 2) :
    ∃ rep : Finset V → Fin 3 → Finset V,
      (∀ C ∈ largeParts w.coarse α, ∀ i : Fin 3,
        rep C i ∈ w.fine.parts ∧ rep C i ⊆ C ∧ C.card ≤ 2 * q * (rep C i).card) ∧
      ∀ (P : FiniteRelModel L (Fin 3)) (T : Fin 3 → Finset V) {θ' : ℝ},
        (∀ i, T i ∈ largeParts w.coarse α) →
        NullaryCompatible P M →
        (∀ i, ∀ v ∈ rep (T i) i,
          binaryVertexProfile M v = binaryVertexProfile P i) →
        θ' ≤ pairDensity
          (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1) →
        θ' ≤ pairDensity
          (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2) →
        θ' ≤ pairDensity
          (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) →
        η ≤ θ' →
        E w.coarse.parts.card ≤ 1 →
        7 * E w.coarse.parts.card < (θ' - η) ^ 3 →
        6 * q < ((θ' - η) ^ 3 - 7 * E w.coarse.parts.card) * (α * s.card) →
        0 < inducedEmbeddingCountOn P M ![rep (T 0) 0, rep (T 1) 1, rep (T 2) 2] := by
  obtain ⟨rep, hmem, hgood⟩ := w.exists_representatives hq hα hη harith
  refine ⟨rep, hmem, ?_⟩
  intro P T θ' hT hnull hprof h01 h02 h12 hηθ hτ1 hmargin hhost
  -- The host is nonempty because a large coarse cell is a nonempty part.
  have hC0 : T 0 ∈ w.coarse.parts := largeParts_subset (hT 0)
  have hs : (0 : ℝ) < s.card := by
    have h1 : 0 < (T 0).card :=
      Finset.card_pos.mpr (w.coarse.nonempty_of_mem_parts hC0)
    have h2 : (T 0).card ≤ s.card := Finset.card_le_card (w.coarse.le hC0)
    exact_mod_cast lt_of_lt_of_le h1 h2
  have han : (0 : ℝ) < α * s.card := mul_pos hα hs
  -- The three ordered required-palette orientations, from the selection clause.
  have h01g := hgood (T 0) (hT 0) (T 1) (hT 1) 0 1 (by decide)
    (binaryPairPalette P 0 1)
  have h02g := hgood (T 0) (hT 0) (T 2) (hT 2) 0 2 (by decide)
    (binaryPairPalette P 0 2)
  have h12g := hgood (T 1) (hT 1) (T 2) (hT 2) 1 2 (by decide)
    (binaryPairPalette P 1 2)
  -- Representative density floors, from the coarse floors through closeness.
  have hd01 := le_of_coarse_of_close h01 h01g.2
  have hd02 := le_of_coarse_of_close h02 h02g.2
  have hd12 := le_of_coarse_of_close h12 h12g.2
  -- Size floors from representative size and large-cell membership.
  have hsz : ∀ i : Fin 3, α * s.card ≤ 2 * q * ((rep (T i) i).card : ℝ) := by
    intro i
    have hCl := card_le_of_mem_largeParts (hT i)
    have hsize : ((T i).card : ℝ) ≤ 2 * q * (rep (T i) i).card := by
      exact_mod_cast (hmem (T i) (hT i) i).2.2
    linarith
  exact inducedEmbeddingCountOn_pos_of_representatives hnull
    (hprof 0) (hprof 1) (hprof 2) (E.pos _).le hτ1 (by linarith) han
    h01g.1 h02g.1 h12g.1 hd01 hd02 hd12 (hsz 0) (hsz 1) (hsz 2) hhost

/-- **Both orientations, visibly**: the selection clause at the reversed roles with
the reversed required palette gives the swap-orientation uniformity — through the
proved reversal law, never an assumption. -/
theorem rep_swap_orientation {α η : ℝ}
    {rep : Finset V → Fin 3 → Finset V} {w : BinaryPaletteStrongDiagWitness M E δ P₀}
    (hgood : ∀ C ∈ largeParts w.coarse α, ∀ D ∈ largeParts w.coarse α,
      ∀ i j : Fin 3, i ≠ j → ∀ c : BinaryPairPalette L,
        IsUniformPair (HasBinaryPairPalette M c) (rep C i) (rep D j)
          (E w.coarse.parts.card) ∧
        |pairDensity (HasBinaryPairPalette M c) (rep C i) (rep D j)
          - pairDensity (HasBinaryPairPalette M c) C D| ≤ η)
    {C D : Finset V} (hC : C ∈ largeParts w.coarse α)
    (hD : D ∈ largeParts w.coarse α) {i j : Fin 3} (hij : i ≠ j)
    (c : BinaryPairPalette L) :
    IsUniformPair (HasBinaryPairPalette M (swapBinaryPairPalette c))
      (rep D j) (rep C i) (E w.coarse.parts.card) :=
  (isUniformPair_hasBinaryPairPalette_swap_iff M c).mpr
    (hgood C hC D hD i j hij c).1

end RepCertificate

/-! ### The viable-constants package -/

/-- **Viable constants exist**, with the quantifier order visible: the language
enters through the palette count `K`, the budget through the free parameter `θ`; the
derived `η`, `τ`, `ρ` depend on those alone — never on a pattern family or a carrier;
and the host-size inequality is a pure large-host cutoff in which the fine-part bound
`q` legitimately appears. Witnesses: `η = θ/2`, `τ = ρ³/8`. -/
theorem exists_viable_constants (K : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθK : θ ≤ 1 / K) :
    ∃ η τ ρ : ℝ, 0 < η ∧ 0 < τ ∧ τ ≤ 1 ∧ ρ = min θ (1 / K) - η ∧ 0 < ρ ∧
      7 * τ < ρ ^ 3 ∧
      ∀ (q : ℕ) (a n : ℝ), 48 * q < ρ ^ 3 * (a * n) →
        6 * q < (ρ ^ 3 - 7 * τ) * (a * n) := by
  have hθ1 : θ ≤ 1 := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · rw [hK] at hθK
      norm_num at hθK
      linarith
    · refine hθK.trans ?_
      rw [div_le_one (by exact_mod_cast hK)]
      exact_mod_cast hK
  refine ⟨θ / 2, (θ / 2) ^ 3 / 8, θ / 2, by positivity, by positivity, ?_, ?_,
    by positivity, ?_, ?_⟩
  · have hhalf : θ / 2 ≤ 1 := by linarith
    have hpow : (θ / 2) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hhalf
    linarith
  · rw [min_eq_left hθK]
    ring
  · nlinarith [pow_pos (by positivity : (0 : ℝ) < θ / 2) 3]
  · intro q a n hq
    nlinarith [hq]

/-! ### The parameter hierarchy: the viable half and the formalized obstruction -/

/-- **The uniformity-side hierarchy is viable, in the correct quantifier order**: the
schedule is chosen BEFORE any witness, and at EVERY realized coarse complexity `k` it
satisfies the tolerance clamp, the triangle margin, and the uniformity half of the
Unit 7 selection inequality against the coverage-forced threshold `α(k) = δ'/(k+1)`.
Witness: `E k = min 1 (min (ρ³/8) (δ'²/(96·K·(k+1)⁴ + 1)))`. -/
theorem exists_selection_schedule (K : ℕ) {ρ δ' : ℝ} (hρ : 0 < ρ) (hδ' : 0 < δ') :
    ∃ E : ErrorSchedule, ∀ k : ℕ,
      E k ≤ 1 ∧ 7 * E k < ρ ^ 3 ∧
      48 * (k : ℝ) ^ 2 * K * E k < (δ' / ((k : ℝ) + 1)) ^ 2 := by
  refine ⟨⟨fun k => min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1))),
    fun k => ?_⟩, fun k => ⟨?_, ?_, ?_⟩⟩
  · refine lt_min one_pos (lt_min (by positivity) (by positivity))
  · exact min_le_left _ _
  · have h1 : min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)))
        ≤ ρ ^ 3 / 8 := (min_le_right _ _).trans (min_le_left _ _)
    show 7 * min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)))
        < ρ ^ 3
    nlinarith [pow_pos hρ 3]
  · have h1 : min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)))
        ≤ δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    show 48 * (k : ℝ) ^ 2 * K
        * min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)))
        < (δ' / ((k : ℝ) + 1)) ^ 2
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hden : (0 : ℝ) < 96 * K * ((k : ℝ) + 1) ^ 4 + 1 := by positivity
    have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    rw [div_pow, lt_div_iff₀ (by positivity)]
    have hstep : 48 * (k : ℝ) ^ 2 * K
          * (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)) * ((k : ℝ) + 1) ^ 2
        < δ' ^ 2 := by
      rw [div_eq_mul_inv]
      rw [show 48 * (k : ℝ) ^ 2 * K * (δ' ^ 2 * (96 * K * ((k : ℝ) + 1) ^ 4 + 1)⁻¹)
          * ((k : ℝ) + 1) ^ 2
          = δ' ^ 2 * ((48 * (k : ℝ) ^ 2 * K * ((k : ℝ) + 1) ^ 2)
            * (96 * K * ((k : ℝ) + 1) ^ 4 + 1)⁻¹) from by ring]
      have hfrac : (48 * (k : ℝ) ^ 2 * K * ((k : ℝ) + 1) ^ 2)
          * (96 * K * ((k : ℝ) + 1) ^ 4 + 1)⁻¹ < 1 := by
        rw [mul_inv_lt_iff₀ hden, one_mul]
        have hmono : (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 4 := by
          have h2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
          calc (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2
              ≤ ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2 :=
                mul_le_mul_of_nonneg_right h2 (by positivity)
            _ = ((k : ℝ) + 1) ^ 4 := by ring
        nlinarith [mul_le_mul_of_nonneg_left hmono hKnn]
      calc δ' ^ 2 * ((48 * (k : ℝ) ^ 2 * K * ((k : ℝ) + 1) ^ 2)
            * (96 * K * ((k : ℝ) + 1) ^ 4 + 1)⁻¹)
          < δ' ^ 2 * 1 := by
            refine mul_lt_mul_of_pos_left hfrac (by positivity)
        _ = δ' ^ 2 := by ring
    calc 48 * (k : ℝ) ^ 2 * K
          * min 1 (min (ρ ^ 3 / 8) (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)))
          * ((k : ℝ) + 1) ^ 2
        ≤ 48 * (k : ℝ) ^ 2 * K
          * (δ' ^ 2 / (96 * K * ((k : ℝ) + 1) ^ 4 + 1)) * ((k : ℝ) + 1) ^ 2 := by
          have hnn : (0 : ℝ) ≤ 48 * (k : ℝ) ^ 2 * K := by positivity
          have := mul_le_mul_of_nonneg_left h1 hnn
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ < δ' ^ 2 := hstep

/-- **The obstruction, made precise.** The deviant half of the Unit 7 selection
inequality against the coverage-forced threshold `α = δ'/(k+1)` FORCES the witness
gap below `η²·δ'²/(48·K·k²·(k+1)²)` at the realized coarse complexity `k`. Since `δ`
must be fixed before the witness while `k` is produced by it (with a bound that
itself grows as `δ` shrinks), no fixed gap satisfies this at every realizable `k` —
the fixed-gap strong-witness API cannot support the per-pair density-closeness clause
of the Unit 7 selection at scale. This is the checkpoint finding; the proposed
re-scope replaces the per-pair closeness clause by an aggregate deviant-cost clause
(consumed only in the 11B edit budget), which removes `δ/η²` from the selection
inequality entirely and makes the hierarchy schedule-satisfiable
(`exists_selection_schedule`). -/
theorem deviant_condition_forces_gap_lt (K : ℕ) {δ η δ' : ℝ} (hη : 0 < η)
    {k : ℕ} (hK : 0 < K) (hk : 0 < k)
    (h : 48 * (k : ℝ) ^ 2 * K * (δ / η ^ 2) < (δ' / ((k : ℝ) + 1)) ^ 2) :
    δ < η ^ 2 * δ' ^ 2 / (48 * K * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  rw [div_pow] at h
  rw [lt_div_iff₀ (by positivity)]
  have h2 := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)
  rw [div_mul_cancel₀ _ (by positivity : (((k : ℝ) + 1) ^ 2) ≠ 0)] at h2
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have h3 := mul_lt_mul_of_pos_right h2 hη2
  have hsimp : 48 * (k : ℝ) ^ 2 * K * (δ / η ^ 2) * ((k : ℝ) + 1) ^ 2 * η ^ 2
      = δ * (48 * K * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2) := by
    field_simp
  rw [hsimp] at h3
  nlinarith [h3]

/-! ### Tests and adversarial examples -/

section Tests

-- The constants package computes at the graph language (`K = 4`): `θ = 1/4` is
-- admissible and the package delivers `ρ = 1/8` with all inequalities strict and the
-- counting-required clamp `τ ≤ 1` packaged.
example : ∃ η τ ρ : ℝ, 0 < η ∧ 0 < τ ∧ τ ≤ 1 ∧
    ρ = min (1 / 4 : ℝ) (1 / (4 : ℕ)) - η ∧ 0 < ρ ∧
    7 * τ < ρ ^ 3 ∧ ∀ (q : ℕ) (a n : ℝ), 48 * q < ρ ^ 3 * (a * n) →
      6 * q < (ρ ^ 3 - 7 * τ) * (a * n) :=
  exists_viable_constants 4 (θ := 1 / 4) (by norm_num) (by norm_num)

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
