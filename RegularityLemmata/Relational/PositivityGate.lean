/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.GenericTripleEstimate

/-!
# Route (b) ladder step 2: the positivity gate

`ARCHITECTURE.md` route (b) ladder step 2. The indexed-box estimate bounds the DIFFERENCE
between the representative count and its density estimate. Removal needs the count itself to
be positive, so the estimate must be bounded BELOW by more than the error. This file asks
whether that margin can be met.

**This is a gate, not step 5.** No adapter and no selection is built.

## The margin

* `le_representativeInducedEstimate_of_single_triple` — one matching triple with three
  representative-density floors `ρ`, proxy-cell floors `α·#s ≤ #Cᵢ`, and the candidate
  inequalities `#Cᵢ ≤ 2q·#(g Cᵢ)` already forces
  `ρ³ · α³ · #s³ ≤ (2q)³ · representativeInducedEstimate`.
* `representativeInducedCount_pos` — combined with the indexed-box estimate, the count is
  positive under the **multiplication-form margin**

  `(2q)³ · (7ε + 3β) < ρ³ · α³`.

  Stated multiplicatively throughout: nothing is divided by `q`, matching the candidate API,
  which itself is multiplicative (`#C ≤ 2q·#A`).
* `positivityMargin_of_combined_cost` — with the available combined-cost bound
  `β ≤ 4Kε + 4Kδ/η²`, the obligation becomes

  `(2q)³ · (7ε + 12Kε + 12Kδ/η²) < ρ³ · α³`.

## Gate G-Q1 — the margin is not satisfiable in the current order

`q` bounds the FINE partition's part count, and the fine partition is produced AT the
tolerance `ε` that appears in the margin. Shrinking `ε` to buy the inequality enlarges the
fine partition, hence `q`, and `q` enters cubed.

`margin_fails_of_inverse_linear_q` makes this precise without needing the exact growth rate:
**any** dependence with `c/ε ≤ q` for a positive constant `c` — inverse-linear, already far
weaker than the tower the regularity iteration actually gives — forces the left-hand side to
be at least `56c³/ε²`, which exceeds any fixed `ρ³α³` once `ε` is small. Shrinking `ε` makes
the margin worse, not better.

This is the same shape as gate G-H2b, now on `q` rather than on the coarse count: the
parameter that must shrink to buy the estimate is the parameter that enlarges the quantity it
is fighting.

**Consequence.** The route does not close by choosing parameters in the current order.
Step 5 stays closed, and the `ProxyIndex Q → Finset V → Finset V` adapter is NOT built —
building it would polish a route whose stop condition has not been met.

What is not claimed: that no route closes. The gate constrains the ORDER of choice. Escapes
that remain open are a `ρ` or `α` improving with `q` fast enough to absorb `q³`, a count
bounded below without passing through the density estimate, or an error term not proportional
to `#s³`.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] [AtMostBinary L]
  {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}

/-! ### A single triple bounds the estimate below -/

omit [AtMostBinary L] in
set_option maxHeartbeats 1000000 in
open Classical in
/-- **One matching triple suffices.** All terms of the estimate are nonnegative, so a single
triple with representative-density floors `ρ`, proxy-cell floors `α·#s`, and the candidate
inequalities `#Cᵢ ≤ 2q·#(g Cᵢ)` bounds the whole estimate below — in multiplication form,
with `(2q)³` on the left rather than a division. -/
theorem le_representativeInducedEstimate_of_single_triple {g : Finset V → Finset V}
    {T : Fin 3 → Finset V} (hT : T ∈ transversalCellTriples Q)
    (hmatch : MatchesThreeProfiles P M (fun i => g (T i)))
    {ρ α q : ℝ} (hρ0 : 0 ≤ ρ) (hα0 : 0 ≤ α) (hq0 : 0 ≤ q)
    (hρ01 : ρ ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1))
      (g (T 0)) (g (T 1)))
    (hρ02 : ρ ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2))
      (g (T 0)) (g (T 2)))
    (hρ12 : ρ ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2))
      (g (T 1)) (g (T 2)))
    (hα : ∀ i, α * (s.card : ℝ) ≤ ((T i).card : ℝ))
    (hcand : ∀ i, ((T i).card : ℝ) ≤ 2 * q * ((g (T i)).card : ℝ)) :
    ρ ^ 3 * α ^ 3 * (s.card : ℝ) ^ 3
      ≤ (2 * q) ^ 3 * representativeInducedEstimate P M Q g := by
  classical
  set d01 := pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1))
    (g (T 0)) (g (T 1)) with hd01def
  set d02 := pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2))
    (g (T 0)) (g (T 2)) with hd02def
  set d12 := pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2))
    (g (T 1)) (g (T 2)) with hd12def
  set b : ℝ := ((g (T 0)).card : ℝ) * (g (T 1)).card * (g (T 2)).card with hbdef
  have hs0 : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hgnn : ∀ i, (0 : ℝ) ≤ ((g (T i)).card : ℝ) := fun i => by positivity
  have hb0 : (0 : ℝ) ≤ b := by rw [hbdef]; positivity
  have hq3 : (0 : ℝ) ≤ (2 * q) ^ 3 := by positivity
  have hρ3 : (0 : ℝ) ≤ ρ ^ 3 := pow_nonneg hρ0 3
  -- The three density floors multiply.
  have hdprod : ρ ^ 3 ≤ d01 * d02 * d12 := by
    calc ρ ^ 3 = ρ * ρ * ρ := by ring
      _ ≤ d01 * d02 * d12 :=
          mul_le_mul (mul_le_mul hρ01 hρ02 hρ0 (hρ0.trans hρ01)) hρ12 hρ0
            (mul_nonneg (hρ0.trans hρ01) (hρ0.trans hρ02))
  -- The cell floors and the candidate inequalities multiply.
  have hbox : α ^ 3 * (s.card : ℝ) ^ 3 ≤ (2 * q) ^ 3 * b := by
    have h0 := (hα 0).trans (hcand 0)
    have h1 := (hα 1).trans (hcand 1)
    have h2 := (hα 2).trans (hcand 2)
    have hαs : (0 : ℝ) ≤ α * (s.card : ℝ) := mul_nonneg hα0 hs0
    have hc0 : (0 : ℝ) ≤ 2 * q * ((g (T 0)).card : ℝ) := by positivity
    have hc1 : (0 : ℝ) ≤ 2 * q * ((g (T 1)).card : ℝ) := by positivity
    calc α ^ 3 * (s.card : ℝ) ^ 3
        = (α * (s.card : ℝ)) * (α * (s.card : ℝ)) * (α * (s.card : ℝ)) := by ring
      _ ≤ (2 * q * ((g (T 0)).card : ℝ)) * (2 * q * ((g (T 1)).card : ℝ))
            * (2 * q * ((g (T 2)).card : ℝ)) :=
          mul_le_mul (mul_le_mul h0 h1 hαs hc0) h2 hαs (mul_nonneg hc0 hc1)
      _ = (2 * q) ^ 3 * b := by rw [hbdef]; ring
  -- The estimate dominates the single matching triple's term.
  have hsingle : d01 * d02 * d12 * (g (T 0)).card * (g (T 1)).card * (g (T 2)).card
      ≤ representativeInducedEstimate P M Q g := by
    rw [hd01def, hd02def, hd12def, representativeInducedEstimate]
    have hnn : ∀ U : Fin 3 → Finset V, (0 : ℝ) ≤
        pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g (U 0)) (g (U 1))
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (g (U 0)) (g (U 2))
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (g (U 1)) (g (U 2))
          * (g (U 0)).card * (g (U 1)).card * (g (U 2)).card := fun U =>
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        pairDensity_nonneg pairDensity_nonneg) pairDensity_nonneg)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    exact Finset.single_le_sum (fun U _ => hnn U) (Finset.mem_filter.mpr ⟨hT, hmatch⟩)
  have hterm : ρ ^ 3 * b
      ≤ d01 * d02 * d12 * (g (T 0)).card * (g (T 1)).card * (g (T 2)).card := by
    calc ρ ^ 3 * b ≤ (d01 * d02 * d12) * b := mul_le_mul_of_nonneg_right hdprod hb0
      _ = d01 * d02 * d12 * (g (T 0)).card * (g (T 1)).card * (g (T 2)).card := by
          rw [hbdef]; ring
  calc ρ ^ 3 * α ^ 3 * (s.card : ℝ) ^ 3 = ρ ^ 3 * (α ^ 3 * (s.card : ℝ) ^ 3) := by ring
    _ ≤ ρ ^ 3 * ((2 * q) ^ 3 * b) := mul_le_mul_of_nonneg_left hbox hρ3
    _ = (2 * q) ^ 3 * (ρ ^ 3 * b) := by ring
    _ ≤ (2 * q) ^ 3 * representativeInducedEstimate P M Q g :=
        mul_le_mul_of_nonneg_left (hterm.trans hsingle) hq3

/-! ### Positivity under the margin -/

open Classical in
omit [AtMostBinary L] in
/-- **The positivity criterion.** With the estimate bounded below by a single triple and the
indexed-box estimate bounding the error, the representative count is positive as soon as the
multiplication-form margin holds. Nothing is divided by `q`. -/
theorem representativeInducedCount_pos {g : Finset V → Finset V}
    {ρ α q ε β : ℝ} (hq0 : 0 ≤ q)
    (hlow : ρ ^ 3 * α ^ 3 * (s.card : ℝ) ^ 3
      ≤ (2 * q) ^ 3 * representativeInducedEstimate P M Q g)
    (herr : |(representativeInducedCount P M Q g : ℝ) - representativeInducedEstimate P M Q g|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3)
    (hspos : 0 < (s.card : ℝ))
    (hmargin : (2 * q) ^ 3 * (7 * ε + 3 * β) < ρ ^ 3 * α ^ 3) :
    0 < representativeInducedCount P M Q g := by
  have hq3 : (0 : ℝ) ≤ (2 * q) ^ 3 := by positivity
  have hs3 : (0 : ℝ) < (s.card : ℝ) ^ 3 := by positivity
  have habs := (abs_le.mp herr).1
  -- `(2q)³ · count ≥ ρ³α³|s|³ − (2q)³(7ε+3β)|s|³ > 0`.
  have hpos : (0 : ℝ) < (2 * q) ^ 3 * (representativeInducedCount P M Q g : ℝ) := by
    nlinarith [hlow, habs, hmargin, hq3, hs3]
  have hcast : (0 : ℝ) < (representativeInducedCount P M Q g : ℝ) := by
    by_contra hcon
    push Not at hcon
    nlinarith [hpos, hq3, hcon]
  exact_mod_cast hcast

/-- **The obligation with the combined cost substituted.** The available bound on the
selected bad-pair mass is `β ≤ 4Kε + 4Kδ/η²`, so the margin becomes
`(2q)³ · (7ε + 12Kε + 12Kδ/η²) < ρ³α³`. -/
theorem positivityMargin_of_combined_cost {ρ α q ε β K δ η : ℝ} (hq0 : 0 ≤ q)
    (hβ : β ≤ 4 * K * ε + 4 * K * δ / η ^ 2)
    (hobl : (2 * q) ^ 3 * (7 * ε + 12 * K * ε + 12 * K * δ / η ^ 2) < ρ ^ 3 * α ^ 3) :
    (2 * q) ^ 3 * (7 * ε + 3 * β) < ρ ^ 3 * α ^ 3 := by
  have hq3 : (0 : ℝ) ≤ (2 * q) ^ 3 := by positivity
  have h3 : 7 * ε + 3 * β ≤ 7 * ε + 12 * K * ε + 12 * K * δ / η ^ 2 := by
    have h3β := mul_le_mul_of_nonneg_left hβ (by norm_num : (0 : ℝ) ≤ 3)
    have hring : 3 * (4 * K * ε + 4 * K * δ / η ^ 2)
        = 12 * K * ε + 12 * K * δ / η ^ 2 := by ring
    linarith [h3β, hring.le, hring.ge]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h3 hq3) hobl

/-! ### Gate G-Q1 — the margin worsens as the tolerance shrinks -/

/-- **Gate G-Q1.** `q` bounds the fine partition's part count, and that partition is produced
at the tolerance `ε` appearing in the margin. Any dependence at least inverse-linear —
`c/ε ≤ q` for a positive constant — already forces the margin's left-hand side above
`56c³/ε²`, which exceeds any fixed `ρ³α³` once `ε` is small. Shrinking `ε` to buy the
inequality makes it worse.

The regularity iteration gives a far stronger dependence than inverse-linear, so this is a
weak hypothesis, deliberately: the obstruction does not rest on the exact growth rate. -/
theorem margin_fails_of_inverse_linear_q {c ε q ρ α β : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hβ0 : 0 ≤ β) (hq : c / ε ≤ q)
    (hsmall : ρ ^ 3 * α ^ 3 * ε ^ 2 ≤ 56 * c ^ 3) :
    ¬ ((2 * q) ^ 3 * (7 * ε + 3 * β) < ρ ^ 3 * α ^ 3) := by
  intro hmargin
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hqe : c ≤ q * ε := by
    rw [div_le_iff₀ hε] at hq
    linarith
  -- `(2q)³ · 7ε ≥ 56c³/ε²`, i.e. `(2q)³ · 7ε · ε² ≥ 56c³`.
  have hcube : 56 * c ^ 3 ≤ (2 * q) ^ 3 * (7 * ε) * ε ^ 2 := by
    have h0 : (0 : ℝ) ≤ c := hc.le
    have hqe0 : (0 : ℝ) ≤ q * ε := h0.trans hqe
    have h : c ^ 3 ≤ (q * ε) ^ 3 := by
      calc c ^ 3 = c * c * c := by ring
        _ ≤ (q * ε) * (q * ε) * (q * ε) :=
            mul_le_mul (mul_le_mul hqe hqe h0 hqe0) hqe h0 (mul_nonneg hqe0 hqe0)
        _ = (q * ε) ^ 3 := by ring
    calc 56 * c ^ 3 ≤ 56 * (q * ε) ^ 3 := by linarith [h]
      _ = (2 * q) ^ 3 * (7 * ε) * ε ^ 2 := by ring
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hq3 : (0 : ℝ) ≤ (2 * q) ^ 3 := by positivity
  have hstep : (2 * q) ^ 3 * (7 * ε) ≤ (2 * q) ^ 3 * (7 * ε + 3 * β) := by
    nlinarith [hq3, hβ0]
  have hlt : (2 * q) ^ 3 * (7 * ε) < ρ ^ 3 * α ^ 3 := lt_of_le_of_lt hstep hmargin
  have h1 := mul_lt_mul_of_pos_right hlt hε2
  exact lt_irrefl _ (lt_of_le_of_lt hcube (lt_of_lt_of_le h1 hsmall))

/-! ### Tests -/

section Tests

-- The margin is multiplicative: `q` never appears in a denominator, matching the candidate
-- API `#C ≤ 2q·#(g C)`.
example {ρ α q ε β : ℝ} (h : (2 * q) ^ 3 * (7 * ε + 3 * β) < ρ ^ 3 * α ^ 3) :
    (2 * q) ^ 3 * (7 * ε + 3 * β) < ρ ^ 3 * α ^ 3 := h

-- G-Q1 at a concrete instance: with `q = 1/ε` and unit floors, the margin already fails once
-- `ε ≤ 1`, so no smaller tolerance can rescue it.
example {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ ((2 * (1 / ε)) ^ 3 * (7 * ε + 3 * 0) < 1 ^ 3 * 1 ^ 3) := by
  refine margin_fails_of_inverse_linear_q (c := 1) one_pos hε (le_refl 0) (le_refl _) ?_
  have hsq : ε ^ 2 ≤ 1 := by nlinarith [hε.le, hε1]
  nlinarith [hsq]

-- The gate constrains the ORDER of choice, not the existence of a route: at a `q` that does
-- NOT grow with `ε`, the same margin is satisfiable.
example : (2 * (1 : ℝ)) ^ 3 * (7 * (1 / 1000 : ℝ) + 3 * 0) < (1 : ℝ) ^ 3 * 1 ^ 3 := by
  norm_num

end Tests

end RegularityLemmata
