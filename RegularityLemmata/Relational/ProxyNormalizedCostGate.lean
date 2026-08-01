/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxyHierarchyBridge

/-!
# Route (b) ladder step 2: the normalized-cost gate

`ARCHITECTURE.md` route (b) ladder step 2. Gate G-H1 left two ways to break the `P`/`δ`
hierarchy, and `Relational/ProxyHierarchyBridge.lean` closed the first (gates G-H2a, G-H2b):
no a priori count bound is available for `w.coarse`. This file tests the second — **a `P`-free
deviation requirement** — by changing what the cost channel charges.

**This is a gate, not step 5.** Nothing is assembled here.

## The change

Step 3 charged **one unit** per (proxy pair, colour) incidence at which the selected
representatives deviate. Its budget was `K * (δ / η ^ 2 * #s ^ 2) / w₀ ^ 2`, and the common
weight floor `w₀ = m / 2` turned `#s ^ 2 / m ^ 2` into a factor `4 * P ^ 2`.

Here each incidence is charged its proxy pair's own normalized mass,
`proxyPairMassWeight s pd = #pd.1 * #pd.2 / #s ^ 2`, and the cancellation is done
**coordinatewise** rather than against a common floor: `half_card_le_proxyCandidateWeight`
gives `W_C ≥ #C / 2` and `W_D ≥ #D / 2` at the event's OWN two coordinates, so
`#C * #D ≤ 4 * W_C * W_D` and the `#s ^ 2` cancels against the weight.

## The result

`expected_proxyNormalizedDeviationCost_le` :  `μ = 4 * K * δ / η ^ 2`

with **no `P` and no proxy-size floor `m`**. Conditioned at `σ ≤ 1/2`
(`conditioned_proxyNormalizedCost_le`) the selected cost is at most `8 * K * δ / η ^ 2`.
The requirement on `δ` is now `P`-free: `δ ≤ η ^ 2 * τ / (4 * K)` gives `μ ≤ τ`.

## What this does NOT do

It closes the **cost** side of the hierarchy only. The forbidden channel is untouched: `hbad`
still needs the count bound and the `m` / `m + 1` equitability facts that G-H2a says are
unavailable for `w.coarse`. **Step 5 stays closed**, and the remaining design fork is
explicit — either produce an equitable, large-cell witness coarse partition for the forbidden
channel, or redesign how nonuniform selected pairs are handled. Neither is decided here.

Note also what the conclusion now means: a bound on the total normalized MASS of deviant
incidences, not on their number. A `τ < 1` no longer forces zero deviant incidences; it
forces them to carry little proxy-pair mass.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
  {sch : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-! ### The event weight and the normalized cost -/

/-- **The event weight**: a proxy pair's own mass, normalized by the host. Replacing the
unit charge of step 3 by this is what removes `P` from the budget. -/
noncomputable def proxyPairMassWeight (s : Finset V) (pd : Finset V × Finset V) : ℝ :=
  (pd.1.card : ℝ) * pd.2.card / (s.card : ℝ) ^ 2

omit [DecidableEq V] in
theorem proxyPairMassWeight_nonneg (s : Finset V) (pd : Finset V × Finset V) :
    0 ≤ proxyPairMassWeight s pd := by
  rw [proxyPairMassWeight]; positivity

open Classical in
/-- **The normalized cost of a selection**: each (proxy pair, colour) incidence at which the
two chosen representatives deviate is charged its proxy pair's normalized mass. -/
noncomputable def proxyNormalizedDeviationCost (M : FiniteRelModel L V) (η : ℝ)
    (F : Finpartition s) (Q : Finpartition s) (g : ProxyIndex Q → Finset V) : ℝ :=
  ∑ e : ProxyDevEvent Q L,
    if (g (proxyDevFst e), g (proxyDevSnd e)) ∈
        proxyDeviantFinePairs M (proxyDevColor e) η F (proxyDevPair e)
      then proxyPairMassWeight s (proxyDevPair e) else 0

theorem proxyNormalizedDeviationCost_nonneg (M : FiniteRelModel L V) (η : ℝ)
    (F : Finpartition s) (Q : Finpartition s) (g : ProxyIndex Q → Finset V) :
    0 ≤ proxyNormalizedDeviationCost M η F Q g := by
  classical
  refine Finset.sum_nonneg fun e _ => ?_
  split
  · exact proxyPairMassWeight_nonneg s _
  · exact le_refl 0

/-! ### The `P`-free budget -/

open Classical in
/-- **Coordinatewise cancellation.** At the event's own two coordinates the half-mass theorem
gives `W_C ≥ #C / 2` and `W_D ≥ #D / 2`, so the event weight `#C * #D / #s ^ 2` is absorbed
by `4 * W_C * W_D / #s ^ 2`. No common floor and no proxy size enter. -/
theorem proxyPairMassWeight_mul_mass_le (w : BinaryPaletteStrongDiagWitness M sch δ P₀)
    {q : ℕ} (hq : w.fine.parts.card ≤ q) (e : ProxyDevEvent w.coarse L) :
    proxyPairMassWeight s (proxyDevPair e)
        * ∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩
            (proxyCandidates (Q := w.coarse) w.fine q (proxyDevFst e) ×ˢ
              proxyCandidates (Q := w.coarse) w.fine q (proxyDevSnd e)),
            ((p.1.card : ℝ) * p.2.card)
      ≤ (4 * (∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩
              (proxyCandidates (Q := w.coarse) w.fine q (proxyDevFst e) ×ˢ
                proxyCandidates (Q := w.coarse) w.fine q (proxyDevSnd e)),
              ((p.1.card : ℝ) * p.2.card)) / (s.card : ℝ) ^ 2)
        * (proxyCandidateWeight (Q := w.coarse) w.fine q (proxyDevFst e)
            * proxyCandidateWeight (Q := w.coarse) w.fine q (proxyDevSnd e)) := by
  classical
  set mass := ∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩
      (proxyCandidates (Q := w.coarse) w.fine q (proxyDevFst e) ×ˢ
        proxyCandidates (Q := w.coarse) w.fine q (proxyDevSnd e)),
      ((p.1.card : ℝ) * p.2.card) with hmassdef
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun p _ => by positivity
  have hW1 := half_card_le_proxyCandidateWeight w.fine_le hq (proxyDevFst e)
  have hW2 := half_card_le_proxyCandidateWeight w.fine_le hq (proxyDevSnd e)
  have hC : (0 : ℝ) ≤ ((proxyDevFst e).1.card : ℝ) := by positivity
  have hD : (0 : ℝ) ≤ ((proxyDevSnd e).1.card : ℝ) := by positivity
  have hkey : ((proxyDevFst e).1.card : ℝ) * ((proxyDevSnd e).1.card : ℝ)
      ≤ 4 * (proxyCandidateWeight (Q := w.coarse) w.fine q (proxyDevFst e)
        * proxyCandidateWeight (Q := w.coarse) w.fine q (proxyDevSnd e)) := by
    nlinarith [hW1, hW2, hC, hD]
  rw [proxyPairMassWeight]
  show ((proxyDevPair e).1.card : ℝ) * ((proxyDevPair e).2.card : ℝ) / (s.card : ℝ) ^ 2
      * mass ≤ _
  -- No case split on an empty host is needed: the inequality is divided by `#s ^ 2`, and
  -- division by zero sends both sides to zero.
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  show ((proxyDevFst e).1.card : ℝ) * ((proxyDevSnd e).1.card : ℝ) * mass ≤ _
  nlinarith [hkey, hmass]

open Classical in
/-- **The `P`-free cost budget.** Charging each deviant incidence its proxy pair's normalized
mass gives `μ = 4 * K * δ / η ^ 2`: no proxy count and no proxy-size floor appear. -/
theorem expected_proxyNormalizedDeviationCost_le
    (w : BinaryPaletteStrongDiagWitness M sch δ P₀) (q : ℕ) {η : ℝ} (hη : 0 < η)
    (hδ0 : 0 ≤ δ) (hq : w.fine.parts.card ≤ q) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
        (∏ j, ((g j).card : ℝ)) * proxyNormalizedDeviationCost M η w.fine w.coarse g
      ≤ 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * δ / η ^ 2
        * proxyTotalCandidateWeight w.fine q w.coarse := by
  classical
  set Dev : ProxyDevEvent w.coarse L → Finset (Finset V × Finset V) := fun e =>
    proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) with hDev
  set t := proxyCandidates (Q := w.coarse) w.fine q with ht
  set mass : ProxyDevEvent w.coarse L → ℝ := fun e =>
    ∑ p ∈ Dev e ∩ (t (proxyDevFst e) ×ˢ t (proxyDevSnd e)), ((p.1.card : ℝ) * p.2.card)
    with hmass
  have htotal : (0 : ℝ) ≤ proxyTotalCandidateWeight w.fine q w.coarse :=
    proxyTotalCandidateWeight_nonneg w.fine q
  -- The per-event accounting, with the cancellation done at each event's own coordinates.
  have hstep := sum_piFinset_weight_mul_eventCost_le t (fun A => (A.card : ℝ))
    (fun A => by positivity) proxyDevFst proxyDevSnd proxyDev_fst_ne_snd Dev
    (fun e => proxyPairMassWeight s (proxyDevPair e)) (fun e => 4 * mass e / (s.card : ℝ) ^ 2)
    (fun e => proxyPairMassWeight_mul_mass_le w hq e)
  refine le_trans (le_of_eq ?_) (le_trans hstep ?_)
  · simp only [proxyNormalizedDeviationCost, hDev, ht]
  -- The summed per-event charges are `P`-free.
  have haggr : ∑ e : ProxyDevEvent w.coarse L, mass e
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) :=
    sum_proxyDevEvent_mass_le w q hη
  have hsum : ∑ e : ProxyDevEvent w.coarse L, 4 * mass e / (s.card : ℝ) ^ 2
      ≤ 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * δ / η ^ 2 := by
    have hrw : ∑ e : ProxyDevEvent w.coarse L, 4 * mass e / (s.card : ℝ) ^ 2
        = 4 * (∑ e : ProxyDevEvent w.coarse L, mass e) / (s.card : ℝ) ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [hrw]
    rcases eq_or_ne ((s.card : ℝ) ^ 2) 0 with h0 | h0
    · rw [h0, div_zero]
      have hK : (0 : ℝ) ≤ (Fintype.card (BinaryPairPalette L) : ℝ) := by positivity
      have : (0 : ℝ) ≤ 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * δ / η ^ 2 := by
        apply div_nonneg _ (by positivity)
        nlinarith [hK, hδ0]
      exact this
    · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rw [div_le_iff₀ hpos]
      have h4 : 4 * (∑ e : ProxyDevEvent w.coarse L, mass e)
          ≤ 4 * ((Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2)) := by
        linarith [haggr]
      calc 4 * (∑ e : ProxyDevEvent w.coarse L, mass e)
          ≤ 4 * ((Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2)) := h4
        _ = 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
            field_simp
  exact mul_le_mul_of_nonneg_right hsum htotal

/-- **Conditioned.** With the forbidden budget at `σ ≤ 1/2`, the selection returned by
`exists_piFinset_forall_not_mem_bad_cost_le` has normalized deviation cost at most
`8 * K * δ / η ^ 2` — still `P`-free. -/
theorem conditioned_proxyNormalizedCost_le {K : ℕ} {η σ : ℝ} (hη : 0 < η) (hδ0 : 0 ≤ δ)
    (hσ : σ ≤ 1 / 2) :
    (4 * (K : ℝ) * δ / η ^ 2) / (1 - σ) ≤ 8 * (K : ℝ) * δ / η ^ 2 := by
  have hτ : (0 : ℝ) ≤ 4 * (K : ℝ) * δ / η ^ 2 := by
    apply div_nonneg _ (by positivity)
    have hK : (0 : ℝ) ≤ (K : ℝ) := by positivity
    nlinarith [hK, hδ0]
  have hdouble := proxyCost_le_two_mul (μ := 4 * (K : ℝ) * δ / η ^ 2)
    (τ := 4 * (K : ℝ) * δ / η ^ 2) hσ (le_refl _) hτ
  have h8 : 2 * (4 * (K : ℝ) * δ / η ^ 2) = 8 * (K : ℝ) * δ / η ^ 2 := by ring
  linarith [hdouble, h8]

/-! ### Tests -/

section Tests

-- The refinement hypothesis is not an argument: it is a field of the witness, so the two
-- cost theorems take only the candidate-index bound.
example (w : BinaryPaletteStrongDiagWitness M sch δ P₀) : w.fine ≤ w.coarse := w.fine_le

-- The event weight is nonnegative and the cost with it is too, which is `hcost`.
example (M : FiniteRelModel L V) (η : ℝ) (F : Finpartition s) (g : ProxyIndex Q → Finset V) :
    0 ≤ proxyNormalizedDeviationCost M η F Q g :=
  proxyNormalizedDeviationCost_nonneg M η F Q g

-- The budget mentions no proxy count and no proxy size: the requirement `δ ≤ η²τ/(4K)` is
-- `P`-free, unlike `proxyDeviationTolerance`.
example {K : ℕ} {η τ δ' : ℝ} (hη : 0 < η) (hK : 0 < K) (hδ : δ' ≤ η ^ 2 * τ / (4 * K)) :
    4 * (K : ℝ) * δ' / η ^ 2 ≤ τ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  rw [le_div_iff₀ (by positivity)] at hδ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hδ]

-- Coordinatewise cancellation, in isolation: two half-mass floors give the factor four, and
-- no common floor `m` is used.
example {C D W₁ W₂ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (h1 : C / 2 ≤ W₁) (h2 : D / 2 ≤ W₂) :
    C * D ≤ 4 * (W₁ * W₂) := by nlinarith [h1, h2, hC, hD]

-- The conditioning factor is two, as at the frozen half-budget.
example {K : ℕ} {η : ℝ} (hη : 0 < η) (hδ0 : 0 ≤ δ) :
    (4 * (K : ℝ) * δ / η ^ 2) / (1 - 1 / 2) ≤ 8 * (K : ℝ) * δ / η ^ 2 :=
  conditioned_proxyNormalizedCost_le hη hδ0 (le_refl _)

-- What the bound now means: a deviant incidence carries its proxy pair's normalized mass,
-- so a small total does NOT force zero deviant incidences — only little mass.
example (pd : Finset V × Finset V) : 0 ≤ proxyPairMassWeight s pd :=
  proxyPairMassWeight_nonneg s pd

end Tests

end RegularityLemmata
