/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ForbiddenForkGate
import RegularityLemmata.Relational.TransversalCounting

/-!
# Route (b) ladder step 2: the weakened-counting gate

`ARCHITECTURE.md` route (b) ladder step 2. Branch B replaced "every selected proxy pair is
palette-uniform" by "the selected palette-nonuniform pairs carry little normalized mass". The
question this file answers is what that weakening costs the three-vertex count.

**This is a gate, not step 5.** No selection is performed and no summit is assembled.

## The chain

1. `selectedPaletteNonuniformPairs` — the proxy pairs whose two selected representatives fail
   uniformity for some colour. A `Finset (Finset V × Finset V)` inside `Q.parts ×ˢ Q.parts`,
   so the existing pair-to-triple lifting applies to it unchanged.
2. `sum_selectedPaletteNonuniformPairs_mass` — its RAW pair mass is exactly
   `#s ^ 2 * proxyNormalizedPaletteCost`. The normalized charge and the raw mass are the same
   quantity in different units, so a cost bound is a mass bound.
3. The lifting is REUSED, not reproved: `selectedPairTripleMass_zero_one_le`,
   `selectedPairTripleMass_zero_two_le`, `selectedPairTripleMass_one_two_le`
   (`Relational/TransversalCounting.lean`) each bound a one-coordinate-pair-restricted triple
   mass by the pair mass times `#s`.
4. The three-coordinate union is `selectedPairTripleMass_any_le`, which lives with the rest
   of the counting infrastructure in `Relational/TransversalCounting.lean` and mentions no
   palette, proxy or regularity: triples with ANY coordinate pair in `D` carry volume at most
   `3 * (D-pair mass) * #s`. `badTripleVolume_le` is its short NORMALIZED corollary, giving
   `3 * β * #s ^ 3` from a pair mass at most `β * #s ^ 2`. The factor three is the number of
   coordinate pairs in a triple and nothing else.

## The combined constant

Under branch B uniformity is no longer a forbidden event, so a weighted-choice call would use
an EMPTY forbidden-event type: `hbad` holds at `σ = 0` and the conditioning factor
`1 / (1 - σ)` is `1`. The palette-nonuniformity and deviation charges then combine into a
single cost, and `expected_proxyCombinedCost_le` gives its budget as

`4 * K * ε + 4 * K * δ / η ^ 2`

**undoubled** — not the `2 ×` of the conditioned form. `exists_piFinset_cost_le`
(`Finite/WeightedChoice.lean`) makes that formal without dummy event arguments: it consumes
a positive total weight and an expected-cost bound and returns a selection at cost at most
`μ`, being the conditioned theorem at `E := Empty`, `σ := 0`. That is the constant branch B
has to live with, and it is what this file pins.

## What is NOT done here

Step 5's second half: applying ordinary three-vertex counting to the surviving triples and
the crude volume bound to the bad ones, and seeing whether the resulting count is still
positive. `badTripleVolume_le` is the input that step needs; the count itself is not attempted
here, and **step 5 stays closed**.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] (M : FiniteRelModel L V)

/-! ### The selected palette-nonuniform proxy pairs -/

open Classical in
/-- The proxy pairs whose two SELECTED representatives fail uniformity for some colour. -/
noncomputable def selectedPaletteNonuniformPairs (ε : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) : Finset (Finset V × Finset V) :=
  ((Finset.univ : Finset (ProxyEvent Q)).filter fun e =>
      (g (proxyEventFst e), g (proxyEventSnd e)) ∈ paletteNonuniformFinePairs M ε F).image
    proxyEventPair

theorem selectedPaletteNonuniformPairs_subset (ε : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) :
    selectedPaletteNonuniformPairs M ε F Q g ⊆ Q.parts ×ˢ Q.parts := by
  classical
  intro p hp
  rw [selectedPaletteNonuniformPairs, Finset.mem_image] at hp
  obtain ⟨e, -, rfl⟩ := hp
  have := mem_proxyPairEvents.mp e.2
  exact Finset.mem_product.mpr ⟨this.1, this.2.1⟩

open Classical in
/-- **The charge and the raw mass are the same quantity.** The selected palette-nonuniform
pairs carry raw mass exactly `#s ^ 2` times the normalized charge, so a cost bound on the
charge is a mass bound on the pairs — which is what the pair-to-triple lifting consumes. -/
theorem sum_selectedPaletteNonuniformPairs_mass (ε : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) :
    ∑ p ∈ selectedPaletteNonuniformPairs M ε F Q g, ((p.1.card : ℝ) * p.2.card)
      = (s.card : ℝ) ^ 2 * proxyNormalizedPaletteCost M ε F Q g := by
  classical
  rw [selectedPaletteNonuniformPairs,
    Finset.sum_image fun a _ b _ h => proxyEventPair_injective h,
    proxyNormalizedPaletteCost, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [proxyPairMassWeight]
  rcases Nat.eq_zero_or_pos s.card with hs | hs
  · -- No parts, hence no events: the index set is empty and `e` cannot exist.
    refine absurd (mem_proxyPairEvents.mp e.2).1 ?_
    have hQ : Q.parts = ∅ := by
      rw [Finpartition.parts_eq_empty_iff]
      exact Finset.card_eq_zero.mp hs
    rw [hQ]
    exact Finset.notMem_empty _
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs
      positivity
    field_simp

/-! ### The three-coordinate union bound -/

open Classical in
/-- **Bad-triple volume.** With the selected nonuniform pair mass at most `β * #s ^ 2`, the
transversal triples having ANY bad coordinate pair carry volume at most `3 * β * #s ^ 3`. The
three coordinate pairs of a triple are charged by a union bound, so the factor is exactly
three; the pair-to-triple lifting is the existing one, reused unchanged. -/
theorem badTripleVolume_le {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    {β : ℝ} (hβ : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2) :
    ∑ T ∈ (transversalCellTriples Q).filter
        (fun T => (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ 3 * β * (s.card : ℝ) ^ 3 := by
  refine (selectedPairTripleMass_any_le hD).trans ?_
  have hs0 : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  calc 3 * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * s.card
      ≤ 3 * (β * (s.card : ℝ) ^ 2) * s.card := by nlinarith [hβ, hs0]
    _ = 3 * β * (s.card : ℝ) ^ 3 := by ring

/-! ### The undoubled combined cost -/

variable {sch : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

open Classical in
/-- **The combined branch-B cost.** With uniformity no longer forbidden, the two charges are
one cost, and its budget is the SUM of the two — `4 * K * ε + 4 * K * δ / η ^ 2`. No
conditioning factor appears: an empty forbidden-event type makes `hbad` hold at `σ = 0`, so
`1 / (1 - σ) = 1` and the doubled form of the conditioned bound is not incurred. -/
theorem expected_proxyCombinedCost_le (w : BinaryPaletteStrongDiagWitness M sch δ P₀)
    (q : ℕ) {ε η : ℝ} (hη : 0 < η) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ)
    (hq : w.fine.parts.card ≤ q)
    (hB : ∀ c : BinaryPairPalette L,
      badMassDiagNum (HasBinaryPairPalette M c) ε w.fine ≤ ε * (s.card : ℝ) ^ 2) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
        (∏ j, ((g j).card : ℝ))
          * (proxyNormalizedPaletteCost M ε w.fine w.coarse g
            + proxyNormalizedDeviationCost M η w.fine w.coarse g)
      ≤ (4 * (Fintype.card (BinaryPairPalette L) : ℝ) * ε
          + 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * δ / η ^ 2)
        * proxyTotalCandidateWeight w.fine q w.coarse := by
  classical
  have hsplit : ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
        (∏ j, ((g j).card : ℝ))
          * (proxyNormalizedPaletteCost M ε w.fine w.coarse g
            + proxyNormalizedDeviationCost M η w.fine w.coarse g)
      = (∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
            (∏ j, ((g j).card : ℝ)) * proxyNormalizedPaletteCost M ε w.fine w.coarse g)
        + ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
            (∏ j, ((g j).card : ℝ)) * proxyNormalizedDeviationCost M η w.fine w.coarse g := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [hsplit, add_mul]
  exact add_le_add (expected_proxyNormalizedPaletteCost_le M w.fine_le hq hε hB)
    (expected_proxyNormalizedDeviationCost_le w q hη hδ0 hq)

/-! ### Tests -/

section Tests

-- The selected pairs live where the lifting expects them, which is why it applies unchanged.
example (ε : ℝ) (F : Finpartition s) (g : ProxyIndex Q → Finset V) :
    selectedPaletteNonuniformPairs M ε F Q g ⊆ Q.parts ×ˢ Q.parts :=
  selectedPaletteNonuniformPairs_subset M ε F Q g

-- Charge and raw mass are one quantity in two units.
example (ε : ℝ) (F : Finpartition s) (g : ProxyIndex Q → Finset V) :
    ∑ p ∈ selectedPaletteNonuniformPairs M ε F Q g, ((p.1.card : ℝ) * p.2.card)
      = (s.card : ℝ) ^ 2 * proxyNormalizedPaletteCost M ε F Q g :=
  sum_selectedPaletteNonuniformPairs_mass M ε F Q g

-- The bad-triple factor is three because a triple has three coordinate pairs — not because
-- of any count of cells or events.
example : Fintype.card (Fin 3) = 3 := by decide

-- The raw union theorem is palette-, proxy- and regularity-free, and `badTripleVolume_le` is
-- its normalized corollary.
example {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts) :
    ∑ T ∈ (transversalCellTriples Q).filter
        (fun T => (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ 3 * (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * s.card :=
  selectedPairTripleMass_any_le hD

-- The undoubled constant is formally reachable: no forbidden events, no conditioning factor,
-- and no dummy event arguments at the call site.
example {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] (t : ι → Finset β)
    (wt : β → ℝ) (hwt : ∀ x, 0 ≤ wt x) (cost : (ι → β) → ℝ) (hcost : ∀ g, 0 ≤ cost g)
    {μ : ℝ} (hWpos : 0 < ∏ j, ∑ x ∈ t j, wt x)
    (hexp : ∑ g ∈ Fintype.piFinset t, (∏ j, wt (g j)) * cost g ≤ μ * ∏ j, ∑ x ∈ t j, wt x) :
    ∃ g ∈ Fintype.piFinset t, cost g ≤ μ :=
  exists_piFinset_cost_le t wt hwt cost hcost hWpos hexp

-- A vanishing charge gives no bad triples at all, so the bound degrades gracefully.
example {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    (h0 : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ 0 * (s.card : ℝ) ^ 2) :
    ∑ T ∈ (transversalCellTriples Q).filter
        (fun T => (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ 3 * 0 * (s.card : ℝ) ^ 3 :=
  badTripleVolume_le hD h0

end Tests

end RegularityLemmata
