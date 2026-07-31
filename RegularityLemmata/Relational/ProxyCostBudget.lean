/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxySelectionSetup

/-!
# Route (b) ladder step 2: the conditioned aggregate-cost budget

`ARCHITECTURE.md` route (b) ladder step 2, final unit, **step 3 of five**: the `hexp` input
of `exists_piFinset_forall_not_mem_bad_cost_le`, built from `sum_proxyPair_deviant_le` once
per palette. The constants and `σ < 1` are step 4; the summit is step 5.

## The cost, and why its index may carry a colour

`cost` is a function of the SELECTION alone, so the index used to build it is free — it is
not the forbidden-event type `E` of `hbad`. The cost therefore charges once per ordered
distinct proxy pair AND per palette colour:

* `ProxyDevEvent Q L` — a `ProxyEvent Q` together with a `BinaryPairPalette L`, with
  coordinates `proxyDevFst`, `proxyDevSnd` inherited from the proxy pair and still distinct.
* `proxyDeviantFinePairs M c η F pd` — the fine pairs whose palette-`c` density differs from
  the proxy pair `pd`'s by more than `η`.
* `proxyDeviationCost M η F Q g` — the number of (proxy pair, colour) incidences at which the
  selection's two representatives deviate. Nonnegative by construction
  (`proxyDeviationCost_nonneg`, the `hcost` input).

## The budget

`sum_piFinset_weight_mul_eventCost_le_of_weight_floor` (`Finite/WeightedChoice.lean`) takes
an aggregate event-mass bound straight to `hexp`: it composes the expected-cost identity with
the weight-floor factorization used by the forbidden channel. `sum_proxyDevEvent_mass_le`
supplies that aggregate by applying `sum_proxyPair_deviant_le` once per colour. The result is

`expected_proxyDeviationCost_le` :  `μ = K * (δ / η ^ 2 * #s ^ 2) / w₀ ^ 2`

with `K = Fintype.card (BinaryPairPalette L)`. **The same principle as step 2 holds here**:
the mass is summed over proxy pairs once per palette, so only the palette multiplicity is
paid — never the event-cardinality envelope. No `9n²` multiplier occurs.

## Steps 4–5, not done here

The candidate-weight and proxy-size constants that give `w₀` a value and discharge `σ < 1`;
the summit. `ARCHITECTURE.md` waits for the completed theorem and its actual constants.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
  {sch : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-! ### The cost events -/

/-- The cost events: an ordered distinct proxy pair together with a palette colour. Unlike
the FORBIDDEN events these do carry a colour — `cost` is a function of the selection alone,
so the index used to build it is free and need not be `hbad`'s event type. -/
abbrev ProxyDevEvent (Q : Finpartition s) (L : FirstOrder.Language) [FiniteRelational L] :
    Type _ :=
  ProxyEvent Q × BinaryPairPalette L

/-- The ordered proxy PAIR a cost event charges against. -/
def proxyDevPair (e : ProxyDevEvent Q L) : Finset V × Finset V := proxyEventPair e.1

/-- The COLOUR a cost event charges for. -/
def proxyDevColor (e : ProxyDevEvent Q L) : BinaryPairPalette L := e.2

/-- The first coordinate of a cost event — a proxy CELL, inherited from its proxy pair. -/
def proxyDevFst (e : ProxyDevEvent Q L) : ProxyIndex Q := proxyEventFst e.1

/-- The second coordinate of a cost event. -/
def proxyDevSnd (e : ProxyDevEvent Q L) : ProxyIndex Q := proxyEventSnd e.1

@[simp] theorem proxyDevPair_fst (e : ProxyDevEvent Q L) :
    (proxyDevPair e).1 = (proxyDevFst e).1 := rfl

@[simp] theorem proxyDevPair_snd (e : ProxyDevEvent Q L) :
    (proxyDevPair e).2 = (proxyDevSnd e).1 := rfl

@[simp] theorem proxyDevPair_mk (e₁ : ProxyEvent Q) (c : BinaryPairPalette L) :
    proxyDevPair (Q := Q) (e₁, c) = proxyEventPair e₁ := rfl

@[simp] theorem proxyDevColor_mk (e₁ : ProxyEvent Q) (c : BinaryPairPalette L) :
    proxyDevColor (Q := Q) (e₁, c) = c := rfl

/-- The two coordinates of a cost event are distinct, the colour playing no part. -/
theorem proxyDev_fst_ne_snd (e : ProxyDevEvent Q L) : proxyDevFst e ≠ proxyDevSnd e :=
  proxyEvent_fst_ne_snd e.1

/-! ### The deviant pairs and the cost -/

open Classical in
/-- The fine pairs whose palette-`c` density differs by more than `η` from that of the proxy
pair `pd`. -/
noncomputable def proxyDeviantFinePairs (M : FiniteRelModel L V) (c : BinaryPairPalette L)
    (η : ℝ) (F : Finpartition s) (pd : Finset V × Finset V) :
    Finset (Finset V × Finset V) :=
  (F.parts ×ˢ F.parts).filter fun p =>
    η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
      - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|

open Classical in
/-- **The cost of a selection**: the number of (proxy pair, colour) incidences at which the
two chosen representatives deviate by more than `η` from their proxy pair. -/
noncomputable def proxyDeviationCost (M : FiniteRelModel L V) (η : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) : ℝ :=
  ∑ e : ProxyDevEvent Q L,
    if (g (proxyDevFst e), g (proxyDevSnd e)) ∈
        proxyDeviantFinePairs M (proxyDevColor e) η F (proxyDevPair e)
      then (1 : ℝ) else 0

/-- The `hcost` input: the cost is nonnegative. -/
theorem proxyDeviationCost_nonneg (M : FiniteRelModel L V) (η : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) :
    0 ≤ proxyDeviationCost M η F Q g := by
  classical
  refine Finset.sum_nonneg fun e _ => ?_
  split <;> norm_num

/-! ### The aggregate deviant mass over cost events -/

open Classical in
/-- **Aggregate deviant mass over ALL cost events.** Summed over every ordered distinct
proxy pair and every colour, the deviant candidate-pair mass is at most `K` times the
witness's total deviant mass: `sum_proxyPair_deviant_le` is applied once per colour, and
each colour's proxy-pair sum is bounded once. Only the palette multiplicity is paid; the
number of proxy pairs multiplies nothing. -/
theorem sum_proxyDevEvent_mass_le (w : BinaryPaletteStrongDiagWitness M sch δ P₀) (q : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∑ e : ProxyDevEvent w.coarse L,
        ∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩
            (proxyCandidates (Q := w.coarse) w.fine q (proxyDevFst e) ×ˢ
              proxyCandidates (Q := w.coarse) w.fine q (proxyDevSnd e)),
          ((p.1.card : ℝ) * p.2.card)
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) := by
  classical
  -- Each cost event's mass sits inside its own proxy pair's deviant fine-fibre mass.
  have hsub : ∀ e : ProxyDevEvent w.coarse L,
      ∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩
          (proxyCandidates (Q := w.coarse) w.fine q (proxyDevFst e) ×ˢ
            proxyCandidates (Q := w.coarse) w.fine q (proxyDevSnd e)),
        ((p.1.card : ℝ) * p.2.card)
        ≤ ∑ p ∈ ((w.fine.parts.filter (· ⊆ (proxyDevPair e).1)) ×ˢ
            (w.fine.parts.filter (· ⊆ (proxyDevPair e).2))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M (proxyDevColor e)) p.1 p.2
            - pairDensity (HasBinaryPairPalette M (proxyDevColor e))
                (proxyDevPair e).1 (proxyDevPair e).2|),
          ((p.1.card : ℝ) * p.2.card) := by
    intro e
    rw [proxyDeviantFinePairs]
    exact sum_candidateMass_le_fibreMass w.fine q _ (proxyDevFst e) (proxyDevSnd e)
  calc ∑ e : ProxyDevEvent w.coarse L,
        ∑ p ∈ proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e) ∩ _, _
      ≤ ∑ e : ProxyDevEvent w.coarse L,
          ∑ p ∈ ((w.fine.parts.filter (· ⊆ (proxyDevPair e).1)) ×ˢ
              (w.fine.parts.filter (· ⊆ (proxyDevPair e).2))).filter
            (fun p => η < |pairDensity (HasBinaryPairPalette M (proxyDevColor e)) p.1 p.2
              - pairDensity (HasBinaryPairPalette M (proxyDevColor e))
                (proxyDevPair e).1 (proxyDevPair e).2|),
            ((p.1.card : ℝ) * p.2.card) := Finset.sum_le_sum fun e _ => hsub e
    _ = ∑ c : BinaryPairPalette L, ∑ e₁ : ProxyEvent w.coarse,
          ∑ p ∈ ((w.fine.parts.filter (· ⊆ e₁.1.1)) ×ˢ
              (w.fine.parts.filter (· ⊆ e₁.1.2))).filter
            (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
              - pairDensity (HasBinaryPairPalette M c) e₁.1.1 e₁.1.2|),
            ((p.1.card : ℝ) * p.2.card) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_comm
    _ ≤ ∑ _c : BinaryPairPalette L, δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine le_of_eq_of_le (Finset.sum_coe_sort (proxyPairEvents w.coarse) (fun pd =>
          ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ
              (w.fine.parts.filter (· ⊆ pd.2))).filter
            (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
              - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
            ((p.1.card : ℝ) * p.2.card))) ?_
        exact w.sum_proxyPair_deviant_le c hη
    _ = (Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ### The conditioned cost budget -/

open Classical in
/-- **Step 3: the `hexp` input.** The weighted expected deviation cost is at most
`K * (δ / η ^ 2 * #s ^ 2) / w₀ ^ 2` times the total selection weight. The route is the same
as in the forbidden channel: the expected-cost identity of `Finite/WeightedChoice.lean`
turns the expectation into per-event rectangle masses, the weight floor divides by `w₀ ^ 2`,
and the remaining aggregate is bounded by `sum_proxyPair_deviant_le` ONCE PER PALETTE. Only
the palette multiplicity `K` is paid — never the event-cardinality envelope, and no `9n²`
multiplier appears. -/
theorem expected_proxyDeviationCost_le (w : BinaryPaletteStrongDiagWitness M sch δ P₀)
    (q : ℕ) {η w₀ : ℝ} (hη : 0 < η) (hw₀ : 0 < w₀)
    (hW : ∀ C : ProxyIndex w.coarse,
      w₀ ≤ proxyCandidateWeight (Q := w.coarse) w.fine q C) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := w.coarse) w.fine q),
        (∏ j, ((g j).card : ℝ)) * proxyDeviationCost M η w.fine w.coarse g
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) / w₀ ^ 2
        * proxyTotalCandidateWeight w.fine q w.coarse := by
  classical
  simp only [proxyDeviationCost, proxyTotalCandidateWeight, proxyCandidateWeight]
  exact sum_piFinset_weight_mul_eventCost_le_of_weight_floor
    (proxyCandidates (Q := w.coarse) w.fine q) (fun A => (A.card : ℝ))
    (fun A => by positivity) proxyDevFst proxyDevSnd proxyDev_fst_ne_snd
    (fun e : ProxyDevEvent w.coarse L =>
      proxyDeviantFinePairs M (proxyDevColor e) η w.fine (proxyDevPair e))
    hw₀ hW (sum_proxyDevEvent_mass_le w q hη)

/-! ### Tests -/

section Tests

-- The cost is nonnegative, which is `hcost`.
example (M : FiniteRelModel L V) (η : ℝ) (F Q : Finpartition s) (g : ProxyIndex Q → Finset V) :
    0 ≤ proxyDeviationCost M η F Q g :=
  proxyDeviationCost_nonneg M η F Q g

-- A cost event's two coordinates are distinct: the colour is a passenger, not a coordinate.
example (e : ProxyDevEvent Q L) : proxyDevFst e ≠ proxyDevSnd e := proxyDev_fst_ne_snd e

-- Two cost events on the same proxy pair with different colours share both coordinates —
-- the colour multiplies the CHARGES, not the coordinates.
example (e₁ : ProxyEvent Q) (c c' : BinaryPairPalette L) :
    proxyDevFst (Q := Q) (e₁, c) = proxyDevFst (Q := Q) (e₁, c')
      ∧ proxyDevSnd (Q := Q) (e₁, c) = proxyDevSnd (Q := Q) (e₁, c') :=
  ⟨rfl, rfl⟩

-- The cost-event projections separate the proxy pair from the colour, so `e.1.1` never has
-- to be read as a pair and `e.2` never as a cell.
example (e₁ : ProxyEvent Q) (c : BinaryPairPalette L) :
    proxyDevPair (Q := Q) (e₁, c) = proxyEventPair e₁ ∧ proxyDevColor (Q := Q) (e₁, c) = c := by
  simp

-- A selection whose representatives never deviate costs nothing, however many proxy pairs
-- and colours there are: the cost counts incidences, not events.
example (M : FiniteRelModel L V) (η : ℝ) (F Q : Finpartition s) (g : ProxyIndex Q → Finset V)
    (hg : ∀ e : ProxyDevEvent Q L,
      (g (proxyDevFst e), g (proxyDevSnd e)) ∉
        proxyDeviantFinePairs M (proxyDevColor e) η F (proxyDevPair e)) :
    proxyDeviationCost M η F Q g = 0 := by
  classical
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg (hg e)]

end Tests

end RegularityLemmata
