/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxyAggregateMass
import RegularityLemmata.Finite.WeightedChoice

/-!
# Route (b) ladder step 2: weighted choice on proxy cells, and the forbidden-event budgets

`ARCHITECTURE.md` route (b) ladder step 2, final unit, **steps 1 and 2 of five**: the index
and event types on which `Finite/WeightedChoice.lean` is instantiated, and the conversion of
the aggregate nonuniform mass into that machine's forbidden-event hypothesis. The cost
budget, the constants and the summit are steps 3–5 and are NOT here.

`Finite/WeightedChoice.lean` is untouched: it is already indexed by an abstract event type
with two distinct coordinates, which is exactly what this file supplies.

## Step 1 — the instantiation

* `ProxyIndex Q` — the selection coordinates: one per PROXY cell, so a selection chooses one
  representative fine cell inside every proxy.
* `ProxyEvent Q` — the forbidden events: an ordered distinct proxy pair. **No palette
  component.** In `exists_piFinset_forall_not_mem_bad_cost_le` the event type occurs only in
  `hbad`; the cost hypothesis `hexp` mentions `cost` alone. Palettes are NOT event
  coordinates. They enter the forbidden channel through the UNION of the per-palette
  nonuniform sets, and the cost channel through aggregate deviation. Multiplying them into
  the event index would be a different and wasteful thing: it would carry the palette count
  into the event cardinality rather than into the forbidden set.
* `proxyEventFst`, `proxyEventSnd`, `proxyEvent_fst_ne_snd` — the two coordinates and the
  distinctness the machine demands. Sibling pairs are events like any other.
* `proxyCandidates` — the candidate family, `repCandidates` of the fine partition inside
  each proxy, reused unchanged: the rebuild changes the INDEX, not the candidate notion.
* `prod_sum_proxyCandidates_pos` — `hWpos`, from the half-mass theorem proxy by proxy.

## Step 2 — the forbidden-event budget

* `sum_event_mass_le_of_weight_floor` — the generic factorization. For each event the
  omitted product `∏_{j ≠ i₁ e, i₂ e} W j` equals `(∏_j W j) / (W (i₁ e) * W (i₂ e))`, so a
  uniform floor `w₀ ≤ W j` turns the whole `hbad` left-hand side into
  `(aggregate mass) / w₀ ^ 2 * ∏_j W j`. **The event count does not appear** — each event
  contributes its own mass, never a copy of the total.
* `sum_proxyEvent_nonuniform_mass_le` — that factorization instantiated on proxies for a
  SINGLE relation, with the aggregate supplied by `sum_proxyPair_nonuniform_le`. The
  resulting admissible `σ` is `badMassDiagNum R ε F / w₀ ^ 2`, in which no `9n²` event-count
  multiplier occurs.
* `sum_le_sum_of_exists_mem` — the union bound over colours: a set covered by finitely many
  sets has mass at most the summed masses.
* `sum_proxyEvent_paletteNonuniform_mass_le` — **the simultaneous budget**, which is what the
  selection actually needs. The forbidden set `paletteNonuniformFinePairs` is the union over
  palette colours of the per-palette nonuniform sets, and its budget is
  `K * B / w₀ ^ 2` times the total weight, where `K = Fintype.card (BinaryPairPalette L)` and
  `B` bounds each palette's bad mass. The factor `K` is necessary for SIMULTANEOUS palette
  uniformity and comes from the union over colours; it is not an event-count factor, and no
  `9n²` multiplier occurs here either.

## Steps 3–5, not done here

The conditioned cost budget from `sum_proxyPair_deviant_le`; the candidate-weight and
proxy-size constants that discharge `σ < 1`; the summit. `ARCHITECTURE.md` waits for the
completed theorem and its actual constants.
-/

namespace RegularityLemmata

open FirstOrder

/-! ### The generic factorization -/

section Factorization

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] {E : Type*} [Fintype E]

/-- **The forbidden-event budget is the aggregate mass divided by the squared weight
floor.** For an event `e` the product `WeightedChoice` omits is the total product divided by
the two coordinate weights, so a uniform floor `w₀` on the coordinate weights converts the
`hbad` left-hand side into the AGGREGATE forbidden mass over all events, scaled by
`w₀ ^ (-2)` and the total product. The number of events never multiplies anything: each
event contributes only its own mass. -/
theorem sum_event_mass_le_of_weight_floor (t : ι → Finset β) (wt : β → ℝ)
    (hwt : ∀ x, 0 ≤ wt x) (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e)
    (Bad : E → Finset (β × β)) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ j, w₀ ≤ ∑ x ∈ t j, wt x) :
    ∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ x ∈ t j, wt x
      ≤ (∑ e : E, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) / w₀ ^ 2
        * ∏ j, ∑ x ∈ t j, wt x := by
  classical
  set W : ι → ℝ := fun j => ∑ x ∈ t j, wt x with hWdef
  have hWpos : ∀ j, 0 < W j := fun j => lt_of_lt_of_le hw₀ (hW j)
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  -- The inner sum factors: the omitted product does not depend on the pair.
  have hmass : (0 : ℝ) ≤ ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hwt _) (hwt _)
  rw [← Finset.sum_mul]
  -- The omitted product is the total product divided by the two coordinate weights.
  have hmem₂ : i₂ e ∈ Finset.univ.erase (i₁ e) :=
    Finset.mem_erase.mpr ⟨(hne e).symm, Finset.mem_univ _⟩
  have hsplit : W (i₁ e) * (W (i₂ e) * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j)
      = ∏ j, W j := by
    rw [Finset.mul_prod_erase _ W hmem₂, Finset.mul_prod_erase _ W (Finset.mem_univ (i₁ e))]
  have hrest : (0 : ℝ) ≤ ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j :=
    Finset.prod_nonneg fun j _ => (hWpos j).le
  have hbound : ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j ≤ (∏ j, W j) / w₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j) * w₀ ^ 2
        ≤ (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j) * (W (i₁ e) * W (i₂ e)) := by
          have := mul_le_mul (hW (i₁ e)) (hW (i₂ e)) hw₀.le (hWpos (i₁ e)).le
          nlinarith [hrest]
      _ = ∏ j, W j := by rw [← hsplit]; ring
  calc (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2)
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), W j
      ≤ (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) * ((∏ j, W j) / w₀ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hmass
    _ = (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), wt p.1 * wt p.2) / w₀ ^ 2 * ∏ j, W j := by
        ring

/-- **The union bound over colours.** A set every element of which lies in at least one of
finitely many sets has mass at most the summed masses. This is where a palette factor comes
from when one forbidden condition must hold for EVERY colour simultaneously: the forbidden
set is the union of the per-colour ones, not a product of the event index with the colours. -/
theorem sum_le_sum_of_exists_mem {γ κ : Type*} [DecidableEq γ] [Fintype κ]
    (S : Finset γ) (T : κ → Finset γ) (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcov : ∀ x ∈ S, ∃ k, x ∈ T k) :
    ∑ x ∈ S, f x ≤ ∑ k, ∑ x ∈ T k, f x := by
  classical
  calc ∑ x ∈ S, f x
      ≤ ∑ x ∈ S, ∑ k : κ, (if x ∈ T k then f x else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨k, hk⟩ := hcov x hx
        have hterm : f x = (if x ∈ T k then f x else 0) := by rw [if_pos hk]
        refine le_trans (le_of_eq hterm) (Finset.single_le_sum
          (f := fun k => if x ∈ T k then f x else 0)
          (fun k _ => by by_cases h : x ∈ T k <;> simp [h, hf x]) (Finset.mem_univ k))
    _ = ∑ k : κ, ∑ x ∈ S, (if x ∈ T k then f x else 0) := Finset.sum_comm
    _ ≤ ∑ k : κ, ∑ x ∈ T k, f x := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_ite_mem]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          fun x _ _ => hf x

end Factorization

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### The coordinates and the events -/

/-- The selection coordinates: one per PROXY cell. A selection assigns each proxy a
representative fine cell. -/
abbrev ProxyIndex (Q : Finpartition s) : Type _ := {C : Finset V // C ∈ Q.parts}

/-- The forbidden events: an ordered DISTINCT proxy pair. Sibling pairs — two proxies of one
owner — are events like any other, and there is deliberately no palette component: palettes
enter only through the cost channel. -/
abbrev ProxyEvent (Q : Finpartition s) : Type _ :=
  {pd : Finset V × Finset V // pd ∈ proxyPairEvents Q}

variable {Q : Finpartition s}

/-- The first coordinate of an event. -/
def proxyEventFst (e : ProxyEvent Q) : ProxyIndex Q :=
  ⟨e.1.1, (mem_proxyPairEvents.mp e.2).1⟩

/-- The second coordinate of an event. -/
def proxyEventSnd (e : ProxyEvent Q) : ProxyIndex Q :=
  ⟨e.1.2, (mem_proxyPairEvents.mp e.2).2.1⟩

/-- **The two coordinates are distinct** — the hypothesis `WeightedChoice` demands of an
event index, and the reason self-pairs are excluded from `proxyPairEvents`. -/
theorem proxyEvent_fst_ne_snd (e : ProxyEvent Q) : proxyEventFst e ≠ proxyEventSnd e := by
  intro h
  exact (mem_proxyPairEvents.mp e.2).2.2 (Subtype.ext_iff.mp h)

/-! ### The candidate family and its total weight -/

/-- The candidate family: inside each proxy, the `repCandidates` of the fine partition.
Reused unchanged — the proxy rebuild changes the INDEX, not the candidates. -/
def proxyCandidates (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) : Finset (Finset V) :=
  repCandidates F q C.1

theorem proxyCandidates_subset_fibre (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) :
    proxyCandidates (Q := Q) F q C ⊆ F.parts.filter (· ⊆ C.1) :=
  Finset.filter_subset _ _

theorem proxyCandidates_nonempty {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) (hCpos : 0 < C.1.card) :
    (proxyCandidates (Q := Q) F q C).Nonempty :=
  repCandidates_nonempty hFQ C.2 hq hCpos

/-- Each proxy's candidate weight is at least half its size, hence positive. -/
theorem sum_card_proxyCandidates_pos {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) :
    0 < ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ) := by
  have hCpos : (0 : ℝ) < (C.1.card : ℝ) := by
    have := Finset.card_pos.mpr (Q.nonempty_of_mem_parts C.2)
    exact_mod_cast this
  have := half_le_sum_card_repCandidates hFQ C.2 hq
  rw [proxyCandidates]
  linarith

/-- **The half-mass theorem is the weight floor.** Every proxy's candidate weight is at
least half the proxy's size, so a size floor on proxies gives the uniform `w₀` the
factorization needs. -/
theorem half_card_le_sum_card_proxyCandidates {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) :
    (C.1.card : ℝ) / 2 ≤ ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ) :=
  half_le_sum_card_repCandidates hFQ C.2 hq

/-- **The total selection weight is positive** — `hWpos` of the conditioned-cost form,
obtained proxy by proxy from the half-mass theorem. -/
theorem prod_sum_proxyCandidates_pos {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) :
    0 < ∏ C : ProxyIndex Q, ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ) :=
  Finset.prod_pos fun C _ => sum_card_proxyCandidates_pos hFQ hq C

/-! ### The forbidden events: nonuniform fine pairs -/

open Classical in
/-- The forbidden set, the same for every event: pairs of fine cells that are not
`ε`-uniform. Intersected with the event's own candidate rectangle by `WeightedChoice`. -/
noncomputable def nonuniformFinePairs (R : V → V → Prop) [DecidableRel R] (ε : ℝ)
    (F : Finpartition s) :
    Finset (Finset V × Finset V) :=
  (F.parts ×ˢ F.parts).filter fun p => ¬ IsUniformPair R p.1 p.2 ε

open Classical in
/-- **Step 2: the forbidden-event budget.** The `hbad` left-hand side of
`exists_piFinset_forall_not_mem_bad_cost_le`, instantiated on proxy cells and proxy-pair
events, is at most `badMassDiagNum R ε F / w₀ ^ 2` times the total selection weight. The
admissible `σ` is therefore that quotient: the aggregate mass, bounded ONCE by
`sum_proxyPair_nonuniform_le`, against the squared weight floor. No `9n²` event-count
multiplier appears — the factorization gives each event its own mass and nothing else. -/
theorem sum_proxyEvent_nonuniform_mass_le (R : V → V → Prop) [DecidableRel R] {ε : ℝ}
    (F : Finpartition s) (q : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ C : ProxyIndex Q, w₀ ≤ ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ)) :
    ∑ e : ProxyEvent Q,
        ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
            proxyCandidates (Q := Q) F q (proxyEventSnd e)),
          (p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ)
      ≤ badMassDiagNum R ε F / w₀ ^ 2
        * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) := by
  classical
  refine le_trans (sum_event_mass_le_of_weight_floor (proxyCandidates (Q := Q) F q)
    (fun A => (A.card : ℝ)) (fun A => by positivity) proxyEventFst proxyEventSnd
    proxyEvent_fst_ne_snd (fun _ => nonuniformFinePairs R ε F) hw₀ hW) ?_
  have hprod : (0 : ℝ) ≤ ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun A _ => by positivity
  refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by positivity)) hprod
  -- Each event's forbidden mass sits inside its own proxy pair's fine-fibre mass, so the
  -- sum over events is the aggregate — bounded once, with no event-count factor.
  have hsub : ∀ e : ProxyEvent Q,
      ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
        ≤ ∑ p ∈ ((F.parts.filter (· ⊆ e.1.1)) ×ˢ (F.parts.filter (· ⊆ e.1.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) := by
    intro e
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
    rw [Finset.mem_inter, Finset.mem_product, nonuniformFinePairs, Finset.mem_filter] at hp
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨proxyCandidates_subset_fibre F q (proxyEventFst e) hp.2.1,
      proxyCandidates_subset_fibre F q (proxyEventSnd e) hp.2.2⟩, hp.1.2⟩
  calc ∑ e : ProxyEvent Q,
        ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
      ≤ ∑ e : ProxyEvent Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ e.1.1)) ×ˢ (F.parts.filter (· ⊆ e.1.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) :=
        Finset.sum_le_sum fun e _ => hsub e
    _ = ∑ pd ∈ proxyPairEvents Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) :=
        Finset.sum_coe_sort (proxyPairEvents Q) (fun pd =>
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card))
    _ ≤ badMassDiagNum R ε F := sum_proxyPair_nonuniform_le R F Q

/-! ### The simultaneous forbidden budget over all palettes -/

section Palettes

variable {L : FirstOrder.Language} [FiniteRelational L]

open Classical in
/-- **The forbidden set for SIMULTANEOUS palette uniformity.** A fine pair is forbidden as
soon as it fails `ε`-uniformity for SOME palette colour — the union of the per-colour
forbidden sets. This is how palettes enter the forbidden channel: as a union inside `Bad`,
never as a coordinate of the event index. -/
noncomputable def paletteNonuniformFinePairs (M : FiniteRelModel L V) (ε : ℝ)
    (F : Finpartition s) : Finset (Finset V × Finset V) :=
  (F.parts ×ˢ F.parts).filter fun p =>
    ∃ c : BinaryPairPalette L, ¬ IsUniformPair (HasBinaryPairPalette M c) p.1 p.2 ε

open Classical in
/-- The union is covered colour by colour: every forbidden pair is forbidden for some
specific colour. -/
theorem exists_mem_nonuniformFinePairs {M : FiniteRelModel L V} {ε : ℝ} {F : Finpartition s}
    {p : Finset V × Finset V} (hp : p ∈ paletteNonuniformFinePairs M ε F) :
    ∃ c : BinaryPairPalette L, p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F := by
  rw [paletteNonuniformFinePairs, Finset.mem_filter] at hp
  obtain ⟨c, hc⟩ := hp.2
  exact ⟨c, Finset.mem_filter.mpr ⟨hp.1, hc⟩⟩

open Classical in
/-- Conversely each colour's forbidden set sits inside the union, which is why the palette
factor below cannot be avoided: simultaneous uniformity really does forbid every colour's
bad pairs. -/
theorem nonuniformFinePairs_subset_palette (M : FiniteRelModel L V) (ε : ℝ)
    (F : Finpartition s) (c : BinaryPairPalette L) :
    nonuniformFinePairs (HasBinaryPairPalette M c) ε F ⊆ paletteNonuniformFinePairs M ε F := by
  intro p hp
  rw [nonuniformFinePairs, Finset.mem_filter] at hp
  exact Finset.mem_filter.mpr ⟨hp.1, ⟨c, hp.2⟩⟩

open Classical in
/-- **The simultaneous forbidden-event budget.** With `Bad e` the union over palette colours
of the per-colour nonuniform pairs, the `hbad` left-hand side is at most `K * B / w₀ ^ 2`
times the total selection weight, where `K = Fintype.card (BinaryPairPalette L)` and `B`
bounds each colour's diagonal-inclusive bad mass. The factor `K` is necessary for
SIMULTANEOUS palette uniformity and comes from the union over colours — it is not an
event-count factor, and no `9n²` multiplier appears: the per-colour budget
`sum_proxyEvent_nonuniform_mass_le` is applied once per colour and is itself event-count
free. -/
theorem sum_proxyEvent_paletteNonuniform_mass_le (M : FiniteRelModel L V) {ε : ℝ}
    (F : Finpartition s) (q : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ C : ProxyIndex Q, w₀ ≤ ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ))
    {B : ℝ} (hB : ∀ c : BinaryPairPalette L,
      badMassDiagNum (HasBinaryPairPalette M c) ε F ≤ B) :
    ∑ e : ProxyEvent Q,
        ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
            (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
              proxyCandidates (Q := Q) F q (proxyEventSnd e)),
          (p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ)
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B / w₀ ^ 2
        * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) := by
  classical
  have hprod : (0 : ℝ) ≤ ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun A _ => by positivity
  -- Colour by colour: the union's mass is at most the summed per-colour masses.
  have hstep : ∀ e : ProxyEvent Q,
      ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
          (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
            proxyCandidates (Q := Q) F q (proxyEventSnd e)),
        ((p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ))
      ≤ ∑ c : BinaryPairPalette L,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ)) := by
    intro e
    refine sum_le_sum_of_exists_mem _
      (fun c => nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
        (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e))) _
      (fun p => by positivity) (fun p hp => ?_)
    rw [Finset.mem_inter] at hp
    obtain ⟨c, hc⟩ := exists_mem_nonuniformFinePairs hp.1
    exact ⟨c, Finset.mem_inter.mpr ⟨hc, hp.2⟩⟩
  have hsum : ∑ _c : BinaryPairPalette L, B
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  calc ∑ e : ProxyEvent Q, ∑ p ∈ paletteNonuniformFinePairs M ε F ∩ _, _
      ≤ ∑ e : ProxyEvent Q, ∑ c : BinaryPairPalette L,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ)) :=
        Finset.sum_le_sum fun e _ => hstep e
    _ = ∑ c : BinaryPairPalette L, ∑ e : ProxyEvent Q,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ)) := Finset.sum_comm
    _ ≤ ∑ c : BinaryPairPalette L, badMassDiagNum (HasBinaryPairPalette M c) ε F / w₀ ^ 2
          * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) :=
        Finset.sum_le_sum fun c _ =>
          sum_proxyEvent_nonuniform_mass_le (HasBinaryPairPalette M c) F q hw₀ hW
    _ ≤ ∑ _c : BinaryPairPalette L, B / w₀ ^ 2
          * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hB c) (by positivity)) hprod
    _ = (∑ _c : BinaryPairPalette L, B) / w₀ ^ 2
          * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
    _ ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B / w₀ ^ 2
          * ∏ j, ∑ A ∈ proxyCandidates (Q := Q) F q j, (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsum (by positivity)) hprod

end Palettes

/-! ### Tests -/

section Tests

-- The two event coordinates are always distinct, so `WeightedChoice`'s `hne` is available
-- for every event — including sibling events.
example (e : ProxyEvent Q) : proxyEventFst e ≠ proxyEventSnd e := proxyEvent_fst_ne_snd e

-- A sibling pair really does give an event, whose two coordinates are the two siblings.
example {A B : Finset V} (hA : A ∈ Q.parts) (hB : B ∈ Q.parts) (hAB : A ≠ B) :
    (proxyEventFst (Q := Q) ⟨(A, B), mem_proxyPairEvents.mpr ⟨hA, hB, hAB⟩⟩).1 = A ∧
      (proxyEventSnd (Q := Q) ⟨(A, B), mem_proxyPairEvents.mpr ⟨hA, hB, hAB⟩⟩).1 = B :=
  ⟨rfl, rfl⟩

-- The candidates are the unchanged `repCandidates`: the rebuild changes the index, not the
-- candidate notion.
example (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) :
    proxyCandidates (Q := Q) F q C = repCandidates F q C.1 := rfl

-- Every colour's forbidden set lies inside the union, which is why the palette factor `K`
-- cannot be dropped: simultaneous uniformity forbids every colour's bad pairs at once.
example {L : FirstOrder.Language} [FiniteRelational L] (M : FiniteRelModel L V) (ε : ℝ)
    (F : Finpartition s) (c : BinaryPairPalette L) :
    nonuniformFinePairs (HasBinaryPairPalette M c) ε F ⊆ paletteNonuniformFinePairs M ε F :=
  nonuniformFinePairs_subset_palette M ε F c

-- …and the union is not everything: a pair uniform for EVERY colour is not forbidden, so
-- the union really is the simultaneous condition and not a blanket exclusion.
example {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V} {ε : ℝ}
    {F : Finpartition s} {p : Finset V × Finset V}
    (hp : ∀ c : BinaryPairPalette L, IsUniformPair (HasBinaryPairPalette M c) p.1 p.2 ε) :
    p ∉ paletteNonuniformFinePairs M ε F := by
  classical
  intro hmem
  obtain ⟨c, hc⟩ := exists_mem_nonuniformFinePairs hmem
  rw [nonuniformFinePairs, Finset.mem_filter] at hc
  exact hc.2 (hp c)

-- The union bound charges once per COLOUR and not once per anything else: with a single
-- covering set the bound is the mass itself, so no cardinality factor is hidden in it.
example {γ : Type*} [DecidableEq γ] (S : Finset γ) (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ S, f x ≤ ∑ _k : Unit, ∑ x ∈ S, f x :=
  sum_le_sum_of_exists_mem S (fun _ : Unit => S) f hf fun _ hx => ⟨(), hx⟩

-- The factorization is genuinely event-count free: with an EMPTY forbidden family the
-- budget is zero however many events there are.
example {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] {E : Type*} [Fintype E]
    (t : ι → Finset β) (i₁ i₂ : E → ι) (hne : ∀ e, i₁ e ≠ i₂ e) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ j, w₀ ≤ ∑ _ ∈ t j, (1 : ℝ)) :
    ∑ e : E, ∑ _ ∈ (∅ : Finset (β × β)) ∩ (t (i₁ e) ×ˢ t (i₂ e)), (1 : ℝ) * 1
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ _ ∈ t j, (1 : ℝ)
      ≤ (∑ e : E, ∑ _ ∈ (∅ : Finset (β × β)) ∩ (t (i₁ e) ×ˢ t (i₂ e)), (1 : ℝ) * 1) / w₀ ^ 2
        * ∏ j, ∑ _ ∈ t j, (1 : ℝ) :=
  sum_event_mass_le_of_weight_floor t (fun _ => 1) (fun _ => zero_le_one) i₁ i₂ hne
    (fun _ => ∅) hw₀ hW

end Tests

end RegularityLemmata
