/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.PolyadWitness
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The global energy increment for an arbitrary one-atom observable

The regularization iteration at its natural generality: a coloring `κ : RSet j α → Fin K`
of `j`-sets, an arbitrary decidable observable `obs` on ordered `(j+1)`-tuples, and the
`δ⁴` global energy increment that drives the iteration to a summit. The triadic
development of `Hypergraph/Triad.lean` and `Hypergraph/TriadIncrement.lean` is the
specialization at `j = 2`, `obs = triadObs H`.

Nothing here is dimension-specific. A **bad key** (`IsBadPolyad`) is one where local disc
regularity fails at the block's own density; the bad keys carry the mass
`badPolyadMassNum`, normalized by the frozen `|V|^{j+1}` convention to `badPolyadMass`.
That normalization is bounded by `1` through the generic block partition identity
`sum_card_polyadBlock` — the bad blocks are disjoint subsets of the injective
`(j+1)`-tuples — so no counting identity specific to a single arity enters.

The witness family is the **chosen simultaneous witness family**
(`badPolyadWitnessFamily`): an actual `DiscWitness` on each bad key, selected by
`Classical.choice` from `exists_discWitness`, and the empty face family on good keys — the
cut budget of `cutBound j K = K·2^(K^{j+1}·(j+1))` counts all possible tests even though
the good keys' cuts are constant. The increment
(`polyadEnergy_cutRefine_gain_of_badPolyadMass`) composes the exact refinement-variance
identity (`polyadEnergyNum_comp_variance`, through the merge identity
`cutRefineProj_comp`) with the strict local gain `δ³·|block| < variance` at every bad key
(`local_variance_gain`, itself already generic in `j` and `obs`), summed over the
(nonempty) bad-key set, then normalizes: the gain exceeds `δ³ · badPolyadMass > δ⁴`. This
is the index-increment step of the iteration toward the weak regularization summit,
following V. Rödl, M. Schacht, *Regular partitions of hypergraphs: Regularity lemmas*,
Combin. Probab. Comput. 16 (2007) — a precursor built from their index and polyad test
surfaces, not a formalization of their regular-partition theorem.

The iteration is **refinement-preserving**. Each round is a `cutRefine`, hence a
`ColoringRefines` step (`coloringRefines_cutRefine`), and the projections compose along
the induction, so the summit is exported in seeded form
(`exists_goodPolyadColoring_refining`): from an arbitrary starting coloring `κ₀`, an
output that still refines it. That is what lets the summit be inserted into a hierarchy,
where `κ₀` already encodes a constructed lower level;
`exists_goodPolyadColoring` is the trivial-seed specialization.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### Bad keys and their mass -/

/-- A **bad key**: the observable fails local disc regularity at the block's own density
(`IsLocalDiscRegular`, the canonical local predicate). -/
def IsBadPolyad (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs]
    (δ : ℝ) (key : Fin (j + 1) → Fin K) : Prop :=
  ¬ IsLocalDiscRegular κ obs key δ

/-- Unrealized keys are never bad (for `0 ≤ δ`). -/
theorem not_isBadPolyad_of_empty_block {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {δ : ℝ} {key : Fin (j + 1) → Fin K}
    (h : polyadBlock κ key = ∅) (hδ : 0 ≤ δ) : ¬ IsBadPolyad κ obs δ key :=
  not_not_intro (isLocalDiscRegular_of_empty_block h hδ)

/-- **Permutation closure of bad keys**, for a permutation-invariant observable: all
ordered presentations of an unordered polyad go bad together. -/
theorem isBadPolyad_comp_perm_iff (κ : RSet j α → Fin K)
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] (δ : ℝ) (key : Fin (j + 1) → Fin K)
    (σ : Equiv.Perm (Fin (j + 1))) (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ σ) ↔ obs w) :
    IsBadPolyad κ obs δ (key ∘ ⇑σ⁻¹) ↔ IsBadPolyad κ obs δ key :=
  not_congr (isLocalDiscRegular_comp_perm_iff σ hobs)

open Classical in
/-- The (ordered, diagonal-free) mass carried by the bad keys. -/
noncomputable def badPolyadMassNum (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) : ℝ :=
  ∑ key ∈ Finset.univ.filter (fun key => IsBadPolyad κ obs δ key),
    ((polyadBlock κ key).card : ℝ)

/-- Normalized bad mass, per the frozen `|V|^{j+1}` convention (guard-free on `V = ∅`). -/
noncomputable def badPolyadMass (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) : ℝ :=
  badPolyadMassNum κ obs δ / (Fintype.card α : ℝ) ^ (j + 1)

theorem badPolyadMassNum_nonneg (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    0 ≤ badPolyadMassNum κ obs δ :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem badPolyadMass_nonneg (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    0 ≤ badPolyadMass κ obs δ :=
  div_nonneg (badPolyadMassNum_nonneg κ obs δ) (by positivity)

/-- The bad mass is at most the total injective mass: the bad blocks are disjoint subsets
of the injective `(j+1)`-tuples, by the generic block partition identity. -/
theorem badPolyadMassNum_le_count (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    badPolyadMassNum κ obs δ ≤ (injectiveTupleCount α (j + 1) : ℝ) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => Nat.cast_nonneg _) (le_of_eq ?_)
  rw [← Nat.cast_sum]
  exact_mod_cast sum_card_polyadBlock κ

theorem badPolyadMass_le_one (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    badPolyadMass κ obs δ ≤ 1 := by
  rw [badPolyadMass]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hcard | hcard
  · rw [hcard]
    norm_num
  · rw [div_le_one (by positivity)]
    refine le_trans (badPolyadMassNum_le_count κ obs δ) ?_
    exact_mod_cast injectiveTupleCount_le_pow (α := α) (j + 1)

open Classical in
/-- The exceptional tuple set: all ordered `(j+1)`-tuples living in a bad block. -/
noncomputable def badPolyadTuples (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    Finset (Fin (j + 1) → α) :=
  (Finset.univ.filter fun key => IsBadPolyad κ obs δ key).biUnion (polyadBlock κ)

open Classical in
theorem card_badPolyadTuples (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    (badPolyadTuples κ obs δ).card
      = ∑ key ∈ Finset.univ.filter (fun key => IsBadPolyad κ obs δ key),
          (polyadBlock κ key).card := by
  classical
  rw [badPolyadTuples]
  exact Finset.card_biUnion fun key _ key' _ h => polyadBlock_disjoint h

theorem cast_card_badPolyadTuples (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    ((badPolyadTuples κ obs δ).card : ℝ) = badPolyadMassNum κ obs δ := by
  classical
  rw [card_badPolyadTuples, badPolyadMassNum, Nat.cast_sum]

/-! ### The chosen simultaneous witness family -/

/-- The chosen simultaneous witness family: an actual witness on each bad key (classical
choice), the empty face family elsewhere. -/
noncomputable def badPolyadWitnessFamily (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (δ : ℝ) :
    (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α) := by
  classical
  exact fun key =>
    if h : IsBadPolyad κ obs δ key then (exists_discWitness h).some.faces
    else fun _ => ∅

/-- On a bad key, the chosen family is an actual witness's face system. -/
theorem badPolyadWitnessFamily_spec {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {δ : ℝ}
    {key : Fin (j + 1) → Fin K} (h : IsBadPolyad κ obs δ key) :
    ∃ w : DiscWitness κ obs key δ, badPolyadWitnessFamily κ obs δ key = w.faces := by
  classical
  refine ⟨(exists_discWitness h).some, ?_⟩
  rw [badPolyadWitnessFamily]
  simp only [dite_eq_left h]

/-! ### The global increment -/

/-- **The global increment**: if the bad keys carry more than a `δ` fraction of the
`(j+1)`-tuple mass, one simultaneous cut round strictly gains more than `δ⁴` of
normalized energy. -/
theorem polyadEnergy_cutRefine_gain_of_badPolyadMass {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ)
    (hbad : δ < badPolyadMass κ obs δ) :
    δ ^ 4 < polyadEnergy (cutRefine κ (badPolyadWitnessFamily κ obs δ)) obs
        - polyadEnergy κ obs := by
  classical
  set W := badPolyadWitnessFamily κ obs δ with hWdef
  -- The host is nonempty (otherwise the bad mass is 0 and `δ < 0`).
  have hV : (0 : ℝ) < (Fintype.card α : ℝ) ^ (j + 1) := by
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
    · exfalso
      rw [badPolyadMass, h0, Nat.cast_zero, zero_pow (Nat.succ_ne_zero j), div_zero] at hbad
      linarith
    · positivity
  -- The exact variance identity, with the merge rewritten back to `κ`.
  have hvar := polyadEnergyNum_comp_variance (cutRefineProj (j := j) (K := K))
    (cutRefine κ W) obs
  rw [cutRefineProj_comp κ W] at hvar
  -- The bad keys alone force the variance above `δ³ · badPolyadMassNum`.
  have hne : (Finset.univ.filter fun key : Fin (j + 1) → Fin K =>
      IsBadPolyad κ obs δ key).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [badPolyadMass, badPolyadMassNum, hempty, Finset.sum_empty, zero_div] at hbad
    linarith
  have hstep : δ ^ 3 * badPolyadMassNum κ obs δ
      < ∑ P : Fin (j + 1) → Fin K,
          ∑ Q ∈ Finset.univ.filter fun Q : Fin (j + 1) → Fin (cutBound j K) =>
            (fun i => cutRefineProj (Q i)) = P,
            ((polyadBlock (cutRefine κ W) Q).card : ℝ)
              * (densityOn (polyadBlock (cutRefine κ W) Q) obs
                  - densityOn (polyadBlock κ P) obs) ^ 2 := by
    rw [badPolyadMassNum, Finset.mul_sum]
    refine lt_of_lt_of_le (Finset.sum_lt_sum_of_nonempty hne fun P hP => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun P _ _ => Finset.sum_nonneg fun Q _ =>
          mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rw [Finset.mem_filter] at hP
    obtain ⟨w, hw⟩ := badPolyadWitnessFamily_spec hP.2
    exact local_variance_gain hδ W w hw
  have h1 : δ ^ 3 * badPolyadMassNum κ obs δ
      < polyadEnergyNum (cutRefine κ W) obs - polyadEnergyNum κ obs := by
    rw [hvar]
    exact hstep
  -- Normalize.
  have h2 : δ ^ 4
      < (δ ^ 3 * badPolyadMassNum κ obs δ) / (Fintype.card α : ℝ) ^ (j + 1) := by
    rw [mul_div_assoc, show δ ^ 4 = δ ^ 3 * δ from by ring]
    refine mul_lt_mul_of_pos_left ?_ (by positivity)
    rw [badPolyadMass] at hbad
    exact hbad
  calc δ ^ 4
      < (δ ^ 3 * badPolyadMassNum κ obs δ) / (Fintype.card α : ℝ) ^ (j + 1) := h2
    _ ≤ (polyadEnergyNum (cutRefine κ W) obs
          - polyadEnergyNum κ obs) / (Fintype.card α : ℝ) ^ (j + 1) :=
        div_le_div_of_nonneg_right h1.le hV.le
    _ = polyadEnergy (cutRefine κ W) obs - polyadEnergy κ obs := by
        rw [polyadEnergy, polyadEnergy, sub_div]

/-! ### Bounded iteration and the weak summit -/

/-- The color budget of `t` rounds of simultaneous cutting starting from `K` colors: the
exact frozen recurrence, iterating `cutBound j`. -/
def polyadRegularityBound (j : ℕ) : ℕ → ℕ → ℕ
  | 0, K => K
  | t + 1, K => polyadRegularityBound j t (cutBound j K)

theorem le_polyadRegularityBound (j t K : ℕ) : K ≤ polyadRegularityBound j t K := by
  induction t generalizing K with
  | zero => exact le_refl K
  | succ t ih =>
    refine le_trans ?_ (ih (cutBound j K))
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * 2 ^ (K ^ (j + 1) * (j + 1)) := Nat.mul_le_mul_left K (Nat.one_le_two_pow)

/-- **The existential fuel theorem, refinement-preserving**: once the remaining energy
budget is below `t · δ⁴`, some coloring with at most `polyadRegularityBound j t K` colors
**refines the one it started from** and has bad mass at most `δ`.

Every round is a `cutRefine`, hence a refinement (`coloringRefines_cutRefine`); the
projections compose along the induction by `ColoringRefines.trans`. Preserving the
projection is what makes the summit usable when `κ` already encodes structure — a
prescribed vertex partition, a family of lower-arity colorings, or a lower level of a
complex. -/
theorem exists_goodPolyadColoring_of_fuel_refining {obs : (Fin (j + 1) → α) → Prop}
    [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (K : ℕ) (κ : RSet j α → Fin K)
    (hbudget : 1 - polyadEnergy κ obs ≤ (t : ℝ) * δ ^ 4) :
    ∃ (K' : ℕ) (κ' : RSet j α → Fin K'),
      K' ≤ polyadRegularityBound j t K ∧ ColoringRefines κ' κ ∧
        badPolyadMass κ' obs δ ≤ δ := by
  induction t generalizing K κ with
  | zero =>
    refine ⟨K, κ, le_refl _, ColoringRefines.refl κ, ?_⟩
    by_contra hbad
    rw [not_le] at hbad
    have hgain := polyadEnergy_cutRefine_gain_of_badPolyadMass hδ hbad
    have hle := polyadEnergy_le_one
      (cutRefine κ (badPolyadWitnessFamily κ obs δ)) obs
    have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
    rw [Nat.cast_zero, zero_mul] at hbudget
    linarith
  | succ t ih =>
    by_cases hgood : badPolyadMass κ obs δ ≤ δ
    · exact ⟨K, κ, le_polyadRegularityBound j (t + 1) K, ColoringRefines.refl κ, hgood⟩
    · rw [not_le] at hgood
      have hgain := polyadEnergy_cutRefine_gain_of_badPolyadMass hδ hgood
      obtain ⟨K', κ', hcard, href, hbad⟩ :=
        ih (cutBound j K) (cutRefine κ (badPolyadWitnessFamily κ obs δ)) (by
          rw [Nat.cast_succ] at hbudget
          linarith)
      exact ⟨K', κ', hcard, href.trans (coloringRefines_cutRefine κ _), hbad⟩

/-- **The existential fuel theorem**: once the remaining energy budget is below `t · δ⁴`,
some coloring with at most `polyadRegularityBound j t K` colors has bad mass at most `δ`.
Each failing round strictly gains `δ⁴` of energy and multiplies the colors by at most one
`cutBound j` step. The refinement-forgetting form of
`exists_goodPolyadColoring_of_fuel_refining`. -/
theorem exists_goodPolyadColoring_of_fuel {obs : (Fin (j + 1) → α) → Prop}
    [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) (t : ℕ) (K : ℕ) (κ : RSet j α → Fin K)
    (hbudget : 1 - polyadEnergy κ obs ≤ (t : ℝ) * δ ^ 4) :
    ∃ (K' : ℕ) (κ' : RSet j α → Fin K'),
      K' ≤ polyadRegularityBound j t K ∧ badPolyadMass κ' obs δ ≤ δ := by
  obtain ⟨K', κ', hcard, _, hbad⟩ :=
    exists_goodPolyadColoring_of_fuel_refining hδ t K κ hbudget
  exact ⟨K', κ', hcard, hbad⟩

/-- The iteration fuel: `⌈1/δ⁴⌉₊` rounds suffice from any starting energy. -/
noncomputable def polyadFuel (δ : ℝ) : ℕ := ⌈1 / δ ^ 4⌉₊

/-- The host-independent color bound of the weak summit: `polyadFuel δ` rounds of
`cutBound j`, starting from the trivial `1`-coloring. -/
noncomputable def polyadBound (j : ℕ) (δ : ℝ) : ℕ := polyadRegularityBound j (polyadFuel δ) 1

/-- The fuel budget is available from **any** seed coloring: the polyad energy is
nonnegative and `polyadFuel δ` rounds already exhaust a budget of `1`. -/
theorem one_sub_polyadEnergy_le_polyadFuel_mul {K₀ : ℕ} (κ₀ : RSet j α → Fin K₀)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) :
    1 - polyadEnergy κ₀ obs ≤ (polyadFuel δ : ℝ) * δ ^ 4 := by
  have hE := polyadEnergy_nonneg κ₀ obs
  have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
  have hceil : 1 / δ ^ 4 ≤ (polyadFuel δ : ℝ) := Nat.le_ceil _
  calc 1 - polyadEnergy κ₀ obs
      ≤ 1 := by linarith
    _ = (1 / δ ^ 4) * δ ^ 4 := by field_simp
    _ ≤ (polyadFuel δ : ℝ) * δ ^ 4 := mul_le_mul_of_nonneg_right hceil hδ4.le

/-- **The seeded weak regularization summit**: from an arbitrary starting coloring `κ₀` of
`j`-sets, a coloring that **refines** it, has at most
`polyadRegularityBound j (polyadFuel δ) K₀` colors, and whose bad keys carry at most a `δ`
fraction of the ordered `(j+1)`-tuple mass.

This is the form required to insert the summit into a hierarchy: `κ₀` may already
represent a constructed lower level, and `ColoringRefines` guarantees it survives.
`exists_goodPolyadColoring` is the trivial-seed specialization. -/
theorem exists_goodPolyadColoring_refining {K₀ : ℕ} (κ₀ : RSet j α → Fin K₀)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet j α → Fin K'),
      K' ≤ polyadRegularityBound j (polyadFuel δ) K₀ ∧ ColoringRefines κ' κ₀ ∧
        badPolyadMass κ' obs δ ≤ δ :=
  exists_goodPolyadColoring_of_fuel_refining hδ (polyadFuel δ) K₀ κ₀
    (one_sub_polyadEnergy_le_polyadFuel_mul κ₀ obs hδ)

/-- **The weak regularization summit**: for every decidable observable on ordered
`(j+1)`-tuples there is a coloring of `j`-sets with at most `polyadBound j δ` colors whose
bad keys carry at most a `δ` fraction of the ordered `(j+1)`-tuple mass. The trivial-seed
specialization of `exists_goodPolyadColoring_refining`. -/
theorem exists_goodPolyadColoring (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet j α → Fin K'),
      K' ≤ polyadBound j δ ∧ badPolyadMass κ' obs δ ≤ δ := by
  obtain ⟨K', κ', hcard, _, hbad⟩ :=
    exists_goodPolyadColoring_refining (fun _ : RSet j α => (0 : Fin 1)) obs hδ
  exact ⟨K', κ', hcard, hbad⟩

/-! ### Tests and adversarial examples -/

section Tests

-- The frozen recurrence, numerically, at each small arity: one round from a single color
-- costs `cutBound j 1 = 2^(j+1)` colors.
example : polyadRegularityBound 0 1 1 = 2 := by decide

example : polyadRegularityBound 1 1 1 = 4 := by decide

example : polyadRegularityBound 2 1 1 = 8 := by decide

-- The color budget only grows along rounds, at every arity.
example (j : ℕ) : (5 : ℕ) ≤ polyadRegularityBound j 3 5 := le_polyadRegularityBound j 3 5

-- **Empty host**: with no vertices there are no injective tuples, so the bad mass is `0`
-- and the summit hypothesis `δ < badPolyadMass` is unsatisfiable for `0 < δ`.
example {obs : (Fin 3 → PEmpty.{1}) → Prop} [DecidablePred obs]
    (κ : RSet 2 PEmpty.{1} → Fin 2) (δ : ℝ) (hδ : 0 < δ)
    (h : δ < badPolyadMass κ obs δ) : False := by
  classical
  have hzero : badPolyadMassNum κ obs δ = 0 := by
    refine Finset.sum_eq_zero fun key _ => ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
    exact (v 0).elim
  rw [badPolyadMass, hzero, zero_div] at h
  linarith

-- **Arity 0**: the degenerate one-set case is a genuine instance — `RSet 0 α` is a single
-- point and the "polyads" are `1`-tuples.
example (obs : (Fin 1 → Fin 4) → Prop) [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 0 (Fin 4) → Fin K'),
      K' ≤ polyadBound 0 δ ∧ badPolyadMass κ' obs δ ≤ δ :=
  exists_goodPolyadColoring obs hδ

-- **Arity 1**: colorings of vertices, observables on ordered pairs — the graph case.
example (obs : (Fin 2 → Fin 4) → Prop) [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 1 (Fin 4) → Fin K'),
      K' ≤ polyadBound 1 δ ∧ badPolyadMass κ' obs δ ≤ δ :=
  exists_goodPolyadColoring obs hδ

-- **Arity 2**: colorings of pairs, observables on ordered triples — the triadic case.
example (obs : (Fin 3 → Fin 4) → Prop) [DecidablePred obs] {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 2 (Fin 4) → Fin K'),
      K' ≤ polyadBound 2 δ ∧ badPolyadMass κ' obs δ ≤ δ :=
  exists_goodPolyadColoring obs hδ

-- **A nonsymmetric observable**: nothing in the development assumes permutation
-- invariance. Here `obs v = (v 0 < v 1)` is antisymmetric, so it is not invariant under
-- the transposition — yet the seeded summit applies unchanged.
example {δ : ℝ} (hδ : 0 < δ) {K₀ : ℕ} (κ₀ : RSet 1 (Fin 4) → Fin K₀) :
    ∃ (K' : ℕ) (κ' : RSet 1 (Fin 4) → Fin K'),
      K' ≤ polyadRegularityBound 1 (polyadFuel δ) K₀ ∧ ColoringRefines κ' κ₀ ∧
        badPolyadMass κ' (fun v : Fin 2 → Fin 4 => v 0 < v 1) δ ≤ δ :=
  exists_goodPolyadColoring_refining κ₀ _ hδ

-- The nonsymmetric observable really is nonsymmetric: it fails the permutation-invariance
-- hypothesis of `isBadPolyad_comp_perm_iff`.
example : ¬ ∀ (w : Fin 2 → Fin 4) (σ : Equiv.Perm (Fin 2)),
    ((w ∘ σ) 0 < (w ∘ σ) 1 ↔ w 0 < w 1) := by
  intro h
  exact absurd (h ![0, 1] (Equiv.swap 0 1)) (by decide)

-- Statement-level instance of the global increment at triadic types.
example (κ : RSet 2 (Fin 5) → Fin 2) (obs : (Fin 3 → Fin 5) → Prop) [DecidablePred obs]
    (δ : ℝ) (hδ : 0 < δ) (hbad : δ < badPolyadMass κ obs δ) :
    δ ^ 4 < polyadEnergy (cutRefine κ (badPolyadWitnessFamily κ obs δ)) obs
        - polyadEnergy κ obs :=
  polyadEnergy_cutRefine_gain_of_badPolyadMass hδ hbad

end Tests

end RegularityLemmata
