/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Strong
import RegularityLemmata.Graph.FamilyRefinement

/-!
# Strong regularity for a finite family, via energy-gap stopping

The family counterpart of `Graph/Strong.lean`. A **family strong witness** for a finite
directed family `Rk : Fin K → α → α → Prop`, an error schedule `E`, and a gap `δ` is a
coarse partition and a fine refinement that is `E(#coarse)`-regular **for every relation of
the family at once**, gaining at most `δ` of family energy over the coarse partition.

Two things change from the single-relation development, and only two:

* the energy ceiling is `K` rather than `1` (`familyEnergy_le_card`), so the stopping fuel
  is `⌈K/δ⌉` rather than `⌈1/δ⌉`;
* each round is `exists_familyRegular_refinement` rather than `exists_regular_refinement`,
  so the one-round part-count bound is `regularityBound ⌈K/E(k)⁵⌉ k`, and
  `familyMonoStepBound` is its monotone majorant.

Everything else composes for free. The round is an **exact** refinement of its input, so
`coarse ≤ P₀` follows by transitivity exactly as in `strong_iterate`; no equitability
hypothesis and no exceptional class enters anywhere.

The consumer API extracts a single relation from the bundle. `energy_le_of_familyEnergy_le`
is the component gap: a family-energy gap of `δ` across a refinement gives each component a
gap of `δ`, because the other `K − 1` summands are individually monotone and cancel.
`FamilyStrongWitness.toStrongWitness` packages that into the single-relation
`StrongWitness`. Two per-relation conclusions follow and are kept distinct:
`fine_badMass_le` is the regularity field at one component (bad mass within the schedule's
tolerance), while `deviant_mass_le` is the exceptional-mass consequence — density shifts
from the coarse parent exceeding `η` carry mass at most `(δ/η²)·|s|²`, matching
`StrongWitness.deviant_mass_le` with **no factor of `K`**, since each component receives the
full gap `δ`.

`BinaryPaletteStrongWitness` (`Relational/BinaryStrong.lean`) is **not** an instance of
this: palette colors partition every ordered pair, so its energy ceiling is `1` and its
fuel `⌈1/δ⌉`, both genuinely sharper than the family ceiling `K` and fuel `⌈K/δ⌉` available
here. Only its per-color handoff is routed through this file's API.

The architecture is the standard strong-regularity iteration (T. Tao, *Szemerédi's
regularity lemma revisited*, Contrib. Discrete Math. 1 (2006); see also Y. Zhao, *Graph
Theory and Additive Combinatorics*, ch. 2), run on the library's mass-weighted family
energy.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α} {K : ℕ}

/-! ### The component energy gap -/

/-- **Summand descent.** If every summand of `g` is dominated by the corresponding summand
of `f`, then a bound `∑ f ≤ ∑ g + δ` on the totals descends to each index separately:
`f i ≤ g i + δ`. The other summands cancel rather than absorbing the slack, so the constant
does **not** pick up a factor of the index count.

This is the shared content of every "aggregate gap bounds each component's gap" lemma in
the library: the family energy over `Fin K` here, and the palette energy over
`BinaryPairPalette L` in `Relational/BinaryStrong.lean`. It is stated for an arbitrary
finite index type because neither consumer needs anything more. -/
theorem summand_le_add_of_sum_le_add {ι : Type*} [Fintype ι]
    {f g : ι → ℝ} (hmono : ∀ i, g i ≤ f i) {δ : ℝ}
    (h : ∑ i, f i ≤ ∑ i, g i + δ) (i : ι) : f i ≤ g i + δ := by
  classical
  have hother : ∑ j ∈ Finset.univ.erase i, g j ≤ ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_le_sum fun j _ => hmono j
  have hfsplit : ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hgsplit : ∑ j, g j = g i + ∑ j ∈ Finset.univ.erase i, g j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hfsplit, hgsplit] at h
  linarith

section Component

variable {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]

/-- **The component gap.** A family-energy gap of `δ` across a refinement hands each
relation of the family the same gap. The other `K − 1` summands are monotone under
refinement, so they cancel from both sides rather than absorbing the slack.

This is the direction opposite to `familyEnergy_add_le_of_component`, which lifts a
component *gain* to the family; here a family *gap* descends to every component. -/
theorem energy_le_of_familyEnergy_le {Q P : Finpartition s} (hQP : Q ≤ P) {δ : ℝ}
    (h : familyEnergy Rk Q ≤ familyEnergy Rk P + δ) (k : Fin K) :
    energy (Rk k) Q ≤ energy (Rk k) P + δ :=
  summand_le_add_of_sum_le_add (fun j => energy_mono (Rk j) hQP) h k

end Component

/-! ### The witness -/

variable (Rk : Fin K → α → α → Prop) [∀ k, DecidableRel (Rk k)]

/-- A family strong regularity witness against a starting partition `P₀`: a coarse
refinement of `P₀` and a fine refinement of it, regular at the schedule's tolerance for the
coarse complexity **for every relation of the family**, with a family-energy gap of at most
`δ`. -/
structure FamilyStrongWitness (E : ErrorSchedule) (δ : ℝ) (P₀ : Finpartition s) where
  /-- The coarse partition. -/
  coarse : Finpartition s
  /-- The fine partition. -/
  fine : Finpartition s
  coarse_le : coarse ≤ P₀
  fine_le : fine ≤ coarse
  /-- The fine partition is regular for every relation at the tolerance chosen against the
  coarse complexity. -/
  fine_regular : IsFamilyRegular Rk (E coarse.parts.card) fine
  /-- The fine refinement gains at most `δ` of family energy. -/
  energy_gap : familyEnergy Rk fine ≤ familyEnergy Rk coarse + δ

/-! ### The monotone step bound -/

/-- Monotone majorant of the one-round family part-count bound
`m ↦ regularityBound ⌈K/E(m)⁵⌉ m`. The family size enters only through the fuel of a single
round. -/
noncomputable def familyMonoStepBound (E : ErrorSchedule) (K m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup fun j => regularityBound ⌈(K : ℝ) / (E j) ^ 5⌉₊ j

theorem familyStepBound_le_familyMonoStepBound (E : ErrorSchedule) (K m : ℕ) :
    regularityBound ⌈(K : ℝ) / (E m) ^ 5⌉₊ m ≤ familyMonoStepBound E K m := by
  unfold familyMonoStepBound
  exact Finset.le_sup (f := fun j => regularityBound ⌈(K : ℝ) / (E j) ^ 5⌉₊ j)
    (Finset.self_mem_range_succ m)

theorem le_familyMonoStepBound (E : ErrorSchedule) (K m : ℕ) :
    m ≤ familyMonoStepBound E K m :=
  le_trans (le_regularityBound _ _) (familyStepBound_le_familyMonoStepBound E K m)

theorem familyMonoStepBound_mono (E : ErrorSchedule) (K : ℕ) {m m' : ℕ} (h : m ≤ m') :
    familyMonoStepBound E K m ≤ familyMonoStepBound E K m' := by
  unfold familyMonoStepBound
  exact Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

theorem familyMonoStepBound_iterate_mono (E : ErrorSchedule) (K i : ℕ) {m m' : ℕ}
    (h : m ≤ m') :
    (familyMonoStepBound E K)^[i] m ≤ (familyMonoStepBound E K)^[i] m' := by
  induction i generalizing m m' with
  | zero => simpa using h
  | succ i IH =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact IH (familyMonoStepBound_mono E K h)

theorem le_familyMonoStepBound_iterate (E : ErrorSchedule) (K i m : ℕ) :
    m ≤ (familyMonoStepBound E K)^[i] m := by
  induction i with
  | zero => simp
  | succ i IH =>
    rw [Function.iterate_succ_apply]
    exact le_trans IH (familyMonoStepBound_iterate_mono E K i (le_familyMonoStepBound E K m))

theorem familyMonoStepBound_iterate_le_iterate (E : ErrorSchedule) (K : ℕ) {i j : ℕ}
    (hij : i ≤ j) (m : ℕ) :
    (familyMonoStepBound E K)^[i] m ≤ (familyMonoStepBound E K)^[j] m := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ j IH =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · refine le_trans (IH (by omega)) ?_
      rw [Function.iterate_succ_apply]
      exact familyMonoStepBound_iterate_mono E K j (le_familyMonoStepBound E K m)
    · have hi : i = j + 1 := by omega
      rw [hi]

/-! ### Existence by energy-gap stopping -/

/-- Fuel-parametrized family strong iteration: from family energy within `t · δ` of the
ceiling `K`, `t` restarts suffice.

Each round is `exists_familyRegular_refinement`, an **exact** refinement of its input, so
the coarse partition's refinement of the seed is carried by transitivity. The budget is
stated against the ceiling `K`, which is the only place the family size appears. -/
theorem familyStrong_iterate (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ) :
    ∀ (t : ℕ) (P : Finpartition s), (K : ℝ) - (t : ℝ) * δ ≤ familyEnergy Rk P →
      ∃ w : FamilyStrongWitness Rk E δ P,
        w.coarse.parts.card ≤ (familyMonoStepBound E K)^[t] P.parts.card ∧
        w.fine.parts.card ≤ (familyMonoStepBound E K)^[t + 1] P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_familyRegular_refinement Rk P (E.pos P.parts.card)
    have hgap : familyEnergy Rk Q ≤ familyEnergy Rk P + δ := by
      have h1 : familyEnergy Rk Q ≤ (K : ℝ) := familyEnergy_le_card
      have h2 : (K : ℝ) ≤ familyEnergy Rk P := by simpa using hbudget
      linarith
    refine ⟨⟨P, Q, le_rfl, hQP, hQreg, hgap⟩, by simp, ?_⟩
    calc Q.parts.card
        ≤ regularityBound ⌈(K : ℝ) / (E P.parts.card) ^ 5⌉₊ P.parts.card := hQcard
      _ ≤ familyMonoStepBound E K P.parts.card :=
          familyStepBound_le_familyMonoStepBound E K _
      _ = (familyMonoStepBound E K)^[0 + 1] P.parts.card := by simp
  | succ t IH =>
    intro P hbudget
    obtain ⟨Q, hQP, hQreg, hQcard⟩ :=
      exists_familyRegular_refinement Rk P (E.pos P.parts.card)
    have hQmono : Q.parts.card ≤ familyMonoStepBound E K P.parts.card :=
      le_trans hQcard (familyStepBound_le_familyMonoStepBound E K _)
    by_cases hgap : familyEnergy Rk Q ≤ familyEnergy Rk P + δ
    · refine ⟨⟨P, Q, le_rfl, hQP, hQreg, hgap⟩,
        le_familyMonoStepBound_iterate E K _ _, ?_⟩
      calc Q.parts.card ≤ familyMonoStepBound E K P.parts.card := hQmono
        _ = (familyMonoStepBound E K)^[1] P.parts.card := rfl
        _ ≤ (familyMonoStepBound E K)^[t + 1 + 1] P.parts.card :=
            familyMonoStepBound_iterate_le_iterate E K (by omega) _
    · rw [not_le] at hgap
      have hbudget' : (K : ℝ) - (t : ℝ) * δ ≤ familyEnergy Rk Q := by
        push_cast at hbudget
        nlinarith [hgap, hbudget]
      obtain ⟨w, hwc, hwf⟩ := IH Q hbudget'
      refine ⟨⟨w.coarse, w.fine, w.coarse_le.trans hQP, w.fine_le, w.fine_regular,
        w.energy_gap⟩, ?_, ?_⟩
      · calc w.coarse.parts.card ≤ (familyMonoStepBound E K)^[t] Q.parts.card := hwc
          _ ≤ (familyMonoStepBound E K)^[t] (familyMonoStepBound E K P.parts.card) :=
              familyMonoStepBound_iterate_mono E K t hQmono
          _ = (familyMonoStepBound E K)^[t + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm
      · calc w.fine.parts.card ≤ (familyMonoStepBound E K)^[t + 1] Q.parts.card := hwf
          _ ≤ (familyMonoStepBound E K)^[t + 1] (familyMonoStepBound E K P.parts.card) :=
              familyMonoStepBound_iterate_mono E K _ hQmono
          _ = (familyMonoStepBound E K)^[t + 1 + 1] P.parts.card :=
              (Function.iterate_succ_apply _ _ _).symm

/-- **Family strong regularity.** Every starting partition admits a family strong witness
for any positive error schedule and gap, with explicit host-independent part-count bounds.

The fuel is `⌈K/δ⌉`, linear in the family size, because the family-energy ceiling is `K`
rather than `1`. -/
theorem exists_familyStrongWitness (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ)
    (P₀ : Finpartition s) :
    ∃ w : FamilyStrongWitness Rk E δ P₀,
      w.coarse.parts.card ≤ (familyMonoStepBound E K)^[⌈(K : ℝ) / δ⌉₊] P₀.parts.card ∧
      w.fine.parts.card ≤ (familyMonoStepBound E K)^[⌈(K : ℝ) / δ⌉₊ + 1] P₀.parts.card := by
  refine familyStrong_iterate Rk E hδ _ P₀ ?_
  have h0 : (0 : ℝ) ≤ familyEnergy Rk P₀ := familyEnergy_nonneg
  have ht : (K : ℝ) ≤ (⌈(K : ℝ) / δ⌉₊ : ℝ) * δ := by
    calc (K : ℝ) = (K : ℝ) / δ * δ := by field_simp
      _ ≤ (⌈(K : ℝ) / δ⌉₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le
  linarith

/-! ### The consumer API -/

namespace FamilyStrongWitness

variable {Rk} {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-- Each relation of the family inherits the gap: the component form of `energy_gap`. -/
theorem component_energy_gap (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) :
    energy (Rk k) w.fine ≤ energy (Rk k) w.coarse + δ :=
  energy_le_of_familyEnergy_le w.fine_le w.energy_gap k

/-- **The single-relation projection**: a family strong witness is a strong witness for
each relation of the family, at the *same* schedule and the *same* gap. The coarse
complexity — and therefore the tolerance the fine partition is regular at — is the family
witness's, so the projection is faithful rather than a re-derivation. -/
def toStrongWitness (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) :
    StrongWitness (Rk k) E δ P₀ where
  coarse := w.coarse
  fine := w.fine
  coarse_le := w.coarse_le
  fine_le := w.fine_le
  fine_regular := w.fine_regular k
  energy_gap := w.component_energy_gap k

@[simp] theorem toStrongWitness_coarse (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) :
    (w.toStrongWitness k).coarse = w.coarse := rfl

@[simp] theorem toStrongWitness_fine (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) :
    (w.toStrongWitness k).fine = w.fine := rfl

/-- **The per-relation regularity conclusion**: for each relation, the fine partition's
normalized bad mass is within the tolerance chosen against the coarse complexity. This is
the regularity field read off one component; it is *not* the exceptional-mass bound — see
`deviant_mass_le` for that. -/
theorem fine_badMass_le (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) :
    badMass (Rk k) (E w.coarse.parts.card) w.fine ≤ E w.coarse.parts.card :=
  w.fine_regular k

/-- **Exceptional-mass (Markov) consequence, per relation.** For each relation, the mass of
refined rectangles whose density shifts from their coarse parent by more than `η` is at
most `(δ/η²)·|s|²` — the same bound `StrongWitness.deviant_mass_le` gives, with no factor of
`K`, because `component_energy_gap` hands each relation the full gap `δ`. -/
theorem deviant_mass_le (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) {η : ℝ}
    (hη : 0 < η) :
    ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (Rk k) p.1 p.2 - pairDensity (Rk k) pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
  StrongWitness.deviant_mass_le (R := Rk k) (w.toStrongWitness k) hη

end FamilyStrongWitness

/-! ### Endpoints -/

/-- **The empty-family endpoint.** With no relations there is nothing to regularize, so the
seed is already its own witness: `coarse = fine = P₀`, no refinement and no restart. This
pins "stops immediately" as an explicit witness rather than as the zero-fuel case of the
general bound. -/
def familyStrongWitness_zero (Rk : Fin 0 → α → α → Prop) [∀ k, DecidableRel (Rk k)]
    (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ) (P₀ : Finpartition s) :
    FamilyStrongWitness Rk E δ P₀ where
  coarse := P₀
  fine := P₀
  coarse_le := le_rfl
  fine_le := le_rfl
  fine_regular := isFamilyRegular_zero Rk
  energy_gap := by linarith

@[simp] theorem familyStrongWitness_zero_coarse (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ)
    (P₀ : Finpartition s) : (familyStrongWitness_zero Rk E hδ P₀).coarse = P₀ := rfl

@[simp] theorem familyStrongWitness_zero_fine (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ)
    (P₀ : Finpartition s) : (familyStrongWitness_zero Rk E hδ P₀).fine = P₀ := rfl

/-- The singleton family's step bound is literally the single-relation one: at `K = 1` the
fuel `⌈K/E(j)⁵⌉` of each round is `⌈1/E(j)⁵⌉`. -/
theorem familyMonoStepBound_one (E : ErrorSchedule) :
    familyMonoStepBound E 1 = monoStepBound E := by
  funext m
  rw [familyMonoStepBound, monoStepBound]
  exact Finset.sup_congr rfl fun j _ => by rw [Nat.cast_one]

/-- **The singleton endpoint.** One relation recovers the single-relation strong shape
exactly: the projected witness satisfies the *ordinary* `monoStepBound` coarse and fine
bounds of `exists_strongWitness`, not merely a family-shaped analogue of them. -/
theorem exists_familyStrongWitness_single (R : α → α → Prop) [DecidableRel R]
    (E : ErrorSchedule) {δ : ℝ} (hδ : 0 < δ) (P₀ : Finpartition s) :
    ∃ w : StrongWitness R E δ P₀,
      w.coarse.parts.card ≤ (monoStepBound E)^[⌈(1 : ℝ) / δ⌉₊] P₀.parts.card ∧
      w.fine.parts.card ≤ (monoStepBound E)^[⌈(1 : ℝ) / δ⌉₊ + 1] P₀.parts.card := by
  obtain ⟨w, hc, hf⟩ := exists_familyStrongWitness (fun _ : Fin 1 => R) E hδ P₀
  rw [familyMonoStepBound_one] at hc hf
  exact ⟨w.toStrongWitness 0, by simpa using hc, by simpa using hf⟩

/-! ### Tests and adversarial examples -/

section Tests

-- The family step bound dominates the identity, at every family size.
example (K : ℕ) : (3 : ℕ) ≤ familyMonoStepBound ⟨fun _ => 1, fun _ => one_pos⟩ K 3 :=
  le_familyMonoStepBound _ K 3

-- **Repeated relations.** A family of `m` identical copies of one relation still stops
-- within the `⌈m/δ⌉` fuel: the ceiling argument counts summands, and never assumes the
-- relations are distinct.
example (R : α → α → Prop) [DecidableRel R] (m : ℕ) (E : ErrorSchedule) {δ : ℝ}
    (hδ : 0 < δ) (P₀ : Finpartition s) :
    ∃ w : FamilyStrongWitness (fun _ : Fin m => R) E δ P₀,
      w.coarse.parts.card ≤ (familyMonoStepBound E m)^[⌈(m : ℝ) / δ⌉₊] P₀.parts.card :=
  (exists_familyStrongWitness _ E hδ P₀).imp fun _ h => h.1

-- The projection is faithful: every relation of a repeated family reads the same coarse
-- complexity, hence the same tolerance.
example (R : α → α → Prop) [DecidableRel R] (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition s) (w : FamilyStrongWitness (fun _ : Fin 3 => R) E δ P₀)
    (j k : Fin 3) :
    (w.toStrongWitness j).coarse.parts.card = (w.toStrongWitness k).coarse.parts.card :=
  rfl

-- Family strong regularity instantiated on a tiny host with a constant schedule.
example (P₀ : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    ∃ w : FamilyStrongWitness (fun k : Fin 2 => fun a b : Fin 3 => a + k.val < b)
        ⟨fun _ => 1 / 2, fun _ => by norm_num⟩ (1 / 2) P₀,
      w.coarse.parts.card
        ≤ (familyMonoStepBound ⟨fun _ => 1 / 2, fun _ => by norm_num⟩ 2)^[⌈(2 : ℝ) / (1 / 2)⌉₊]
            P₀.parts.card :=
  (exists_familyStrongWitness _ _ (by norm_num) P₀).imp fun _ h => h.1

-- The empty-family witness really is the seed on both sides — no refinement happens.
example (Rk : Fin 0 → α → α → Prop) [∀ k, DecidableRel (Rk k)] (E : ErrorSchedule) {δ : ℝ}
    (hδ : 0 < δ) (P₀ : Finpartition s) :
    (familyStrongWitness_zero Rk E hδ P₀).coarse = P₀ ∧
      (familyStrongWitness_zero Rk E hδ P₀).fine = P₀ :=
  ⟨rfl, rfl⟩

-- The exceptional-mass bound carries no `K`: each relation gets `δ/η²·|s|²`, the same
-- constant a single-relation strong witness gives.
example {K : ℕ} (Rk : Fin K → α → α → Prop) [∀ k, DecidableRel (Rk k)] (E : ErrorSchedule)
    {δ : ℝ} {P₀ : Finpartition s} (w : FamilyStrongWitness Rk E δ P₀) (k : Fin K) {η : ℝ}
    (hη : 0 < η) :
    ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (Rk k) p.1 p.2 - pairDensity (Rk k) pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
  w.deviant_mass_le k hη

-- The component gap is not vacuous slack: a family gap of `δ` really does bound each
-- summand's gap by `δ`, not by `K·δ`.
example {K : ℕ} (Rk : Fin K → α → α → Prop) [∀ k, DecidableRel (Rk k)]
    {Q P : Finpartition s} (hQP : Q ≤ P) {δ : ℝ}
    (h : familyEnergy Rk Q ≤ familyEnergy Rk P + δ) (k : Fin K) :
    energy (Rk k) Q ≤ energy (Rk k) P + δ :=
  energy_le_of_familyEnergy_le hQP h k

end Tests

end RegularityLemmata
