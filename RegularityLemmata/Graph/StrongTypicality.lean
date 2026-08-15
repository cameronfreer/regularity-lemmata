/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.FamilyStrong

/-!
# Typical coarse pairs and the second Markov step

The consumer layer above a strong witness. `StrongWitness.deviant_mass_le` converts the
energy gap into a *global* bound on the mass of refined rectangles whose density shifts
from their coarse parent by more than `η`. This file names the **per-coarse-pair**
summand (`deviantChildMass`), calls a coarse pair **typical** when its own deviant child
mass is small *relative to the pair's mass*, and applies Markov a second time to bound the
mass of the coarse pairs that fail.

The reusable core is `deviantMass_mul_sq_le_refinementVarianceNum`: the deviant mass times
`η²` is dominated by the refinement variance. Beyond `0 ≤ η` it assumes nothing — no
witness, and not even that the fine partition refines the coarse one — which is exactly
what lets it be summed over a family before any normalization happens.

## The family bound carries no factor of `K`

For a `FamilyStrongWitness`, "typical" means typical **for every relation**, taken
pointwise (`FamilyStrongWitness.IsTypicalCoarsePair`). The exceptional bound is
nevertheless `(δ/(η²θ))·|s|²`, with **no `K`** — the same constant as for one relation.

The `K` would appear if one union-bounded the per-relation projections, since each
`w.toStrongWitness k` separately admits `δ/η²` and there are `K` of them. That is avoidable
because a family witness has *one* aggregate energy gap, not `K` coincident ones. The route
here sums first and applies Markov once:

* `sum_refinementVarianceNum_eq` — the summed parallel-axis identity, over the family;
* `FamilyStrongWitness.sum_refinementVarianceNum_le` — that sum is at most `δ·|s|²`,
  straight from the single `energy_gap` field;
* `FamilyStrongWitness.sum_deviantMass_le` — one Markov step on the total.

Pointwise typicality survives this because failure is *monotone into the sum*: if some
component's deviant child mass exceeds `θ·|A|·|B|`, then so does the sum over components,
every summand being nonnegative. So the pointwise-atypical set is contained in the set
where the aggregate exceeds the threshold, and the aggregate bound applies to it directly.
This is weaker as a hypothesis than demanding the *total* component mass be below the
threshold, and it is the version a consumer wants.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α} {K : ℕ}

/-! ### The summed parallel-axis identity -/

section SummedVariance

variable {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]

/-- **The summed parallel-axis identity.** Over a finite family, the refinement variances add
up to the family-energy gain scaled by `|s|²`. Each summand is the single-relation identity
`refinementVarianceNum_eq`, renormalized by the all-host `energyNum_eq_energy_mul`; the
family energy is by definition the sum of the component energies, so nothing else is
needed. -/
theorem sum_refinementVarianceNum_eq {Q P : Finpartition s} (hQP : Q ≤ P) :
    ∑ k, refinementVarianceNum (Rk k) Q P
      = (familyEnergy Rk Q - familyEnergy Rk P) * (s.card : ℝ) ^ 2 := by
  rw [familyEnergy, familyEnergy, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [refinementVarianceNum_eq (Rk k) hQP, energyNum_eq_energy_mul, energyNum_eq_energy_mul,
    sub_mul]

end SummedVariance

/-- **The hard-stop checkpoint, cleared.** A family strong witness's component refinement
variances sum to at most `δ·|s|²` — from the single aggregate `energy_gap` field, with no
appeal to the individual components' gaps. This is what makes every downstream constant
`K`-free. -/
theorem FamilyStrongWitness.sum_refinementVarianceNum_le
    {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)] {E : ErrorSchedule} {δ : ℝ}
    {P₀ : Finpartition s} (w : FamilyStrongWitness Rk E δ P₀) :
    ∑ k, refinementVarianceNum (Rk k) w.fine w.coarse ≤ δ * (s.card : ℝ) ^ 2 := by
  rw [sum_refinementVarianceNum_eq w.fine_le]
  exact mul_le_mul_of_nonneg_right (by linarith [w.energy_gap]) (by positivity)

/-! ### Deviant child mass -/

variable (R : α → α → Prop) [DecidableRel R]

/-- The mass of refined child rectangles inside one coarse pair whose density shifts from
that pair's own density by more than `η`. `deviantMass` is its sum over coarse pairs, and
is the quantity `StrongWitness.deviant_mass_le` bounds globally. -/
noncomputable def deviantChildMass (Q : Finpartition s) (η : ℝ)
    (pd : Finset α × Finset α) : ℝ :=
  ∑ p ∈ ((Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2))).filter
      (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|),
    ((p.1.card : ℝ) * p.2.card)

/-- The total deviant mass across all coarse pairs. -/
noncomputable def deviantMass (Q P : Finpartition s) (η : ℝ) : ℝ :=
  ∑ pd ∈ P.parts ×ˢ P.parts, deviantChildMass R Q η pd

variable {R}

theorem deviantChildMass_nonneg {Q : Finpartition s} {η : ℝ}
    {pd : Finset α × Finset α} : 0 ≤ deviantChildMass R Q η pd :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem deviantMass_nonneg {Q P : Finpartition s} {η : ℝ} : 0 ≤ deviantMass R Q P η :=
  Finset.sum_nonneg fun _ _ => deviantChildMass_nonneg

/-- **The Markov core.** The deviant mass times `η²` is dominated by the refinement
variance: every deviant child contributes at least `η²` per unit of mass, and the
non-deviant children contribute nonnegatively.

Stated for arbitrary partitions: beyond `0 ≤ η` (without which `η < |x|` would not give
`η² ≤ x²`) there is no witness and no refinement hypothesis, so the inequality can be summed
over a family before any normalization happens. This is the lemma whose reuse makes the
aggregate bound `K`-free. -/
theorem deviantMass_mul_sq_le_refinementVarianceNum (Q P : Finpartition s) {η : ℝ}
    (hη : 0 ≤ η) : deviantMass R Q P η * η ^ 2 ≤ refinementVarianceNum R Q P := by
  classical
  rw [deviantMass, Finset.sum_mul, refinementVarianceNum]
  refine Finset.sum_le_sum fun pd _ => ?_
  rw [deviantChildMass, Finset.sum_mul]
  calc ∑ p ∈ (((Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|)),
        ((p.1.card : ℝ) * p.2.card) * η ^ 2
      ≤ ∑ p ∈ (((Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2|)),
          ((p.1.card : ℝ) * p.2.card)
            * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter] at hp
        have hdev := hp.2
        have hsq : η ^ 2 ≤ (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 := by
          nlinarith [sq_abs (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2),
            abs_nonneg (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2)]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ ∑ p ∈ (Q.parts.filter (· ⊆ pd.1)) ×ˢ (Q.parts.filter (· ⊆ pd.2)),
          ((p.1.card : ℝ) * p.2.card)
            * (pairDensity R p.1 p.2 - pairDensity R pd.1 pd.2) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun p _ _ => by positivity

/-! ### Typical coarse pairs -/

section Typical

variable {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-- A coarse pair is **`(η, θ)`-typical** when its deviant child mass is at most a `θ`
fraction of the pair's own mass. The threshold is relative, so typicality is a statement
about the pair and not about the host. -/
def StrongWitness.IsTypicalCoarsePair (w : StrongWitness R E δ P₀) (η θ : ℝ)
    (pd : Finset α × Finset α) : Prop :=
  deviantChildMass R w.fine η pd ≤ θ * ((pd.1.card : ℝ) * pd.2.card)

open Classical in
/-- The mass carried by the coarse pairs that fail `(η, θ)` typicality. -/
noncomputable def StrongWitness.atypicalMass (w : StrongWitness R E δ P₀) (η θ : ℝ) : ℝ :=
  ∑ pd ∈ (w.coarse.parts ×ˢ w.coarse.parts).filter
      (fun pd => ¬ w.IsTypicalCoarsePair η θ pd), ((pd.1.card : ℝ) * pd.2.card)

/-- The global deviant mass of a strong witness, in the named form. -/
theorem StrongWitness.deviantMass_le (w : StrongWitness R E δ P₀) {η : ℝ} (hη : 0 < η) :
    deviantMass R w.fine w.coarse η ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
  StrongWitness.deviant_mass_le R w hη

/-- **The ordinary second Markov step.** The mass of coarse pairs that fail `(η, θ)`
typicality is at most `(δ/(η²θ))·|s|²`. The first Markov step is inside
`deviantMass_mul_sq_le_refinementVarianceNum`; this is the second, applied to the coarse
pairs rather than to the refined rectangles. -/
theorem StrongWitness.atypicalMass_le (w : StrongWitness R E δ P₀) {η θ : ℝ}
    (hη : 0 < η) (hθ : 0 < θ) :
    w.atypicalMass η θ ≤ δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2 := by
  classical
  have hstep : θ * w.atypicalMass η θ ≤ deviantMass R w.fine w.coarse η := by
    rw [StrongWitness.atypicalMass, Finset.mul_sum, deviantMass]
    refine le_trans (Finset.sum_le_sum fun pd hpd => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun pd _ _ => deviantChildMass_nonneg)
    rw [Finset.mem_filter, StrongWitness.IsTypicalCoarsePair, not_le] at hpd
    linarith [hpd.2]
  have h1 : θ * w.atypicalMass η θ ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
    le_trans hstep (w.deviantMass_le hη)
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have hgoal : δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2
      = (δ / η ^ 2 * (s.card : ℝ) ^ 2) / θ := by
    field_simp
  rw [hgoal, le_div_iff₀ hθ]
  exact (mul_comm _ _).trans_le h1

end Typical

/-! ### The aggregate family version -/

section FamilyTypical

variable {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)] {E : ErrorSchedule}
  {δ : ℝ} {P₀ : Finpartition s}

/-- **The aggregate deviant-mass bound.** Summed over the whole family, the deviant mass is
at most `(δ/η²)·|s|²` — the same constant as for a single relation, with **no factor of
`K`**.

The route is the point: sum the Markov cores first
(`deviantMass_mul_sq_le_refinementVarianceNum` needs no witness), then apply the single
aggregate variance bound once. Union-bounding the `K` per-relation projections would give
`K·δ/η²` instead. -/
theorem FamilyStrongWitness.sum_deviantMass_le (w : FamilyStrongWitness Rk E δ P₀) {η : ℝ}
    (hη : 0 < η) :
    ∑ k, deviantMass (Rk k) w.fine w.coarse η ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have hcore : (∑ k, deviantMass (Rk k) w.fine w.coarse η) * η ^ 2
      ≤ ∑ k, refinementVarianceNum (Rk k) w.fine w.coarse := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ =>
      deviantMass_mul_sq_le_refinementVarianceNum w.fine w.coarse hη.le
  rw [← le_div_iff₀ hη2] at hcore
  calc ∑ k, deviantMass (Rk k) w.fine w.coarse η
      ≤ (∑ k, refinementVarianceNum (Rk k) w.fine w.coarse) / η ^ 2 := hcore
    _ ≤ δ * (s.card : ℝ) ^ 2 / η ^ 2 :=
        (div_le_div_iff_of_pos_right hη2).mpr w.sum_refinementVarianceNum_le
    _ = δ / η ^ 2 * (s.card : ℝ) ^ 2 := by ring

/-- A coarse pair is typical for a family witness when it is typical for **every** relation
— taken pointwise through the projections, not as a condition on the aggregate. -/
def FamilyStrongWitness.IsTypicalCoarsePair (w : FamilyStrongWitness Rk E δ P₀) (η θ : ℝ)
    (pd : Finset α × Finset α) : Prop :=
  ∀ k, (w.toStrongWitness k).IsTypicalCoarsePair η θ pd

open Classical in
/-- The mass carried by the coarse pairs that fail to be typical for every relation. -/
noncomputable def FamilyStrongWitness.atypicalMass (w : FamilyStrongWitness Rk E δ P₀)
    (η θ : ℝ) : ℝ :=
  ∑ pd ∈ (w.coarse.parts ×ˢ w.coarse.parts).filter
      (fun pd => ¬ w.IsTypicalCoarsePair η θ pd), ((pd.1.card : ℝ) * pd.2.card)

/-- Pointwise failure is monotone into the aggregate: if some component's deviant child mass
exceeds the threshold, the sum over components does too, every summand being nonnegative.
This is what lets a *pointwise* typicality notion be bounded by an *aggregate* Markov step,
and it is why no `K` appears. -/
theorem FamilyStrongWitness.threshold_lt_sum_of_not_typical
    (w : FamilyStrongWitness Rk E δ P₀) {η θ : ℝ} {pd : Finset α × Finset α}
    (h : ¬ w.IsTypicalCoarsePair η θ pd) :
    θ * ((pd.1.card : ℝ) * pd.2.card)
      < ∑ k, deviantChildMass (Rk k) w.fine η pd := by
  classical
  rw [FamilyStrongWitness.IsTypicalCoarsePair] at h
  push Not at h
  obtain ⟨k, hk⟩ := h
  rw [StrongWitness.IsTypicalCoarsePair, not_le] at hk
  refine lt_of_lt_of_le hk ?_
  exact Finset.single_le_sum (f := fun k => deviantChildMass (Rk k) w.fine η pd)
    (fun j _ => deviantChildMass_nonneg) (Finset.mem_univ k)

/-- **The aggregate second Markov step.** The mass of coarse pairs that fail to be
`(η, θ)`-typical **for every relation of the family** is at most `(δ/(η²θ))·|s|²` — the same
constant as the single-relation bound, with **no factor of `K`**.

Typicality is pointwise, so this controls all `K` relations simultaneously without
strengthening the hypothesis to a condition on the summed component mass. -/
theorem FamilyStrongWitness.atypicalMass_le (w : FamilyStrongWitness Rk E δ P₀) {η θ : ℝ}
    (hη : 0 < η) (hθ : 0 < θ) :
    w.atypicalMass η θ ≤ δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2 := by
  classical
  have hstep : θ * w.atypicalMass η θ
      ≤ ∑ k, deviantMass (Rk k) w.fine w.coarse η := by
    rw [FamilyStrongWitness.atypicalMass, Finset.mul_sum]
    calc ∑ pd ∈ (w.coarse.parts ×ˢ w.coarse.parts).filter
            (fun pd => ¬ w.IsTypicalCoarsePair η θ pd),
          θ * ((pd.1.card : ℝ) * pd.2.card)
        ≤ ∑ pd ∈ (w.coarse.parts ×ˢ w.coarse.parts).filter
            (fun pd => ¬ w.IsTypicalCoarsePair η θ pd),
            ∑ k, deviantChildMass (Rk k) w.fine η pd :=
          Finset.sum_le_sum fun pd hpd => by
            rw [Finset.mem_filter] at hpd
            exact (w.threshold_lt_sum_of_not_typical hpd.2).le
      _ ≤ ∑ pd ∈ w.coarse.parts ×ˢ w.coarse.parts,
            ∑ k, deviantChildMass (Rk k) w.fine η pd :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun pd _ _ => Finset.sum_nonneg fun _ _ => deviantChildMass_nonneg
      _ = ∑ k, deviantMass (Rk k) w.fine w.coarse η := Finset.sum_comm
  have h1 : θ * w.atypicalMass η θ ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
    le_trans hstep (w.sum_deviantMass_le hη)
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have hgoal : δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2
      = (δ / η ^ 2 * (s.card : ℝ) ^ 2) / θ := by
    field_simp
  rw [hgoal, le_div_iff₀ hθ]
  exact (mul_comm _ _).trans_le h1

end FamilyTypical

/-! ### Tests and adversarial examples -/

section Tests

variable {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

-- **The exact constant.** Pinned at `δ / (η² θ) · |s|²`, with no family size anywhere in
-- it. A refactor routing this through the `K` per-relation projections would produce
-- `K · δ / (η² θ)` and fail to typecheck here.
example {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]
    (w : FamilyStrongWitness Rk E δ P₀) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    w.atypicalMass η θ ≤ δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2 :=
  w.atypicalMass_le hη hθ

-- **Repeated relations.** `m` identical copies of one relation get the SAME bound as one
-- copy — the direct falsification test for an accidental union bound, which would degrade
-- it by a factor of `m`.
example (R : α → α → Prop) [DecidableRel R] (m : ℕ)
    (w : FamilyStrongWitness (fun _ : Fin m => R) E δ P₀) {η θ : ℝ}
    (hη : 0 < η) (hθ : 0 < θ) :
    w.atypicalMass η θ ≤ δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2 :=
  w.atypicalMass_le hη hθ

-- **Empty family.** With no relations every coarse pair is vacuously typical for all of
-- them.
example (Rk : Fin 0 → α → α → Prop) [∀ k, DecidableRel (Rk k)]
    (w : FamilyStrongWitness Rk E δ P₀) (η θ : ℝ) (pd : Finset α × Finset α) :
    w.IsTypicalCoarsePair η θ pd :=
  fun k => k.elim0

-- **`θ = 1`.** Typicality at `θ = 1` says the deviant children carry at most the whole
-- pair's mass; the bound still reads `δ / η² · |s|²`.
example {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]
    (w : FamilyStrongWitness Rk E δ P₀) {η : ℝ} (hη : 0 < η) :
    w.atypicalMass η 1 ≤ δ / (η ^ 2 * 1) * (s.card : ℝ) ^ 2 :=
  w.atypicalMass_le hη one_pos

-- The single-relation and family constants agree: nothing is lost passing to the family.
example (R : α → α → Prop) [DecidableRel R] (w : StrongWitness R E δ P₀) {η θ : ℝ}
    (hη : 0 < η) (hθ : 0 < θ) :
    w.atypicalMass η θ ≤ δ / (η ^ 2 * θ) * (s.card : ℝ) ^ 2 :=
  w.atypicalMass_le hη hθ

-- The Markov core needs no refinement hypothesis — that is what lets it be summed.
example (R : α → α → Prop) [DecidableRel R] (Q P : Finpartition s) {η : ℝ} (hη : 0 ≤ η) :
    deviantMass R Q P η * η ^ 2 ≤ refinementVarianceNum R Q P :=
  deviantMass_mul_sq_le_refinementVarianceNum Q P hη

end Tests

end RegularityLemmata
