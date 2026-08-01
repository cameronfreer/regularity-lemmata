/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxyNormalizedCostGate
import RegularityLemmata.Relational.BinaryProfile

/-!
# Route (b) ladder step 2: the forbidden-channel fork, stated and tested

`ARCHITECTURE.md` route (b) ladder step 2. The normalized-cost gate closed the COST side of
the `P`/`δ` hierarchy. The forbidden side is the remaining blocker, and it forked in two:

* **Branch A** — produce a witness whose coarse partition is an equipartition with a usable
  size floor, so `σ ≤ 1/2` can be read off `proxySigma_le_half_of_parts`.
* **Branch B** — redesign how nonuniform selected pairs are handled, so nonuniformity is not
  a forbidden event at all.

**This is a statement and falsification pass, not step 5.** Nothing is assembled.

## Branch A is falsified whenever one vertex has a unique profile

The witness's coarse partition must refine the vertex-profile partition (`coarse_profile`).
If some vertex of the host has a profile shared with no other vertex, its profile class is a
singleton, so any refinement has a singleton part (`exists_eq_singleton_of_unique_profile`).
An equipartition with a singleton part has ALL parts of size at most two
(`card_le_two_of_singleton_part`), hence at least `#s / 2` parts
(`card_le_two_mul_card_parts_of_singleton_part`).

The consequence is fatal for branch A, not merely awkward: `proxyFineTolerance K P` at
`P ≥ #s / 2` is at most `1 / (8 * K * #s ^ 2)`
(`proxyFineTolerance_le_of_singleton_part`). The forbidden channel would then demand a fine
partition regular at a tolerance shrinking like `#s ⁻²`, which no regularity lemma provides —
bounded complexity requires a tolerance fixed independently of the host.

A unique profile is not exotic: one vertex distinguished by its loop data suffices, and
`uniqueProfileVertex` exhibits such a model concretely. Branch A therefore cannot be repaired
by choosing a better producer; it is the combination that fails.

**Scope of the refutation.** What is refuted is the conjunction of three things: an EXACT
equipartition, refining the profile partition, with HOST-INDEPENDENT complexity. Drop any one
and the argument says nothing — an approximate size balance, a coarse partition not tied to
profiles, or an admittedly host-dependent part count are all outside it.

## Branch B survives

Charging a nonuniform selected pair its proxy pair's normalized mass — exactly the device
that made the deviation budget `P`-free — keeps the proxy count and the size floor out of the
budget, via the same coordinatewise cancellation (`massWeight_mul_mass_le_of_candidates`).

* `expected_proxyNormalizedNonuniformCost_le` : `μ = 4 * ε` — **the per-relation lemma**, for
  a single relation `R`, from the aggregate `sum_proxyPair_nonuniform_le`.
* `expected_proxyNormalizedPaletteCost_le` : `μ = 4 * K * ε` — **the relational branch-B
  gate**, which is what the forbidden condition actually is: SIMULTANEOUS palette regularity.
  The forbidden family is `paletteNonuniformFinePairs`, the union over colours, and the
  factor `K = Fintype.card (BinaryPairPalette L)` is the union-bound multiplicity, as in the
  step-2 budget. Still no proxy count and no size floor.

What changes is the CONCLUSION available to the summit. Nonuniformity would no longer be
excluded outright; it would be bounded in normalized mass, so the summit must be restated to
consume "all but a small mass of proxy pairs are uniform" instead of "every selected pair is
uniform". Whether the downstream counting survives that weakening is **not decided here** —
it is the next question, and step 5 stays closed until it is answered.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}

/-! ### Branch A: equipartitions with a singleton part are nearly discrete -/

/-- An equipartition with a singleton part has every part of size at most two. -/
theorem card_le_two_of_singleton_part (hQ : Q.IsEquipartition) {A : Finset V}
    (hA : A ∈ Q.parts) (hA1 : A.card = 1) {B : Finset V} (hB : B ∈ Q.parts) : B.card ≤ 2 := by
  by_contra hcon
  refine (Finpartition.not_isEquipartition.mpr ⟨B, hB, A, hA, ?_⟩) hQ
  omega

/-- **Branch A's size collapse.** An equipartition with a singleton part has at least
`#s / 2` parts: the singleton caps every part at two. -/
theorem card_le_two_mul_card_parts_of_singleton_part (hQ : Q.IsEquipartition) {A : Finset V}
    (hA : A ∈ Q.parts) (hA1 : A.card = 1) : s.card ≤ 2 * Q.parts.card := by
  classical
  have hsum : s.card = ∑ B ∈ Q.parts, B.card := (Q.sum_card_parts).symm
  calc s.card = ∑ B ∈ Q.parts, B.card := hsum
    _ ≤ ∑ _B ∈ Q.parts, 2 := Finset.sum_le_sum fun B hB =>
        card_le_two_of_singleton_part hQ hA hA1 hB
    _ = 2 * Q.parts.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Branch A: a unique profile forces a singleton part -/

section Profile

variable {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}

/-- A vertex whose profile is shared with no other vertex of the host has a singleton
profile class, so every partition refining the profile partition has `{v}` as a part. -/
theorem exists_eq_singleton_of_unique_profile (hQ : Q ≤ binaryProfilePartition M s) {v : V}
    (hv : v ∈ s) (huniq : ∀ b ∈ s, binaryVertexProfile M v = binaryVertexProfile M b → b = v) :
    ({v} : Finset V) ∈ Q.parts := by
  classical
  obtain ⟨A, hA, hvA⟩ := Q.exists_mem hv
  obtain ⟨C, hC, hAC⟩ := hQ hA
  -- `v`'s profile class is `{v}`, and `A` lies inside the class containing `v`.
  have hclass : C = {v} := by
    rw [binaryProfilePartition_parts, Finset.mem_image] at hC
    obtain ⟨a, ha, rfl⟩ := hC
    have hvmem : v ∈ {b ∈ s | binaryVertexProfile M a = binaryVertexProfile M b} := hAC hvA
    rw [Finset.mem_filter] at hvmem
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun b hb => ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hv, hvmem.2⟩
    · rw [Finset.mem_filter] at hb
      exact huniq b hb.1 (hvmem.2.symm.trans hb.2)
  have : A = {v} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hvA, fun b hb => ?_⟩
    have := hAC hb
    rw [hclass, Finset.mem_singleton] at this
    exact this
  rwa [← this]

/-- **Branch A, falsified.** A witness coarse partition that is an equipartition and refines
the profile partition has at least `#s / 2` parts as soon as ONE vertex has a unique profile.
The proxy count is then linear in the host, not bounded. -/
theorem card_le_two_mul_card_parts_of_unique_profile (hQ : Q.IsEquipartition)
    (hQP : Q ≤ binaryProfilePartition M s) {v : V} (hv : v ∈ s)
    (huniq : ∀ b ∈ s, binaryVertexProfile M v = binaryVertexProfile M b → b = v) :
    s.card ≤ 2 * Q.parts.card :=
  card_le_two_mul_card_parts_of_singleton_part hQ
    (exists_eq_singleton_of_unique_profile hQP hv huniq) (Finset.card_singleton v)

omit [DecidableEq V] in
/-- **The fatal consequence.** At a proxy count linear in the host, the fine tolerance the
forbidden channel would require shrinks like `#s ⁻²`. No regularity lemma delivers a
bounded-complexity partition at a host-dependent tolerance, so branch A is not repairable by
choosing a different producer. -/
theorem proxyFineTolerance_le_of_singleton_part {K P : ℕ} (hK : 0 < K) (hP : 0 < P)
    (hspos : 0 < s.card) (hs : s.card ≤ 2 * P) :
    proxyFineTolerance K P ≤ 1 / (8 * (K : ℝ) * (s.card : ℝ) ^ 2) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hs' : (s.card : ℝ) ≤ 2 * P := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hspos
  rw [proxyFineTolerance]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hsq : (s.card : ℝ) ^ 2 ≤ 4 * (P : ℝ) ^ 2 := by nlinarith [hs', hs0.le]
  linarith [mul_nonneg hK0.le (sub_nonneg.mpr hsq)]

end Profile

/-! ### Branch B: nonuniformity as a normalized-mass charge -/

section BranchB

variable (R : V → V → Prop) [DecidableRel R]

open Classical in
/-- The normalized nonuniformity cost: each proxy pair whose two selected representatives
form a nonuniform fine pair is charged that proxy pair's normalized mass. -/
noncomputable def proxyNormalizedNonuniformCost (ε : ℝ) (F : Finpartition s)
    (Q : Finpartition s) (g : ProxyIndex Q → Finset V) : ℝ :=
  ∑ e : ProxyEvent Q,
    if (g (proxyEventFst e), g (proxyEventSnd e)) ∈ nonuniformFinePairs R ε F
      then proxyPairMassWeight s (proxyEventPair e) else 0

open Classical in
/-- The aggregate nonuniform candidate mass over all proxy-pair events, bounded once by the
fine partition's diagonal-inclusive bad mass — the mass-only form of the step-2 aggregate. -/
theorem sum_proxyEvent_nonuniformMass_le {ε : ℝ} (F : Finpartition s) (q : ℕ)
    (Q : Finpartition s) :
    ∑ e : ProxyEvent Q, ∑ p ∈ nonuniformFinePairs R ε F ∩
        (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
      ≤ badMassDiagNum R ε F := by
  classical
  calc ∑ e : ProxyEvent Q, ∑ p ∈ nonuniformFinePairs R ε F ∩ _, ((p.1.card : ℝ) * p.2.card)
      ≤ ∑ e : ProxyEvent Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ e.1.1)) ×ˢ (F.parts.filter (· ⊆ e.1.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [nonuniformFinePairs]
        exact sum_candidateMass_le_fibreMass F q _ (proxyEventFst e) (proxyEventSnd e)
    _ = ∑ pd ∈ proxyPairEvents Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) :=
        Finset.sum_coe_sort (proxyPairEvents Q) (fun pd =>
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card))
    _ ≤ badMassDiagNum R ε F := sum_proxyPair_nonuniform_le R F Q

open Classical in
/-- **Branch B, surviving.** Charging nonuniformity by the proxy pair's normalized mass makes
its budget `4 * ε` — no proxy count, no size floor. The cancellation is the same
coordinatewise one that freed the deviation budget. -/
theorem expected_proxyNormalizedNonuniformCost_le {ε : ℝ} {F : Finpartition s} (hFQ : F ≤ Q)
    {q : ℕ} (hq : F.parts.card ≤ q) (hε : 0 ≤ ε)
    (hB : badMassDiagNum R ε F ≤ ε * (s.card : ℝ) ^ 2) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := Q) F q),
        (∏ j, ((g j).card : ℝ)) * proxyNormalizedNonuniformCost R ε F Q g
      ≤ 4 * ε * proxyTotalCandidateWeight F q Q := by
  classical
  set t := proxyCandidates (Q := Q) F q with ht
  set mass : ProxyEvent Q → ℝ := fun e =>
    ∑ p ∈ nonuniformFinePairs R ε F ∩ (t (proxyEventFst e) ×ˢ t (proxyEventSnd e)),
      ((p.1.card : ℝ) * p.2.card) with hmass
  have htotal : (0 : ℝ) ≤ proxyTotalCandidateWeight F q Q :=
    proxyTotalCandidateWeight_nonneg F q
  have hstep := sum_piFinset_weight_mul_eventCost_le t (fun A => (A.card : ℝ))
    (fun A => by positivity) proxyEventFst proxyEventSnd proxyEvent_fst_ne_snd
    (fun _ : ProxyEvent Q => nonuniformFinePairs R ε F)
    (fun e => proxyPairMassWeight s (proxyEventPair e))
    (fun e => 4 * mass e / (s.card : ℝ) ^ 2)
    (fun e => by
      rw [proxyPairMassWeight]
      exact massWeight_mul_mass_le_of_candidates hFQ hq _ (proxyEventFst e) (proxyEventSnd e))
  refine le_trans (le_of_eq ?_) (le_trans hstep ?_)
  · simp only [proxyNormalizedNonuniformCost, ht]
  refine mul_le_mul_of_nonneg_right ?_ htotal
  have hrw : ∑ e : ProxyEvent Q, 4 * mass e / (s.card : ℝ) ^ 2
      = 4 * (∑ e : ProxyEvent Q, mass e) / (s.card : ℝ) ^ 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hrw]
  rcases eq_or_ne ((s.card : ℝ) ^ 2) 0 with h0 | h0
  · rw [h0, div_zero]
    positivity
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [div_le_iff₀ hpos]
    have haggr := (sum_proxyEvent_nonuniformMass_le R F q Q).trans hB
    nlinarith [haggr]

end BranchB

/-! ### Branch B for the real forbidden condition: simultaneous palette regularity -/

section BranchBPalette

variable {L : FirstOrder.Language} [FiniteRelational L] (M : FiniteRelModel L V)

open Classical in
/-- The normalized SIMULTANEOUS-uniformity cost: a proxy pair is charged its normalized mass
as soon as its two selected representatives fail uniformity for SOME palette colour. -/
noncomputable def proxyNormalizedPaletteCost (ε : ℝ) (F : Finpartition s) (Q : Finpartition s)
    (g : ProxyIndex Q → Finset V) : ℝ :=
  ∑ e : ProxyEvent Q,
    if (g (proxyEventFst e), g (proxyEventSnd e)) ∈ paletteNonuniformFinePairs M ε F
      then proxyPairMassWeight s (proxyEventPair e) else 0

open Classical in
/-- The aggregate palette-nonuniform candidate mass: the union over colours is charged once
per colour, so the bound is `K` times a single colour's bad mass — the union-bound
multiplicity, not an event count. -/
theorem sum_proxyEvent_paletteNonuniformMass_le {ε B : ℝ} (F : Finpartition s) (q : ℕ)
    (Q : Finpartition s)
    (hB : ∀ c : BinaryPairPalette L, badMassDiagNum (HasBinaryPairPalette M c) ε F ≤ B) :
    ∑ e : ProxyEvent Q, ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
        (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B := by
  classical
  have hstep : ∀ e : ProxyEvent Q,
      ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
          (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
            proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
        ≤ ∑ c : BinaryPairPalette L,
            ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
              ((p.1.card : ℝ) * p.2.card) := by
    intro e
    refine sum_le_sum_of_exists_mem _
      (fun c => nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
        (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e))) _
      (fun p => by positivity) (fun p hp => ?_)
    rw [Finset.mem_inter] at hp
    obtain ⟨c, hc⟩ := exists_mem_nonuniformFinePairs hp.1
    exact ⟨c, Finset.mem_inter.mpr ⟨hc, hp.2⟩⟩
  calc ∑ e : ProxyEvent Q, ∑ p ∈ paletteNonuniformFinePairs M ε F ∩ _,
        ((p.1.card : ℝ) * p.2.card)
      ≤ ∑ e : ProxyEvent Q, ∑ c : BinaryPairPalette L,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
            (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
              proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card) := Finset.sum_le_sum fun e _ => hstep e
    _ = ∑ c : BinaryPairPalette L, ∑ e : ProxyEvent Q,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
            (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
              proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card) := Finset.sum_comm
    _ ≤ ∑ _c : BinaryPairPalette L, B := Finset.sum_le_sum fun c _ =>
        (sum_proxyEvent_nonuniformMass_le (HasBinaryPairPalette M c) F q Q).trans (hB c)
    _ = (Fintype.card (BinaryPairPalette L) : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

open Classical in
/-- **The relational branch-B gate.** For SIMULTANEOUS palette uniformity — the forbidden
condition the summit actually needs — the normalized charge has budget `4 * K * ε`. No proxy
count and no size floor; `K` is the union-bound multiplicity over colours. -/
theorem expected_proxyNormalizedPaletteCost_le {ε : ℝ} {F : Finpartition s} (hFQ : F ≤ Q)
    {q : ℕ} (hq : F.parts.card ≤ q) (hε : 0 ≤ ε)
    (hB : ∀ c : BinaryPairPalette L,
      badMassDiagNum (HasBinaryPairPalette M c) ε F ≤ ε * (s.card : ℝ) ^ 2) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := Q) F q),
        (∏ j, ((g j).card : ℝ)) * proxyNormalizedPaletteCost M ε F Q g
      ≤ 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * ε
        * proxyTotalCandidateWeight F q Q := by
  classical
  set t := proxyCandidates (Q := Q) F q with ht
  set mass : ProxyEvent Q → ℝ := fun e =>
    ∑ p ∈ paletteNonuniformFinePairs M ε F ∩ (t (proxyEventFst e) ×ˢ t (proxyEventSnd e)),
      ((p.1.card : ℝ) * p.2.card) with hmass
  have htotal : (0 : ℝ) ≤ proxyTotalCandidateWeight F q Q :=
    proxyTotalCandidateWeight_nonneg F q
  have hstep := sum_piFinset_weight_mul_eventCost_le t (fun A => (A.card : ℝ))
    (fun A => by positivity) proxyEventFst proxyEventSnd proxyEvent_fst_ne_snd
    (fun _ : ProxyEvent Q => paletteNonuniformFinePairs M ε F)
    (fun e => proxyPairMassWeight s (proxyEventPair e))
    (fun e => 4 * mass e / (s.card : ℝ) ^ 2)
    (fun e => by
      rw [proxyPairMassWeight]
      exact massWeight_mul_mass_le_of_candidates hFQ hq _ (proxyEventFst e) (proxyEventSnd e))
  refine le_trans (le_of_eq ?_) (le_trans hstep ?_)
  · simp only [proxyNormalizedPaletteCost, ht]
  refine mul_le_mul_of_nonneg_right ?_ htotal
  have hrw : ∑ e : ProxyEvent Q, 4 * mass e / (s.card : ℝ) ^ 2
      = 4 * (∑ e : ProxyEvent Q, mass e) / (s.card : ℝ) ^ 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hrw]
  rcases eq_or_ne ((s.card : ℝ) ^ 2) 0 with h0 | h0
  · rw [h0, div_zero]
    positivity
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [div_le_iff₀ hpos]
    have haggr := sum_proxyEvent_paletteNonuniformMass_le M F q Q hB
    nlinarith [haggr]

end BranchBPalette

/-! ### Tests -/

section Tests

-- Branch A's collapse at a concrete shape: a singleton part caps every part at two.
example (hQ : Q.IsEquipartition) {A : Finset V} (hA : A ∈ Q.parts) (hA1 : A.card = 1)
    {B : Finset V} (hB : B ∈ Q.parts) : B.card ≤ 2 :=
  card_le_two_of_singleton_part hQ hA hA1 hB

-- …and the required tolerance then scales like the inverse square of the host size, which is
-- what makes branch A unrepairable rather than merely inconvenient.
example {K P : ℕ} (hK : 0 < K) (hP : 0 < P) (hspos : 0 < s.card) (hs : s.card ≤ 2 * P) :
    proxyFineTolerance K P ≤ 1 / (8 * (K : ℝ) * (s.card : ℝ) ^ 2) :=
  proxyFineTolerance_le_of_singleton_part hK hP hspos hs

-- The hypothesis is a single vertex with a unique profile — nothing exotic.
example {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
    (hQ : Q.IsEquipartition) (hQP : Q ≤ binaryProfilePartition M s) {v : V} (hv : v ∈ s)
    (huniq : ∀ b ∈ s, binaryVertexProfile M v = binaryVertexProfile M b → b = v) :
    s.card ≤ 2 * Q.parts.card :=
  card_le_two_mul_card_parts_of_unique_profile hQ hQP hv huniq

-- Branch B's palette charge — the one the summit actually needs — is `4 * K * ε`.
example {L : FirstOrder.Language} [FiniteRelational L] (M : FiniteRelModel L V) {ε : ℝ}
    {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ} (hq : F.parts.card ≤ q) (hε : 0 ≤ ε)
    (hB : ∀ c : BinaryPairPalette L,
      badMassDiagNum (HasBinaryPairPalette M c) ε F ≤ ε * (s.card : ℝ) ^ 2) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := Q) F q),
        (∏ j, ((g j).card : ℝ)) * proxyNormalizedPaletteCost M ε F Q g
      ≤ 4 * (Fintype.card (BinaryPairPalette L) : ℝ) * ε * proxyTotalCandidateWeight F q Q :=
  expected_proxyNormalizedPaletteCost_le M hFQ hq hε hB

-- Branch B's charge is nonnegative, which is `hcost`.
example (R : V → V → Prop) [DecidableRel R] (ε : ℝ) (F : Finpartition s)
    (g : ProxyIndex Q → Finset V) : 0 ≤ proxyNormalizedNonuniformCost R ε F Q g := by
  classical
  refine Finset.sum_nonneg fun e _ => ?_
  split
  · exact proxyPairMassWeight_nonneg s _
  · exact le_refl 0

-- Branch B's budget mentions neither a proxy count nor a size floor: `4 * ε` alone.
example (R : V → V → Prop) [DecidableRel R] {ε : ℝ} {F : Finpartition s} (hFQ : F ≤ Q)
    {q : ℕ} (hq : F.parts.card ≤ q) (hε : 0 ≤ ε)
    (hB : badMassDiagNum R ε F ≤ ε * (s.card : ℝ) ^ 2) :
    ∑ g ∈ Fintype.piFinset (proxyCandidates (Q := Q) F q),
        (∏ j, ((g j).card : ℝ)) * proxyNormalizedNonuniformCost R ε F Q g
      ≤ 4 * ε * proxyTotalCandidateWeight F q Q :=
  expected_proxyNormalizedNonuniformCost_le R hFQ hq hε hB

/-! #### The unique-profile hypothesis, exhibited -/

section UniqueProfileExample

open FiniteRelModel

/-- A one-binary-symbol model from a Boolean relation. -/
private def binModel {W : Type*} (p : W → W → Bool) :
    FiniteRelModel (singleRelLang 2) W :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

/-- Three vertices, a loop at `0` and nothing else: `0`'s profile is shared with no other
vertex, while `1` and `2` share theirs. -/
private abbrev loopMarked : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  binModel fun x y => decide (x = 0 ∧ y = 0)

-- The loop data really does distinguish `0`, and really does NOT distinguish `1` from `2`,
-- so the hypothesis is about one vertex rather than about a degenerate model.
example : binaryVertexProfile loopMarked 0 ≠ binaryVertexProfile loopMarked 1 := by decide

example : binaryVertexProfile loopMarked 1 = binaryVertexProfile loopMarked 2 := by decide

/-- **The unique-profile hypothesis, satisfied concretely.** Vertex `0` is distinguished by
its loop data alone. -/
theorem uniqueProfileVertex :
    ∀ b ∈ (Finset.univ : Finset (Fin 3)),
      binaryVertexProfile loopMarked 0 = binaryVertexProfile loopMarked b → b = 0 := by
  decide

-- …and branch A's collapse instantiated at it: any exact equipartition of this host that
-- refines the profile partition has at least half as many parts as the host has vertices.
example (Q : Finpartition (Finset.univ : Finset (Fin 3))) (hQ : Q.IsEquipartition)
    (hQP : Q ≤ binaryProfilePartition loopMarked Finset.univ) :
    (Finset.univ : Finset (Fin 3)).card ≤ 2 * Q.parts.card :=
  card_le_two_mul_card_parts_of_unique_profile hQ hQP (Finset.mem_univ 0) uniqueProfileVertex

end UniqueProfileExample

end Tests

end RegularityLemmata
