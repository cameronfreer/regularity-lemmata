/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.EquitableFamilyRegularity

/-!
# Route (b) ladder step 2: the multiple-of-three seed

`ARCHITECTURE.md` route (b) ladder step 2 (2026-07-28 freeze). Grouping the cells of a
regular equipartition into owners of three needs `3 ∣ #Q.parts`, which the family
regularity summit does not supply: its reachable part counts are the iterates of
`familyStepBound` from the ε-dependent initial floor, and that floor is not divisible by
three in general.

This file supplies the acyclic fix and carries it through the iteration.

* `familyTripleSeed C ε l` — the initial floor rounded UP to a multiple of three. It is
  still a function of `(C, ε, l)` only, so no acyclicity is disturbed, and it costs at most
  two extra parts.
* `three_dvd_familyRegularityBoundAux` — divisibility survives the recursion, because
  `familyStepBound n = n · familyChunksPerPart n`.
* `familyRegularity_iterate_dvd` and `exists_familyRegular_equipartition_triple` — the
  iteration and the summit with `3 ∣ #Q.parts` carried as an invariant. The part count is
  divisible by three at every stage, since each step multiplies it by
  `familyChunksPerPart`.

**No grouping is constructed here.** The owner construction, its cover and disjointness,
the union cardinality bounds, and the selection rebuild are the next unit; rounding,
cleaning, and `Recolor.lean` stay closed.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α} {ε : ℝ}
variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]

/-! ### The seed -/

/-- **The multiple-of-three seed**: the ε-dependent initial floor rounded up to a multiple
of three. Still a function of `(C, ε, l)` only. -/
noncomputable def familyTripleSeed (C ε : ℝ) (l : ℕ) : ℕ :=
  3 * ((familyInitialBound C ε l + 2) / 3)

theorem three_dvd_familyTripleSeed (C ε : ℝ) (l : ℕ) : 3 ∣ familyTripleSeed C ε l :=
  ⟨_, rfl⟩

theorem le_familyTripleSeed (C ε : ℝ) (l : ℕ) :
    familyInitialBound C ε l ≤ familyTripleSeed C ε l := by
  rw [familyTripleSeed]
  omega

/-- The seed costs at most two extra parts over the floor. -/
theorem familyTripleSeed_le (C ε : ℝ) (l : ℕ) :
    familyTripleSeed C ε l ≤ familyInitialBound C ε l + 2 := by
  rw [familyTripleSeed]
  omega

theorem two_le_familyTripleSeed (C ε : ℝ) (l : ℕ) : 2 ≤ familyTripleSeed C ε l :=
  le_trans (two_le_familyInitialBound C ε l) (le_familyTripleSeed C ε l)

theorem le_familyTripleSeed_of_le (C ε : ℝ) (l : ℕ) : l ≤ familyTripleSeed C ε l :=
  le_trans (le_familyInitialBound C ε l) (le_familyTripleSeed C ε l)

/-! ### Divisibility through the recursion -/

/-- Divisibility by three survives the iterate, because each step multiplies the part
count by `familyChunksPerPart`. -/
theorem three_dvd_familyRegularityBoundAux {m : ℕ} (h : 3 ∣ m) (t : ℕ) :
    3 ∣ familyRegularityBoundAux t m := by
  induction t generalizing m with
  | zero => simpa [familyRegularityBoundAux] using h
  | succ t IH =>
    rw [familyRegularityBoundAux]
    exact IH (three_dvd_familyStepBound h)

/-- The final bound from the seed, which is what a grouped construction consumes. -/
noncomputable def familyRegularityBoundTriple (K : ℕ) (ε : ℝ) (l : ℕ) : ℕ :=
  familyRegularityBoundAux (familyFuel K ε) (familyTripleSeed familyChunkThreshold ε l)

theorem three_dvd_familyRegularityBoundTriple (K : ℕ) (ε : ℝ) (l : ℕ) :
    3 ∣ familyRegularityBoundTriple K ε l :=
  three_dvd_familyRegularityBoundAux (three_dvd_familyTripleSeed _ _ _) _

theorem le_familyRegularityBoundTriple (K : ℕ) (ε : ℝ) (l : ℕ) :
    familyTripleSeed familyChunkThreshold ε l ≤ familyRegularityBoundTriple K ε l :=
  le_familyRegularityBoundAux _ _

/-! ### The iteration, carrying divisibility -/

/-- **The iteration with the divisibility invariant.** The part count stays divisible by
three at every stage, because each step multiplies it by `familyChunksPerPart`. Otherwise
this is `familyRegularity_iterate` verbatim. -/
theorem familyRegularity_iterate_dvd (hε : 0 < ε) (hε1 : ε ≤ 1) {l : ℕ} :
    ∀ (t : ℕ) (P : Finpartition s), P.IsEquipartition →
      familyInitialBound familyChunkThreshold ε l ≤ P.parts.card →
      3 ∣ P.parts.card →
      familyRegularityBoundAux t P.parts.card ≤ s.card →
      (K : ℝ) - (t : ℝ) * (familyRetainedFraction * ε ^ 5) ≤ familyEnergy Rk P →
      ∃ Q : Finpartition s, Q ≤ P ∧ Q.IsEquipartition ∧ IsFamilyRegular Rk ε Q ∧
        familyInitialBound familyChunkThreshold ε l ≤ Q.parts.card ∧
        3 ∣ Q.parts.card ∧
        Q.parts.card ≤ familyRegularityBoundAux t P.parts.card := by
  have hgain : (0 : ℝ) < familyRetainedFraction * ε ^ 5 := by
    rw [familyRetainedFraction]; positivity
  intro t
  induction t with
  | zero =>
    intro P hP hfloor hdvd _hs hbudget
    refine ⟨P, le_rfl, hP, ?_, hfloor, hdvd, le_familyRegularityBoundAux 0 _⟩
    by_contra hreg
    rw [IsFamilyRegular] at hreg
    push Not at hreg
    obtain ⟨k, hk⟩ := hreg
    have hgainQ := familyEnergy_equitableIncrement_increment (Rk := Rk) hP hε hε1 hfloor k
      (lt_of_not_ge hk)
    have hceil : familyEnergy Rk (equitableIncrement (Rk k) ε hP) ≤ (K : ℝ) :=
      familyEnergy_le_card
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hbudget
    linarith
  | succ t IH =>
    intro P hP hfloor hdvd hs hbudget
    by_cases hreg : IsFamilyRegular Rk ε P
    · exact ⟨P, le_rfl, hP, hreg, hfloor, hdvd, le_familyRegularityBoundAux _ _⟩
    · rw [familyRegularityBoundAux] at hs
      have hstep : familyStepBound P.parts.card ≤ s.card :=
        le_trans (le_familyRegularityBoundAux t (familyStepBound P.parts.card)) hs
      obtain ⟨P', hP'P, hP'eq, hP'card, hP'gain⟩ :=
        exists_familyEnergy_increment_equitable Rk hP hε hε1 hfloor hstep hreg
      have hfloor' : familyInitialBound familyChunkThreshold ε l ≤ P'.parts.card := by
        rw [hP'card]
        exact le_trans hfloor (le_familyStepBound _)
      have hdvd' : 3 ∣ P'.parts.card := by
        rw [hP'card]
        exact three_dvd_familyStepBound hdvd
      have hs' : familyRegularityBoundAux t P'.parts.card ≤ s.card := by
        rw [hP'card]; exact hs
      have hbudget' : (K : ℝ) - (t : ℝ) * (familyRetainedFraction * ε ^ 5)
          ≤ familyEnergy Rk P' := by
        push_cast at hbudget
        linarith
      obtain ⟨Q, hQP', hQeq, hQreg, hQfloor, hQdvd, hQcard⟩ :=
        IH P' hP'eq hfloor' hdvd' hs' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQeq, hQreg, hQfloor, hQdvd, ?_⟩
      rw [familyRegularityBoundAux, ← hP'card]
      exact hQcard

/-! ### The summit, seeded at a multiple of three -/

/-- **Family regularity with a part count divisible by three.** Seeding the iteration at
`familyTripleSeed` discharges the divisibility prerequisite that grouping into owners of
three needs, at a cost of at most two extra parts and with no acyclicity disturbed: the
seed is still a function of `(ε, l)` alone. -/
theorem exists_familyRegular_equipartition_triple (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (hε : 0 < ε) (hε1 : ε ≤ 1) (l : ℕ)
    (hs : familyRegularityBoundTriple K ε l ≤ s.card) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ IsFamilyRegular Rk ε Q ∧
      l ≤ Q.parts.card ∧ 3 ∣ Q.parts.card ∧
      Q.parts.card ≤ familyRegularityBoundTriple K ε l := by
  set n := familyTripleSeed familyChunkThreshold ε l with hn
  have hn0 : n ≠ 0 := by
    have := two_le_familyTripleSeed familyChunkThreshold ε l
    omega
  have hns : n ≤ s.card :=
    le_trans (le_familyRegularityBoundTriple K ε l) hs
  obtain ⟨P, hPeq, hPcard⟩ := Finpartition.exists_equipartition_card_eq s hn0 hns
  have hfloor : familyInitialBound familyChunkThreshold ε l ≤ P.parts.card := by
    rw [hPcard, hn]
    exact le_familyTripleSeed _ _ _
  have hdvd : 3 ∣ P.parts.card := by
    rw [hPcard, hn]
    exact three_dvd_familyTripleSeed _ _ _
  have hs' : familyRegularityBoundAux (familyFuel K ε) P.parts.card ≤ s.card := by
    rw [hPcard]
    exact hs
  have hbudget : (K : ℝ) - (familyFuel K ε : ℝ) * (familyRetainedFraction * ε ^ 5)
      ≤ familyEnergy Rk P := by
    have h1 := card_le_familyFuel_mul (ε := ε) hε K
    have h2 : (0 : ℝ) ≤ familyEnergy Rk P := familyEnergy_nonneg
    linarith
  obtain ⟨Q, -, hQeq, hQreg, hQfloor, hQdvd, hQcard⟩ :=
    familyRegularity_iterate_dvd hε hε1 (l := l) (familyFuel K ε) P hPeq hfloor hdvd hs'
      hbudget
  refine ⟨Q, hQeq, hQreg, le_trans (le_familyInitialBound _ _ _) hQfloor, hQdvd, ?_⟩
  rw [hPcard] at hQcard
  rw [familyRegularityBoundTriple, ← hn]
  exact hQcard

/-! ### Tests -/

section Tests

-- The seed is a multiple of three, at most two above the floor, and never below it.
example (ε : ℝ) (l : ℕ) : 3 ∣ familyTripleSeed 100 ε l := three_dvd_familyTripleSeed _ _ _

example (ε : ℝ) (l : ℕ) :
    familyInitialBound 100 ε l ≤ familyTripleSeed 100 ε l
      ∧ familyTripleSeed 100 ε l ≤ familyInitialBound 100 ε l + 2 :=
  ⟨le_familyTripleSeed _ _ _, familyTripleSeed_le _ _ _⟩

-- At the sample parameters the floor `3200` is not divisible by three, and the seed
-- corrects it to `3201` — one extra part, not a change of scale.
example : familyInitialBound familyChunkThreshold (1 / 2 : ℝ) 2 = 3200 := by
  rw [familyInitialBound, familyChunkThreshold]
  norm_num

example : familyTripleSeed familyChunkThreshold (1 / 2 : ℝ) 2 = 3201 := by
  rw [familyTripleSeed, familyInitialBound, familyChunkThreshold]
  norm_num

-- Divisibility survives the whole recursion, not just one step.
example (K : ℕ) (ε : ℝ) (l : ℕ) : 3 ∣ familyRegularityBoundTriple K ε l :=
  three_dvd_familyRegularityBoundTriple K ε l

-- The seed still depends only on `(ε, l)` — the acyclicity the schedule requires.
example (ε : ℝ) (l : ℕ) :
    familyTripleSeed familyChunkThreshold ε l
      = 3 * ((familyInitialBound familyChunkThreshold ε l + 2) / 3) := rfl

end Tests

end RegularityLemmata
