/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxySelectionConstants
import RegularityLemmata.Relational.BinaryDiagStrong
import RegularityLemmata.Graph.TripleSeed

/-!
# Route (b) ladder step 2: the `P`/`δ` hierarchy bridge

`ARCHITECTURE.md` route (b) ladder step 2. **Not step 5.** Step 4 left the proxy budgets
local to a realized proxy count `P`, with gate G-H1 recording that no deviation parameter
serves uniformly over all `P`. This file asks the one question that decides how step 5 may be
assembled: **can a witness be produced whose coarse partition satisfies both an a priori
count bound and the size hypotheses the local budget lemmas consume?**

Nothing here assembles weighted choice, and nothing here is the summit.

## What is built

* `proxyCountBound K ρ l = familyRegularityBoundTriple K ρ l` — the a priori bound, in the
  INPUTS `K`, `ρ`, `l` only, from the family-regularity summit.
* `proxyFineSchedule K` — the fine tolerance as an `ErrorSchedule`.
* `sigma_le_half_of_countBound`, `mu_le_of_countBound` — the antitonicity handoff:
  **assuming** `w.coarse.parts.card ≤ B`, tolerances chosen at `B` are admissible at the
  realized count. These are conditional statements; the hypothesis is exactly what the rest
  of the file investigates.

## What the investigation found

**Positive: fine-tolerance scheduling.** `ErrorSchedule` is a FUNCTION evaluated at the
realized coarse count (`fine_diagRegular : IsBinaryPaletteDiagRegular M (E coarse.parts.card)
fine`). Instantiating it at `proxyFineSchedule K` therefore delivers fine regularity at the
fine tolerance for the witness's own coarse count, with **no a priori bound needed** — the
schedule is fixed in advance, the count is realized afterwards, and the two meet by
evaluation (`fine_diagRegular_proxyFineSchedule`, whose tolerance is at `max P 1`;
`fine_diagRegular_proxyFineSchedule_of_pos` states it at `P` itself once the coarse partition
is nonempty). So the `P`-dependence of the fine TOLERANCE is not a hierarchy problem.

This is scheduling only, and does not discharge the forbidden budget. That budget still needs
the count bound and the `m`/`m + 1` size hypotheses, which are exactly what G-H2a says are
unavailable for `w.coarse`.

**Negative, for the deviation parameter — hard stop.** `δ` is a scalar, not a schedule, and
two obstructions stand between it and an a priori bound:

* **G-H2a** (`exists_le_and_card_parts_lt`). `w.coarse ≤ P₀` is the only relation the witness
  gives to its starting partition, and refinement does not bound part counts: a coarser
  partition can have strictly fewer parts than one refining it. So seeding the witness at the
  family-regular equipartition `Q` does NOT give `w.coarse.parts.card ≤ Q.parts.card`, nor
  does it transport `Q`'s equitability — which is separately what the proxy-size floor `m`
  and the ceiling `m + 1` are read from. The bound proved of `Q` is a bound on `Q`.
* **G-H2b** (`witnessCoarseBound_anti_in_deviation`). The producer's own coarse bound is
  `(monoStepBound E)^[⌈1 / δ⌉₊] n₀`, whose fuel grows as `δ` shrinks; the iterate is monotone
  in the fuel, so the bound is antitone in `δ`. Choosing `δ` from a target `B` and then
  demanding the produced coarse count be at most `B` moves both sides the same way: a smaller
  `δ` only enlarges the sole available bound. The order "fix `B`, derive `δ`, produce a
  witness under `B`" is therefore not supported.

**Conclusion.** The decisive producer theorem — one witness with both
`w.coarse.parts.card ≤ B` and the size/equipartition facts the local budgets consume — is not
available from the current construction, and G-H2b says it will not come from shrinking `δ`.
Step 5 stays closed. The live alternative is the one G-H1 named second: a deviation
requirement that is `P`-free, which means changing what the cost channel charges rather than
bounding `P`. That is a design question, not packaging, and is not decided here.

**A `P`-free cost would close only half of this.** It removes the `P`-dependence from the
COST side. The forbidden side is untouched: `hbad` still needs a count bound and the
equitability facts G-H2a denies. So Step 5 remains blocked afterwards, on either producing an
equitable large-cell witness coarse partition or redesigning how nonuniform selected pairs
are handled.
-/

namespace RegularityLemmata

open FirstOrder

/-! ### The a priori count bound and the fine schedule -/

/-- **The a priori proxy-count bound**: the family-regularity summit's part-count bound,
a function of the inputs `K`, `ρ`, `l` alone. -/
noncomputable def proxyCountBound (K : ℕ) (ρ : ℝ) (l : ℕ) : ℕ :=
  familyRegularityBoundTriple K ρ l

/-- **The fine tolerance as a schedule.** `ErrorSchedule` is a function of the realized
coarse count, so the `P`-dependence of `proxyFineTolerance` costs nothing: the schedule is
fixed in advance and evaluated afterwards. -/
noncomputable def proxyFineSchedule (K : ℕ) (hK : 0 < K) : ErrorSchedule where
  toFun P := proxyFineTolerance K (max P 1)
  pos P := proxyFineTolerance_pos hK (lt_of_lt_of_le Nat.one_pos (le_max_right P 1))

@[simp] theorem proxyFineSchedule_apply {K : ℕ} (hK : 0 < K) (P : ℕ) :
    proxyFineSchedule K hK P = proxyFineTolerance K (max P 1) := rfl

/-! ### The antitonicity handoff, conditional on a count bound -/

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}

/-- **Handoff for the forbidden channel.** A tolerance chosen at the a priori bound `B` is
admissible at any realized count below `B`. Conditional on `hPB`, which is the hypothesis
this file investigates. -/
theorem sigma_le_half_of_countBound {K B m : ℕ} {B' ε : ℝ} (hK : 1 ≤ K)
    (hP : 1 ≤ Q.parts.card) (hPB : Q.parts.card ≤ B) (hm : 1 ≤ m)
    (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) (hε0 : 0 ≤ ε)
    (hεB : ε ≤ proxyFineTolerance K B) (hB : B' ≤ ε * (s.card : ℝ) ^ 2) :
    (K : ℝ) * B' / ((m : ℝ) / 2) ^ 2 ≤ 1 / 2 :=
  proxySigma_le_half_of_parts hK hP hm hM hε0
    (hεB.trans (proxyFineTolerance_anti (Nat.lt_of_lt_of_le Nat.zero_lt_one hK) hP hPB)) hB

/-- **Handoff for the cost channel.** Likewise for the deviation parameter — and likewise
conditional on `hPB`. -/
theorem mu_le_of_countBound {K B m : ℕ} {δ η τ : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ Q.parts.card)
    (hPB : Q.parts.card ≤ B) (hm : 1 ≤ m) (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) (hη : 0 < η)
    (hδ0 : 0 ≤ δ) (hτ : 0 ≤ τ) (hδB : δ ≤ proxyDeviationTolerance K B η τ) :
    (K : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) / ((m : ℝ) / 2) ^ 2 ≤ τ :=
  proxyMu_le_of_parts hK hP hm hM hη hδ0
    (hδB.trans (proxyDeviationTolerance_anti (Nat.lt_of_lt_of_le Nat.zero_lt_one hK) hP hPB hτ))

/-! ### The positive finding: the fine tolerance needs no a priori bound -/

variable {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V} {δ : ℝ}
  {P₀ : Finpartition s}

/-- **The schedule meets the realized count by evaluation.** A witness built against
`proxyFineSchedule K` has its fine partition diagonal-inclusively palette-regular at the fine
tolerance for its own realized coarse count — literally at `max P 1`, the schedule's
`ℕ`-clamped argument, since `ErrorSchedule` demands positivity at every input including `0`.
No bound on that count is used. See `fine_diagRegular_proxyFineSchedule_of_pos` for the
unclamped form. -/
theorem fine_diagRegular_proxyFineSchedule {K : ℕ} (hK : 0 < K)
    (w : BinaryPaletteStrongDiagWitness M (proxyFineSchedule K hK) δ P₀) :
    IsBinaryPaletteDiagRegular M
      (proxyFineTolerance K (max w.coarse.parts.card 1)) w.fine :=
  w.fine_diagRegular

/-- The unclamped form: once the coarse partition has at least one part — which it does
whenever the host is nonempty — the tolerance is `proxyFineTolerance K w.coarse.parts.card`
on the nose. -/
theorem fine_diagRegular_proxyFineSchedule_of_pos {K : ℕ} (hK : 0 < K)
    (w : BinaryPaletteStrongDiagWitness M (proxyFineSchedule K hK) δ P₀)
    (hpos : 0 < w.coarse.parts.card) :
    IsBinaryPaletteDiagRegular M (proxyFineTolerance K w.coarse.parts.card) w.fine := by
  have h : max w.coarse.parts.card 1 = w.coarse.parts.card := max_eq_left hpos
  have := w.fine_diagRegular
  rwa [proxyFineSchedule_apply, h] at this

/-! ### Gate G-H2a — refinement does not bound part counts -/

/-- **Gate G-H2a.** `w.coarse ≤ P₀` is all the witness relates to its seed, and a partition
refining another can have strictly more parts. Seeding at the family-regular equipartition
therefore transports neither its count bound nor its equitability to `w.coarse`; the size
floor `m` and ceiling `m + 1` the local budgets read off an equipartition are not available
for `w.coarse` on these grounds. -/
theorem exists_le_and_card_parts_lt :
    ∃ (t : Finset (Fin 2)) (P₀ C : Finpartition t),
      C ≤ P₀ ∧ P₀.parts.card < C.parts.card := by
  classical
  refine ⟨{0, 1}, Finpartition.indiscrete (by decide), ⊥, bot_le, ?_⟩
  rw [Finpartition.indiscrete_parts, Finpartition.card_bot]
  simp

/-! ### Gate G-H2b — the producer's coarse bound grows as the deviation shrinks -/

/-- **Gate G-H2b.** The only coarse-count bound the witness producer offers is
`(monoStepBound E)^[⌈1 / δ⌉₊] n₀`, and it is ANTITONE in `δ`: a smaller deviation parameter
means more fuel, hence a larger bound. So the order "fix a target `B`, derive `δ` from `B`,
then produce a witness whose coarse count is at most `B`" tightens both sides at once and is
not supported by this construction. -/
theorem witnessCoarseBound_anti_in_deviation (E : ErrorSchedule) {δ δ' : ℝ} (hδ : 0 < δ)
    (hδδ : δ ≤ δ') (n₀ : ℕ) :
    (monoStepBound E)^[⌈1 / δ'⌉₊] n₀ ≤ (monoStepBound E)^[⌈1 / δ⌉₊] n₀ := by
  refine monoStepBound_iterate_le_iterate E (Nat.ceil_le_ceil ?_) n₀
  exact one_div_le_one_div_of_le hδ hδδ

/-! ### Tests -/

section Tests

-- The a priori bound is in the inputs only: no partition appears in its statement.
example (K : ℕ) (ρ : ℝ) (l : ℕ) : proxyCountBound K ρ l = familyRegularityBoundTriple K ρ l :=
  rfl

-- The schedule is fixed before any partition exists, and is positive everywhere, which is
-- what `ErrorSchedule` demands.
example {K : ℕ} (hK : 0 < K) (P : ℕ) : 0 < proxyFineSchedule K hK P :=
  (proxyFineSchedule K hK).pos P

-- The scheduled tolerance is the clamped one in general, and the unclamped one exactly
-- when the coarse partition is nonempty.
example {K : ℕ} (hK : 0 < K)
    (w : BinaryPaletteStrongDiagWitness M (proxyFineSchedule K hK) δ P₀)
    (hpos : 0 < w.coarse.parts.card) :
    IsBinaryPaletteDiagRegular M (proxyFineTolerance K w.coarse.parts.card) w.fine :=
  fine_diagRegular_proxyFineSchedule_of_pos hK w hpos

-- The clamp is not vacuous: at a zero count the schedule reads its value at `1`.
example {K : ℕ} (hK : 0 < K) :
    proxyFineSchedule K hK 0 = proxyFineTolerance K 1 := by simp

-- G-H2b at a concrete pair: halving the deviation parameter cannot shrink the bound.
example (E : ErrorSchedule) (n₀ : ℕ) :
    (monoStepBound E)^[⌈1 / (1 : ℝ)⌉₊] n₀ ≤ (monoStepBound E)^[⌈1 / (1 / 2 : ℝ)⌉₊] n₀ :=
  witnessCoarseBound_anti_in_deviation E (by norm_num) (by norm_num) n₀

-- The handoffs really are conditional: `hPB` is a hypothesis, not a consequence. G-H2a is
-- the reason it cannot be read off `w.coarse ≤ P₀`.
example : ∃ (t : Finset (Fin 2)) (P₀ C : Finpartition t),
    C ≤ P₀ ∧ P₀.parts.card < C.parts.card := exists_le_and_card_parts_lt

end Tests

end RegularityLemmata
