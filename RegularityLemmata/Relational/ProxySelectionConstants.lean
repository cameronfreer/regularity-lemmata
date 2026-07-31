/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxyCostBudget
import RegularityLemmata.Graph.BadMassDiag

/-!
# Route (b) ladder step 2: the candidate-weight and proxy-size constants

`ARCHITECTURE.md` route (b) ladder step 2, final unit, **step 4 of five**: the value of the
weight floor `w₀`, the discharge of `σ < 1`, and the tolerance the cost budget needs. The
summit is step 5.

## The order: derive, then choose

* `proxyWeightFloor` — the half-mass theorem turns a proxy-SIZE floor into a candidate-WEIGHT
  floor: `w₀ = m / 2` whenever every proxy has at least `m` vertices.
* `sq_card_le_of_proxy_size` — the geometric normalization. For an equipartition into `P`
  proxies of size `m` or `m + 1` with `1 ≤ m`, the host satisfies `#s ≤ 2 * P * m`, hence
  `#s ^ 2 ≤ 4 * P ^ 2 * m ^ 2`.
* Only then are the constants chosen: `proxyFineTolerance K P = 1 / (32 * K * P ^ 2)` and
  `proxyDeviationTolerance K P η τ = η ^ 2 * τ / (16 * K * P ^ 2)`.
* `proxySigma_le_half`, `proxyMu_le` — the two budgets at those constants, and
  `proxyCost_le_two_mul` — the conditioned conclusion `μ / (1 - σ) ≤ 2 * τ`.

## Where the `P ²` comes from, and where it does not

Replacing `w₀` by the proxy-size floor divides `#s ^ 2` by `m ^ 2`, and
`#s ^ 2 / m ^ 2 ≤ 4 * P ^ 2`. **This is geometric normalization, not event counting**: it is
the ratio of the host size to a single proxy's size, and it would be present even if the
selection charged nothing per event. The step-2 and step-3 budgets remain free of any
event-cardinality envelope; what enters here is the number of proxies as a NORMALIZER.

The numerals can coincide without the sources coinciding: with `n` owners the grouping gives
`P = 3 * n` proxies, so `P ^ 2 = 9 * n ^ 2` — the same numeral as the discarded proxy-pair
envelope, from an unrelated quantity (`card_ordered_pairs_grouped_le` counted pairs; this
counts `#s / m`). `proxySq_eq_nine_mul_sq` records the coincidence so it is never read as a
reappearance.

## The tolerance is not circular

`proxyFineTolerance K P` depends on the language's palette count `K` and on `P`, the number
of PROXIES — which is an input to the fine step, fixed before the fine partition is produced.
It does not depend on the realized fine complexity, and no constant here does. That hard stop
is unchanged.

## Locality, and the open hierarchy question

Every inequality here is local to a REALIZED proxy count. `proxySigma_le_half_of_parts` and
`proxyMu_le_of_parts` state them at `P = #Q.parts` so this is syntactic, not a convention.

The tolerances are chosen for that `P`. Gate **G-H1**
(`exists_proxyCount_gt_globalDeviation`) records what that costs: since
`proxyDeviationTolerance K P η τ` shrinks like `P ⁻²`, no positive `δ` meets the requirement
UNIFORMLY over all positive proxy counts. The gate quantifies over arbitrary positive
naturals, not over counts realized by a partition or by the pipeline, so it neither exhibits
a produced `P` that violates a given `δ` nor rules out choosing `δ` from an a priori bound on
`P`. What it shows is that Step 5 still lacks one of two things: an a priori bound on `P` (or
an order of choice fixing `P` first), or a `P`-free deviation requirement.

## Step 5, not done here

The summit. `ARCHITECTURE.md` waits for the completed theorem and its actual constants.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}

/-! ### From a proxy-size floor to a candidate-weight floor -/

/-- **The weight floor.** The half-mass theorem converts a floor on proxy SIZES into a floor
on candidate WEIGHTS: `w₀ = m / 2`. -/
theorem proxyWeightFloor {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ} (hq : F.parts.card ≤ q)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, m ≤ C.card) (C : ProxyIndex Q) :
    (m : ℝ) / 2 ≤ proxyCandidateWeight (Q := Q) F q C := by
  refine le_trans ?_ (half_card_le_proxyCandidateWeight hFQ hq C)
  have : (m : ℝ) ≤ (C.1.card : ℝ) := by exact_mod_cast hm C.1 C.2
  linarith

/-! ### The geometric normalization -/

/-- **Host size against a single proxy's size.** An equipartition into `P` proxies of size
`m` or `m + 1` with `1 ≤ m` has host size at most `2 * P * m`. -/
theorem card_le_two_mul_parts_mul {m : ℕ} (hm : 1 ≤ m)
    (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) :
    (s.card : ℝ) ≤ 2 * (Q.parts.card : ℝ) * m := by
  classical
  have hsum : (s.card : ℝ) = ∑ C ∈ Q.parts, (C.card : ℝ) := (sum_card_parts_cast Q).symm
  have hle : ∑ C ∈ Q.parts, (C.card : ℝ) ≤ ∑ _C ∈ Q.parts, (2 * m : ℝ) := by
    refine Finset.sum_le_sum fun C hC => ?_
    have h1 : (C.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hM C hC
    have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [hsum]
  refine hle.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_refl _

/-- The normalization in the form the budgets use: `#s ^ 2` against `m ^ 2`. -/
theorem sq_card_le_of_proxy_size {m : ℕ} (hm : 1 ≤ m) (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) :
    (s.card : ℝ) ^ 2 ≤ 4 * (Q.parts.card : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
  have h := card_le_two_mul_parts_mul (Q := Q) hm hM
  have h0 : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  nlinarith [h, h0]

/-! ### The chosen constants -/

/-- The tolerance at which the FINE partition is produced. It depends on the palette count
`K` and on the number of PROXIES `P` — both inputs to the fine step — and never on the
realized fine complexity. -/
noncomputable def proxyFineTolerance (K P : ℕ) : ℝ := 1 / (32 * K * P ^ 2)

/-- The deviation parameter the witness must supply for a cost target `τ`. Same dependence:
palette count and proxy count only. -/
noncomputable def proxyDeviationTolerance (K P : ℕ) (η τ : ℝ) : ℝ :=
  η ^ 2 * τ / (16 * K * P ^ 2)

theorem proxyFineTolerance_pos {K P : ℕ} (hK : 0 < K) (hP : 0 < P) :
    0 < proxyFineTolerance K P := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  rw [proxyFineTolerance]
  positivity

theorem proxyDeviationTolerance_pos {K P : ℕ} (hK : 0 < K) (hP : 0 < P) {η τ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) : 0 < proxyDeviationTolerance K P η τ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  rw [proxyDeviationTolerance]
  positivity

omit [DecidableEq V] in
/-- Both tolerances are antitone in the proxy count: more proxies is a stricter requirement,
never a weaker one. -/
theorem proxyFineTolerance_anti {K P P' : ℕ} (hK : 0 < K) (hP : 0 < P) (hPP : P ≤ P') :
    proxyFineTolerance K P' ≤ proxyFineTolerance K P := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hPP' : (P : ℝ) ≤ P' := by exact_mod_cast hPP
  rw [proxyFineTolerance, proxyFineTolerance]
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : (P : ℝ) ^ 2 ≤ (P' : ℝ) ^ 2 := by nlinarith [hPP', hP0.le]
  linarith [mul_nonneg hK0.le (sub_nonneg.mpr hsq)]

omit [DecidableEq V] in
theorem proxyDeviationTolerance_anti {K P P' : ℕ} (hK : 0 < K) (hP : 0 < P) (hPP : P ≤ P')
    {η τ : ℝ} (hτ : 0 ≤ τ) :
    proxyDeviationTolerance K P' η τ ≤ proxyDeviationTolerance K P η τ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hPP' : (P : ℝ) ≤ P' := by exact_mod_cast hPP
  have hsq : (P : ℝ) ^ 2 ≤ (P' : ℝ) ^ 2 := by nlinarith [hPP', hP0.le]
  rw [proxyDeviationTolerance, proxyDeviationTolerance]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith [mul_nonneg hK0.le (sub_nonneg.mpr hsq)]

/-! ### The two budgets at those constants -/

omit [DecidableEq V] in
/-- **`σ ≤ 1/2`.** The forbidden budget of step 2 at the weight floor `m / 2`, with the fine
partition produced at `proxyFineTolerance K P`. The `P ²` enters through `#s ^ 2 / m ^ 2` —
geometric normalization — and not through any count of events. -/
theorem proxySigma_le_half {K P m : ℕ} {B ε : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ P) (hm : 1 ≤ m)
    (hε0 : 0 ≤ ε) (hεle : ε ≤ proxyFineTolerance K P)
    (hB : B ≤ ε * (s.card : ℝ) ^ 2)
    (hn : (s.card : ℝ) ^ 2 ≤ 4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2) :
    (K : ℝ) * B / ((m : ℝ) / 2) ^ 2 ≤ 1 / 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale : ε * (32 * K * (P : ℝ) ^ 2) ≤ 1 := by
    rw [proxyFineTolerance, le_div_iff₀ (by positivity)] at hεle
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hB' : B ≤ ε * (4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2) :=
    hB.trans (mul_le_mul_of_nonneg_left hn hε0)
  calc (K : ℝ) * B
      ≤ (K : ℝ) * (ε * (4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hB' hK0.le
    _ = (ε * (32 * K * (P : ℝ) ^ 2)) * ((m : ℝ) ^ 2 / 8) := by ring
    _ ≤ 1 * ((m : ℝ) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = 1 / 2 * ((m : ℝ) / 2) ^ 2 := by ring

omit [DecidableEq V] in
/-- **`μ ≤ τ`.** The cost budget of step 3 at the same weight floor, with the witness's
deviation parameter at `proxyDeviationTolerance K P η τ`. -/
theorem proxyMu_le {K P m : ℕ} {δ η τ : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ P) (hm : 1 ≤ m)
    (hη : 0 < η) (hδ0 : 0 ≤ δ) (hδ : δ ≤ proxyDeviationTolerance K P η τ)
    (hn : (s.card : ℝ) ^ 2 ≤ 4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2) :
    (K : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) / ((m : ℝ) / 2) ^ 2 ≤ τ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale : δ * (16 * K * (P : ℝ) ^ 2) ≤ η ^ 2 * τ := by
    rw [proxyDeviationTolerance, le_div_iff₀ (by positivity)] at hδ
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hstep : δ / η ^ 2 * (s.card : ℝ) ^ 2
      ≤ δ / η ^ 2 * (4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  calc (K : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2)
      ≤ (K : ℝ) * (δ / η ^ 2 * (4 * (P : ℝ) ^ 2 * (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hK0.le
    _ = (δ * (16 * K * (P : ℝ) ^ 2)) * ((m : ℝ) ^ 2 / (4 * η ^ 2)) := by
        field_simp
        ring
    _ ≤ (η ^ 2 * τ) * ((m : ℝ) ^ 2 / (4 * η ^ 2)) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = τ * ((m : ℝ) / 2) ^ 2 := by
        field_simp
        ring

/-! ### The inequalities at a REALIZED proxy count -/

/-- `σ ≤ 1/2` stated at the realized proxy count `P = #Q.parts`, with the proxy-size
hypotheses supplied directly. Everything above is local to THIS partition: the tolerance was
chosen for this `P`, and nothing here licenses reusing it at another. -/
theorem proxySigma_le_half_of_parts {K m : ℕ} {B ε : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ Q.parts.card)
    (hm : 1 ≤ m) (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) (hε0 : 0 ≤ ε)
    (hεle : ε ≤ proxyFineTolerance K Q.parts.card) (hB : B ≤ ε * (s.card : ℝ) ^ 2) :
    (K : ℝ) * B / ((m : ℝ) / 2) ^ 2 ≤ 1 / 2 :=
  proxySigma_le_half hK hP hm hε0 hεle hB (sq_card_le_of_proxy_size hm hM)

/-- `μ ≤ τ` at the realized proxy count, likewise. -/
theorem proxyMu_le_of_parts {K m : ℕ} {δ η τ : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ Q.parts.card)
    (hm : 1 ≤ m) (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) (hη : 0 < η) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ proxyDeviationTolerance K Q.parts.card η τ) :
    (K : ℝ) * (δ / η ^ 2 * (s.card : ℝ) ^ 2) / ((m : ℝ) / 2) ^ 2 ≤ τ :=
  proxyMu_le hK hP hm hη hδ0 hδ (sq_card_le_of_proxy_size hm hM)

/-! ### Gate G-H1 — no global deviation parameter serves every proxy count -/

omit [DecidableEq V] in
/-- **Gate G-H1.** The deviation tolerance shrinks like `P ⁻²`, so for ANY positive `δ`
there is a positive proxy count at which `δ` exceeds it. Hence no positive `δ` satisfies the
`proxyMu_le` requirement UNIFORMLY over all positive proxy counts, and a `δ` fixed with no
constraint on `P` is not justified by anything proved here.

**What this does not prove.** `P` here is an arbitrary positive natural, not one realized by
a partition or by the pipeline. The gate therefore does not exhibit a produced proxy count
that violates a given `δ`, and it does not rule out choosing `δ` from an a priori upper
bound on `P`.

What it does establish is what Step 5 still lacks: either an a priori bound on `P` (or an
order of choice that fixes `P` first), or a deviation requirement that is `P`-free.
Recorded, not discharged. -/
theorem exists_proxyCount_gt_globalDeviation (K : ℕ) (hK : 0 < K) {η τ δ : ℝ}
    (hδ : 0 < δ) :
    ∃ P : ℕ, 0 < P ∧ proxyDeviationTolerance K P η τ < δ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨n, hn⟩ := exists_nat_gt (η ^ 2 * τ / (16 * K * δ))
  refine ⟨max n 1, lt_of_lt_of_le Nat.one_pos (le_max_right n 1), ?_⟩
  have hP1 : (1 : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right n 1
  have hPn : ((n : ℕ) : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left n 1
  have hPpos : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hP1
  have hkey : η ^ 2 * τ / (16 * K * δ) < ((max n 1 : ℕ) : ℝ) ^ 2 := by
    have hsq : ((max n 1 : ℕ) : ℝ) ≤ ((max n 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    linarith [hn.trans_le hPn]
  rw [proxyDeviationTolerance, div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at hkey
  nlinarith [hkey]

/-- **The conditioned conclusion.** With `σ ≤ 1/2` and `μ ≤ τ` the selection returned by
`exists_piFinset_forall_not_mem_bad_cost_le` has cost at most `2 * τ`: conditioning on
avoiding every forbidden event costs exactly the factor `1 / (1 - σ)`. -/
theorem proxyCost_le_two_mul {σ μ τ : ℝ} (hσ : σ ≤ 1 / 2) (hμ : μ ≤ τ) (hτ : 0 ≤ τ) :
    μ / (1 - σ) ≤ 2 * τ := by
  have h1 : (0 : ℝ) < 1 - σ := by linarith
  rw [div_le_iff₀ h1]
  nlinarith [hμ, hσ, hτ]

/-! ### Tests -/

section Tests

-- The `P ²` of the normalization and the discarded `9n²` pair envelope can share a numeral
-- without sharing a source: with `n` owners the grouping gives `P = 3n` proxies, so
-- `P ² = 9n²` — but this `P ²` came from `#s / m`, not from counting pairs.
theorem proxySq_eq_nine_mul_sq (n : ℕ) : (3 * n) ^ 2 = 9 * n ^ 2 := by ring

-- …and the two really are different quantities: the pair count is not the square.
example : 3 * 3 * (3 * 3 - 1) ≠ (3 * 3) ^ 2 := by decide

-- The normalization is a ratio of sizes: one proxy of every vertex forces `P` large, and
-- a single proxy holding everything forces `m` large. Both endpoints satisfy `#s ≤ 2Pm`.
example {m : ℕ} (hm : 1 ≤ m) (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) :
    (s.card : ℝ) ≤ 2 * (Q.parts.card : ℝ) * m :=
  card_le_two_mul_parts_mul hm hM

-- The chosen fine tolerance depends on the palette count and the PROXY count only — both
-- inputs to the fine step. It mentions no fine partition at all, which is the hard stop.
example (K P : ℕ) : proxyFineTolerance K P = 1 / (32 * K * P ^ 2) := rfl

example (K P : ℕ) (η τ : ℝ) :
    proxyDeviationTolerance K P η τ = η ^ 2 * τ / (16 * K * P ^ 2) := rfl

-- The fine tolerance shrinks as the proxy count grows: more proxies means a finer
-- normalization, never a weaker requirement.
example {K P P' : ℕ} (hK : 0 < K) (hP : 0 < P) (hPP : P ≤ P') :
    proxyFineTolerance K P' ≤ proxyFineTolerance K P :=
  proxyFineTolerance_anti hK hP hPP

-- Gate G-H1 in use: whatever positive deviation parameter is chosen, some positive proxy
-- count needs a smaller one, so no `δ` serves uniformly over all proxy counts. The `P` it
-- produces is an arbitrary positive natural, not one realized by a partition — hence the
-- gate constrains what Step 5 must supply, not what any produced partition does.
example (K : ℕ) (hK : 0 < K) (η τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : ℕ, 0 < P ∧ proxyDeviationTolerance K P η τ < δ :=
  exists_proxyCount_gt_globalDeviation K hK hδ

-- Both tolerances are antitone in the proxy count, so the claim covers the deviation
-- tolerance and not only the fine one.
example {K P P' : ℕ} (hK : 0 < K) (hP : 0 < P) (hPP : P ≤ P') {η τ : ℝ} (hτ : 0 ≤ τ) :
    proxyDeviationTolerance K P' η τ ≤ proxyDeviationTolerance K P η τ :=
  proxyDeviationTolerance_anti hK hP hPP hτ

example {K P : ℕ} (hK : 0 < K) (hP : 0 < P) {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    0 < proxyDeviationTolerance K P η τ :=
  proxyDeviationTolerance_pos hK hP hη hτ

-- The inequalities are stated at the realized count, so the tolerance and the partition
-- cannot silently drift apart.
example {K m : ℕ} {B ε : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ Q.parts.card) (hm : 1 ≤ m)
    (hM : ∀ C ∈ Q.parts, C.card ≤ m + 1) (hε0 : 0 ≤ ε)
    (hεle : ε ≤ proxyFineTolerance K Q.parts.card) (hB : B ≤ ε * (s.card : ℝ) ^ 2) :
    (K : ℝ) * B / ((m : ℝ) / 2) ^ 2 ≤ 1 / 2 :=
  proxySigma_le_half_of_parts hK hP hm hM hε0 hεle hB

-- The conditioned conclusion at the frozen half-budget is exactly a factor two.
example {τ : ℝ} (hτ : 0 ≤ τ) : τ / (1 - 1 / 2) ≤ 2 * τ :=
  proxyCost_le_two_mul (le_refl _) (le_refl τ) hτ

end Tests

end RegularityLemmata
