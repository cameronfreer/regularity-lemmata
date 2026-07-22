/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.IndependentSet
import RegularityLemmata.Graph.Uniformity

/-!
# Route (b) supplier checkpoint, item 2: the piece-supplier obligation (statement)

`ARCHITECTURE.md` route (b), supplier checkpoint (2026-07-22). This file FREEZES the
statement of the piece supplier as `Prop`-valued definitions and records, as
permanent gates, why the weighted-mass control of the existing regularity API does
not discharge it. **No proof is attempted here** — the checkpoint record in
`ARCHITECTURE.md` explains why the current diagonal-palette regularity API cannot
prove it and what mathematics is missing; per the reviewer's instruction the phase
STOPS for review at this point.

* `IsPieceFamily` — `t` pairwise-disjoint pieces inside a host `A`, of EQUAL
  cardinality `m`, with every ordered pair of distinct pieces `τ`-uniform for every
  relation of a finite family (ordered pairs quantified, so both directions).
* `PieceSupplierStatement` — the obligation: for every palette count, target count,
  and tolerance `τ > 0`, there are a retention floor `κ > 0` and a host threshold
  `N₀` — depending on `(K, t, τ)` ONLY, hence fixed before any partition is
  produced, with no inequality in which `τ` depends on its own output complexity —
  such that every sufficiently large host admits such a family carrying at least a
  `κ` fraction of the host mass.
* Gate **G-S1**: weighted bad-pair mass does NOT bound the unweighted bad-pair
  count. One heavy cell and seven unit cells with EVERY distinct ordered pair bad:
  the weighted mass passes the `τ = 3/49` regularity-style test, yet every
  pairwise-clean subfamily is a singleton — while an unweighted conversion at this
  `τ` would promise three clean pieces. Equal (or fixed-`Λ`-comparable) sizes must
  come BEFORE the independent-set extraction of `Finite/IndependentSet.lean`, and
  the readily available candidate cells retain only a `1/(2q)` fraction with `q`
  the output fine-part bound — a supplier tolerance `≤ target/(2q)` would recreate
  the circularity route (b) exists to avoid.

Provenance: the supplier is step 1 of the Lemma 3.6 construction in D. Conlon and
J. Fox, *Graph removal lemmas* (arXiv:1211.3487, §3.2) — there obtained from a
cylinder regularity lemma (their Lemma 3.4), or more weakly from Szemerédi plus
Turán; see `PROVENANCE.md` for the precise formalization scope.
-/

namespace RegularityLemmata

/-! ### The frozen statement -/

/-- `t` pairwise-disjoint pieces inside `A`, of equal cardinality `m`, with every
ordered pair of DISTINCT pieces `τ`-uniform for every relation of the family. -/
def IsPieceFamily {V : Type*} {K : ℕ} (Rk : Fin K → V → V → Prop)
    [∀ k, DecidableRel (Rk k)] (A : Finset V) (τ : ℝ) {t : ℕ} (m : ℕ)
    (P : Fin t → Finset V) : Prop :=
  (∀ i, P i ⊆ A) ∧
  (∀ i j : Fin t, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ i, (P i).card = m) ∧
  (∀ k : Fin K, ∀ i j : Fin t, i ≠ j → IsUniformPair (Rk k) (P i) (P j) τ)

/-- **The route (b) piece-supplier obligation** (STATEMENT ONLY — supplier
checkpoint, 2026-07-22): the retention floor `κ` and host threshold `N₀` depend on
`(K, t, τ)` alone, so they are fixed BEFORE any partition is produced and no
inequality lets `τ` depend on its own output complexity. The mass floor is stated
in multiplication form on the total `t·m`. -/
def PieceSupplierStatement : Prop :=
  ∀ (K t : ℕ) (τ : ℝ), 0 < τ →
  ∃ (κ : ℝ) (N₀ : ℕ), 0 < κ ∧
    ∀ (V : Type) (_ : DecidableEq V) (Rk : Fin K → V → V → Prop)
      (_ : ∀ k, DecidableRel (Rk k)) (A : Finset V), N₀ ≤ A.card →
    ∃ (m : ℕ) (P : Fin t → Finset V), 0 < m ∧
      IsPieceFamily Rk A τ m P ∧ κ * (A.card : ℝ) ≤ (t : ℝ) * m

/-! ### Gate G-S1 — weighted mass does not bound unweighted counts -/

section Gates

/-- One heavy cell and seven unit cells: the weight profile of the checkpoint
counterexample. -/
private abbrev wS : Fin 8 → ℕ := ![343, 1, 1, 1, 1, 1, 1, 1]

-- The weighted bad-pair mass of the ALL-pairs-bad relation passes the
-- regularity-style test at `τ = 3/49` (in multiplication form:
-- `49·mass ≤ 3·(Σw)²`, i.e. `49·4844 ≤ 3·350²`)…
example : 49 * ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin 8 × Fin 8 => p.1 ≠ p.2), wS p.1 * wS p.2
    ≤ 3 * ((∑ i, wS i) * (∑ i, wS i)) := by decide

-- …yet with every distinct ordered pair bad, every pairwise-clean subfamily is a
-- SINGLETON — while the unweighted conversion `|S| ≤ 2·(D+1)·|T|` at the
-- corresponding degree budget would promise three clean pieces out of eight.
-- Equal sizes must come before the extraction; they cannot be recovered after it.
example (T : Finset (Fin 8))
    (hclean : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ (x ≠ y)) : T.card ≤ 1 := by
  by_contra hcon
  have h2 : 1 < T.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
  exact hclean x hx y hy hxy hxy

end Gates

end RegularityLemmata
