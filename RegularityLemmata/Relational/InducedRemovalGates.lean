/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.GraphCounting
import RegularityLemmata.Relational.Edit

/-!
# Phase 11 unit 2: falsification gates for the induced-removal freeze

Permanent kernel-`decide` gates for the Phase 11 scope and normalization freeze
(`ARCHITECTURE.md`). Each gate refutes a tempting simplification of the frozen design or
pins a normalization decision; the exact quantitative removal statements remain
provisional until the feasibility gate passes, and **nothing in this file is part of the
removal API**.

* **G1 — subgraph deletion creates induced copies.** Deleting one edge of the complete
  graph creates two induced path copies: induced removal cannot be deletion-only.
* **G2 — recoloring can create copies, with exact edit accounting.** The same instance
  as a single-pair palette recolor costs exactly `2` aggregate edits and raises an
  induced count from `0` to `2`.
* **G3 — no spare palette.** The path pattern requires both symmetric graph palettes,
  and graph adapters never realize the asymmetric ones: no fixed "safe" palette exists.
* **G4 — a planted within-cell copy is invisible to transversal counting.** All induced
  path copies of a host can sit inside one cell of a partition, where
  `transversalInducedCount` sees nothing.
* **G5 — unary-only degeneracy.** In a unary-only language a positive induced count can
  be removed only by unary edits: the edit budget must be the all-arity
  `aggregateEditCount`/`relativeAggregateEdit`, never a binary-only measure.
* **G6 — binary loops are profile data.** In a binary-only language, loop values alone
  can force copies that no constant off-diagonal recoloring removes; loop edits belong
  to the profile-cleaning layer.
* **G7 — swap-consistency is a realizability condition.** A swap-inconsistent palette
  assignment is realized by no model (`binaryPairPalette_swap`); the recolor primitive
  must take swap-consistent assignments.
* **G8 — nullary preservation.** Nullary incompatibility forces induced count zero
  unconditionally, and a family containing both nullary types is coherent with a
  nullary-preserving cleaning: the incompatible member is vacuously absent.
* **G9 — scope degeneracies.** Hosts with fewer than three vertices have count zero;
  duplicate members, the empty family, and an infinite constant family are all
  harmless; the guard-free `≤` endpoint keeps the empty host meaningful.
* **G10 — role-pair palette incompatibility.** Two representative role pairs below the
  same coarse pair can have DISJOINT palette supports; a role-independent palette
  choice then has no positive density floor valid for every placement. Per-pair
  density closeness rules this out; aggregate deviance alone does not.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

/-! ### Test fixtures -/

/-- The path `0 — 1 — 2` on `Fin 3` (edges `01`, `12`; nonedge `02`). -/
private abbrev pathP : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 2

/-- The complete graph on `Fin 3` with the edge `01` deleted (edges `02`, `12`). -/
private abbrev topMinus01 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 2 ∨ a = 1 ∧ b = 2

/-- The path `0 — 1 — 2` inside `Fin 4`, with vertex `3` isolated. -/
private abbrev pathHost4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 2

/-- Unary-only: every vertex marked. -/
private def marked : FiniteRelModel (singleRelLang 1) (Fin 3) := ⟨fun {_} _ _ => true⟩

/-- Unary-only: no vertex marked. -/
private def unmarked : FiniteRelModel (singleRelLang 1) (Fin 3) := ⟨fun {_} _ _ => false⟩

/-- Binary-only: loops true, off-diagonal pairs false. -/
private def loopOnly : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  ⟨fun {n} _ x => if h : n = 2 then decide (x (Fin.cast h.symm 0) = x (Fin.cast h.symm 1))
    else false⟩

/-- Binary-only: loops true and off-diagonal pairs true (everything true at arity two). -/
private def loopFull : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  ⟨fun {n} _ _ => decide (n = 2)⟩

/-- Binary-only: everything false (in particular loops false). -/
private def binEmpty : FiniteRelModel (singleRelLang 2) (Fin 3) := ⟨fun {_} _ _ => false⟩

/-- Nullary-only: the nullary symbol holds. -/
private def nullTrue : FiniteRelModel (singleRelLang 0) (Fin 3) := ⟨fun {_} _ _ => true⟩

/-- Nullary-only: the nullary symbol fails. -/
private def nullFalse : FiniteRelModel (singleRelLang 0) (Fin 3) := ⟨fun {_} _ _ => false⟩

/-! ### G1 — subgraph deletion creates induced copies -/

-- The complete host has no induced path copies…
example : inducedEmbeddingCountOn (ofSimpleGraph pathP)
    (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) (fun _ : Fin 3 => Finset.univ) = 0 := by decide

-- …and deleting the single edge `01` CREATES two induced path copies. Deletion-only
-- cleaning (the Phase 7 `triadCleaned` shape, mathlib's `G' ≤ G` removal) cannot work.
example : inducedEmbeddingCountOn (ofSimpleGraph pathP)
    (ofSimpleGraph topMinus01) (fun _ : Fin 3 => Finset.univ) = 2 := by decide

/-! ### G2 — recoloring can create copies, with exact ordered-tuple edit accounting -/

-- The same instance as a palette recolor: the pair `{0, 1}` moves from the all-adjacent
-- to the all-nonadjacent palette; the other two pairs keep their palettes.
example : binaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) 0 1 = adjPalette ∧
    binaryPairPalette (ofSimpleGraph topMinus01) 0 1 = nonadjPalette := by decide

example : binaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) 0 2
      = binaryPairPalette (ofSimpleGraph topMinus01) 0 2 ∧
    binaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) 1 2
      = binaryPairPalette (ofSimpleGraph topMinus01) 1 2 := by decide

-- One recolored unordered pair costs exactly `2` aggregate edits (both orientations of
-- the one binary symbol) and strictly increases an induced count (`0 → 2`, G1). Every
-- recolor step of the cleaning must therefore respect the global invariant, not merely
-- its own color.
example : aggregateEditCount (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
    (ofSimpleGraph topMinus01) = 2 := by decide

/-! ### G3 — no spare palette -/

-- The path pattern requires BOTH symmetric palettes among its three pair slots…
example : binaryPairPalette (ofSimpleGraph pathP) 0 1 = adjPalette ∧
    binaryPairPalette (ofSimpleGraph pathP) 0 2 = nonadjPalette := by decide

-- …and graph adapters never realize either asymmetric palette, so no fixed "safe"
-- symmetric palette avoids the path pattern and its complement simultaneously:
-- constant-palette recoloring is unavailable.
example : ∀ a b : Fin 3,
    binaryPairPalette (ofSimpleGraph pathP) a b ≠ (fun _ => (true, false)) ∧
    binaryPairPalette (ofSimpleGraph pathP) a b ≠ (fun _ => (false, true)) := by decide

/-! ### G4 — a planted within-cell copy is invisible to transversal counting -/

-- Both induced path copies of the `Fin 4` host live inside the cell `{0, 1, 2}` of the
-- two-cell partition `{{0, 1, 2}, {3}}`: the transversal count is `0` while the global
-- count is `2`. A cleaning argument whose counting runs only over transversal triples
-- proves nothing here — this is what makes diagonal-inclusive regularity load-bearing.
example : transversalInducedCount (ofSimpleGraph pathP) (ofSimpleGraph pathHost4)
    (twoPartition (Finset.univ : Finset (Fin 4)) {0, 1, 2} (by decide) (by decide)
      (by decide)) = 0 := by decide

example : inducedEmbeddingCountOn (ofSimpleGraph pathP) (ofSimpleGraph pathHost4)
    (fun _ : Fin 3 => (Finset.univ : Finset (Fin 4))) = 2 := by decide

-- The starkest form: on the indiscrete (single-cell) partition `⊤`, EVERY copy is
-- nontransversal.
example : transversalInducedCount (ofSimpleGraph pathP) (ofSimpleGraph pathHost4)
    (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) = 0 := by decide

/-! ### G5 — unary-only degeneracy pins the all-arity edit measure -/

-- The unary-only language has NO binary tuples at all, so any "binary edits only"
-- removal statement is vacuously immovable here…
example : Fintype.card ((singleRelLang 1).Relations 2) = 0 := by decide

-- …yet the all-marked pattern has positive induced count in the all-marked host,
example : inducedEmbeddingCount marked marked = 6 := by decide

-- and removal IS achievable — by exactly three unary edits (all of `aggregateEditCount`
-- lives at arity one; the budget `aggregateTupleBudget = 3` is the unary tuple count).
example : inducedEmbeddingCount marked unmarked = 0 := by decide

example : aggregateEditCount marked unmarked = 3 ∧
    aggregateTupleBudget (singleRelLang 1) (Fin 3) = 3 := by decide

/-! ### G6 — binary loops are profile data; loop edits belong to the profile layer -/

-- In the binary-only language, the loops-true/off-diagonal-false pattern has six copies
-- in its own host…
example : inducedEmbeddingCount loopOnly loopOnly = 6 := by decide

-- …and recoloring EVERY off-diagonal pair to the other symmetric palette merely trades
-- it for the loops-true/off-diagonal-true pattern: constant off-diagonal recoloring
-- cannot escape the loop-true pattern family.
example : inducedEmbeddingCount loopFull loopFull = 6 := by decide

-- Killing the loops kills both members at once (profile mismatch), for the cost of
-- three loop edits: loop values are vertex-profile data, cleaned in layer two.
example : inducedEmbeddingCount loopOnly binEmpty = 0 ∧
    inducedEmbeddingCount loopFull binEmpty = 0 := by decide

example : aggregateEditCount loopOnly binEmpty = 3 := by decide

/-! ### G7 — swap-consistency is a realizability condition on recoloring -/

-- A swap-inconsistent palette assignment exists as raw data…
example : ∃ χ : Fin 2 → Fin 2 → BinaryPairPalette (singleRelLang 2),
    χ 1 0 ≠ swapBinaryPairPalette (χ 0 1) :=
  ⟨fun a b _ => if a = 0 ∧ b = 1 then (true, false) else (false, false), by decide⟩

-- …but every actual model satisfies the reversal law, so no model realizes it: the
-- pair-recoloring primitive must take swap-consistent assignments (recolor both
-- orientations atomically) or its output is not a palette assignment of any model.
example {V : Type*} (M : FiniteRelModel (singleRelLang 2) V) (a b : V) :
    binaryPairPalette M b a = swapBinaryPairPalette (binaryPairPalette M a b) :=
  binaryPairPalette_swap M a b

/-! ### G8 — nullary preservation -/

-- Nullary incompatibility forces induced count zero unconditionally…
example : inducedEmbeddingCount nullTrue nullFalse = 0 := by decide

example : inducedEmbeddingCount nullTrue nullTrue = 6 := by decide

-- …so a family containing BOTH nullary types is coherent with a nullary-preserving
-- cleaning: against any fixed host, the incompatible member is vacuously absent and
-- stays absent (the cleaning never edits nullary symbols).
example : ∀ b : Bool, inducedEmbeddingCount (if b then nullTrue else nullFalse) nullTrue
    = if b then 6 else 0 := by decide

/-! ### G9 — scope degeneracies -/

-- Hosts with fewer than three vertices: no injective triple exists, count is zero.
example : inducedEmbeddingCount (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
    (ofSimpleGraph (⊤ : SimpleGraph (Fin 2))) = 0 := by decide

-- The empty host, concretely (under the frozen `≤` endpoint the removal statement stays
-- meaningful here: the hypothesis `count ≤ δ·0³` holds and `N := M` closes it).
example : inducedEmbeddingCount (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
    (ofSimpleGraph (⊥ : SimpleGraph (Fin 0))) = 0 := by decide

-- Duplicate members of a family are harmless (the cleaning is one model, the
-- conclusion is pointwise).
example (M : FiniteRelModel (singleRelLang 1) (Fin 3)) :
    ∀ i : Fin 2, inducedEmbeddingCount ((fun _ => marked) i) M
      = inducedEmbeddingCount marked M :=
  fun _ => rfl

-- The empty family is vacuously removable at zero edits.
example : ∀ i : Empty, inducedEmbeddingCount ((fun j => j.elim) i : FiniteRelModel
    (singleRelLang 1) (Fin 3)) marked = 0 :=
  fun i => i.elim

-- An infinite constant family (`ι = ℕ`) demands nothing beyond its single member:
-- the frozen statement quantifies over an arbitrary index type with no finiteness.
example : ∀ _i : ℕ, inducedEmbeddingCount marked unmarked = 0 := fun _ => by decide

/-! ### G10 — role-pair palette incompatibility (11A checkpoint, round 2) -/

/-- One edge `0 — 2` inside `Fin 4`; in particular `1, 3` is a nonedge. -/
private abbrev oneEdge02 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 2

-- Two representative role pairs below the SAME coarse pair (`C = {0,1}`, `D = {2,3}`,
-- with `rep C 0 = {0}`, `rep C 1 = {1}`, `rep D 1 = {2}`, `rep D 2 = {3}`) can have
-- DISJOINT palette supports: `({0},{2})` realizes only the all-adjacent palette while
-- `({1},{3})` realizes only the all-nonadjacent one. A cleaner that assigns ONE
-- palette to the coarse pair, independent of the role pair through which it is
-- realized, then has no positive density floor valid for every placement: whichever
-- palette is chosen, some role pair supports it with density zero. Unit 7's per-pair
-- density-closeness clause rules this configuration out among the SELECTED
-- representatives (all six role-pair densities are within `2η` of the common coarse
-- density); an aggregate deviant-cost clause alone does NOT — hence the
-- role-independent rounding certificate is a standing obligation of any re-scope
-- that drops per-pair closeness.
example : pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) adjPalette)
    {0} {2} = 1 := by decide

example : pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) nonadjPalette)
    {0} {2} = 0 := by decide

example : pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) adjPalette)
    {1} {3} = 0 := by decide

example : pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) nonadjPalette)
    {1} {3} = 1 := by decide

-- The incompatibility is not an artifact of tiny boxes: no palette has positive
-- count on BOTH role pairs simultaneously.
example : ∀ c : BinaryPairPalette FirstOrder.Language.graph,
    pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) c) {0} {2} = 0
    ∨ pairCount (HasBinaryPairPalette (ofSimpleGraph oneEdge02) c) {1} {3} = 0 := by
  decide

end RegularityLemmata
