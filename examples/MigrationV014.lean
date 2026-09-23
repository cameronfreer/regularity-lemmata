/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.FiniteRamsey
import RegularityLemmata.RelationalApproximation
import RegularityLemmata.Partition.Grouping

/-!
# Migration consumer for the US-English identifiers

A compiled check of exactly the public API surface that v0.14.0 renames (see the v0.14.0
entry of `CHANGELOG.md`): the four renamed public declarations and one explicit
named-argument application `(color := …)`. Nothing here is mathematics; a downstream project
migrating from v0.13.0 can copy these uses. Keeping this file compiling is what verifies that
the advertised migration targets exist under their new names.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

/-- `BinaryTreeTwoColouring` → `BinaryTreeTwoColoring`, and the binder `colour` → `color`
applied by name. -/
theorem migration_binaryTreeRamsey_two (a b : ℕ) (c : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + b + 1), ∀ x, c (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (a + b + 1), ∀ x, c (e x) = 1) :=
  binaryTreeRamsey_two a b (color := c)

/-- `labelFibre` → `labelFiber` and `labelFibre_eq_empty_iff` → `labelFiber_eq_empty_iff`. -/
example {V Λ : Type*} [DecidableEq V] [DecidableEq Λ] (lab : V → Λ) (s : Finset V) (a : Λ)
    (h : ∀ v ∈ s, lab v ≠ a) : labelFiber lab s a = ∅ :=
  (labelFiber_eq_empty_iff lab s a).mpr h

/-- `exists_fibre_labelling` → `exists_fiber_labeling`. -/
example {β : Type*} [DecidableEq β] (d k : ℕ) (S : Finset β) (hS : S.card = d * k) :
    ∃ g : β → ℕ, (∀ x ∈ S, g x < k) ∧ ∀ j < k, (S.filter fun x => g x = j).card = d :=
  exists_fiber_labeling d k S hS

end RegularityLemmataExamples
