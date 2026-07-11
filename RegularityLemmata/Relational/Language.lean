/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.ModelTheory.Basic

/-!
# Finite relational languages

Phase 8 unit 1 (design freeze in `ARCHITECTURE.md`): a typeclass carving the
**finite relational** fragment out of mathlib's first-order languages
(`FirstOrder.Language`, `Mathlib.ModelTheory.Basic`) — no function symbols,
finitely many decidable relation symbols at each arity, and none above an explicit
`arityBound`. The bound is an upper bound, not necessarily attained (the empty
language has bound `0`). No competing language syntax is introduced; mathlib's
`Structure.RelMap` already interprets relations on ordered tuples `Fin n → M`,
exactly the convention this library uses.

The bounded symbol type `RelSymbol L = Σ n : Fin (arityBound + 1), L.Relations n`
bridges arbitrary mathlib symbols to bounded computation: every symbol's arity is
at most the bound (`arity_le_arityBound` — a symbol above it would inhabit an empty
type), and `RelSymbol.mk'` packages any symbol with its arity. Emptiness above the
bound is consumed through that theorem, not an aggressive instance.

**Arity zero is supported**: a nullary relation has exactly one tuple (the empty
one) even on an empty carrier — a permanent adversarial test, not a corner case.

The class lives in the `RegularityLemmata` namespace so the axiom audit walks it;
`singleRelLang r` (one symbol at arity `r`) is provided here as the running test
language and for the hypergraph adapters.
-/

namespace RegularityLemmata

open FirstOrder

/-- A finite relational language: no function symbols, finitely many decidable
relation symbols at each arity, and no symbols above `arityBound` — an upper
bound, not necessarily attained. -/
class FiniteRelational (L : FirstOrder.Language) where
  /-- An upper bound on the arities of relation symbols (not necessarily
  attained). -/
  arityBound : ℕ
  /-- No function symbols. -/
  functionsEmpty : L.IsRelational
  /-- Finitely many relation symbols at each arity. -/
  relationsFintype : ∀ n, Fintype (L.Relations n)
  /-- Decidable equality of relation symbols at each arity. -/
  relationsDecidableEq : ∀ n, DecidableEq (L.Relations n)
  /-- No relation symbols above the bound. -/
  relationsEmptyAbove : ∀ n, arityBound < n → IsEmpty (L.Relations n)

variable (L : FirstOrder.Language) [FiniteRelational L]

/-- The arity bound of a finite relational language. -/
def arityBound : ℕ := FiniteRelational.arityBound L

instance (n : ℕ) : IsEmpty (L.Functions n) := FiniteRelational.functionsEmpty n

instance (n : ℕ) : Fintype (L.Relations n) := FiniteRelational.relationsFintype n

instance (n : ℕ) : DecidableEq (L.Relations n) :=
  FiniteRelational.relationsDecidableEq n

/-- Emptiness above the bound, as a theorem (not an instance, to keep instance
search unambiguous). -/
theorem isEmpty_relations_of_lt {n : ℕ} (h : arityBound L < n) :
    IsEmpty (L.Relations n) :=
  FiniteRelational.relationsEmptyAbove n h

/-- Every symbol's arity is at most the bound: a symbol above it would inhabit an
empty type. -/
theorem arity_le_arityBound {n : ℕ} (R : L.Relations n) : n ≤ arityBound L := by
  by_contra h
  push Not at h
  exact (FiniteRelational.relationsEmptyAbove n h).false R

/-- The bounded symbol type: relation symbols indexed by their (bounded) arity.
Finite and decidable by construction — the computational enumeration of a finite
relational signature. -/
abbrev RelSymbol : Type _ :=
  Σ n : Fin (arityBound L + 1), L.Relations (n : ℕ)

/-- Package any symbol with its (bounded) arity. -/
def RelSymbol.mk' {L : FirstOrder.Language} [FiniteRelational L] {n : ℕ}
    (R : L.Relations n) : RelSymbol L :=
  ⟨⟨n, Nat.lt_succ_of_le (arity_le_arityBound L R)⟩, R⟩

/-- Every bounded symbol is a packaging of its own second component. -/
theorem RelSymbol.eq_mk' (s : RelSymbol L) : s = RelSymbol.mk' s.2 := rfl

/-! ### The running test language -/

/-- The relational language with exactly one relation symbol, at arity `r`. -/
def singleRelLang (r : ℕ) : FirstOrder.Language.{0, 0} :=
  ⟨fun _ => Empty, fun n => if n = r then Unit else Empty⟩

instance (r : ℕ) : FiniteRelational (singleRelLang r) where
  arityBound := r
  functionsEmpty := fun _ => inferInstanceAs (IsEmpty Empty)
  relationsFintype := fun n => by
    by_cases h : n = r <;> simp only [singleRelLang, h, if_true, if_false] <;>
      infer_instance
  relationsDecidableEq := fun n => by
    by_cases h : n = r <;> simp only [singleRelLang, h, if_true, if_false] <;>
      infer_instance
  relationsEmptyAbove := fun n hn => by
    have h : n ≠ r := by omega
    simp only [singleRelLang, h, if_false]
    infer_instance

/-- The unique symbol of the one-symbol language. -/
def singleRelSymbol (r : ℕ) : (singleRelLang r).Relations r :=
  cast (if_pos rfl : (if r = r then Unit else Empty) = Unit).symm Unit.unit

/-! ### Tests and adversarial examples -/

section Tests

-- Every symbol's arity is bounded, instance-level.
example (R : (singleRelLang 2).Relations 2) :
    (2 : ℕ) ≤ arityBound (singleRelLang 2) :=
  arity_le_arityBound _ R

-- Above the bound there are no symbols.
example : IsEmpty ((singleRelLang 2).Relations 5) :=
  isEmpty_relations_of_lt _ (by decide : arityBound (singleRelLang 2) < 5)

-- The bounded symbol enumeration of the one-symbol language has exactly one
-- element (kernel decide).
example : Fintype.card (RelSymbol (singleRelLang 2)) = 1 := by decide

-- Arity zero is a first-class citizen: the nullary one-symbol language enumerates
-- to one bounded symbol as well.
example : Fintype.card (RelSymbol (singleRelLang 0)) = 1 := by decide

-- Packaging round-trip.
example (s : RelSymbol (singleRelLang 3)) : s = RelSymbol.mk' s.2 :=
  RelSymbol.eq_mk' _ s

end Tests

end RegularityLemmata
