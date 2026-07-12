/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.PatternCounts
import RegularityLemmata.Finite.PairDensity
import RegularityLemmata.Relational.HypergraphAdapters
import Mathlib.Algebra.BigOperators.Field

/-!
# Binary vertex profiles and two-way pair palettes

Phase 9 unit 1 (design freeze in `ARCHITECTURE.md`): the vocabulary for regularizing
the **binary reduct** of a finite relational model, over the **complete two-way
palette** rather than each symbol independently.

* `binaryVertexProfile M v` records every unary relation at `v` and every binary
  loop `R(v,v)` — the data atomized into vertex profiles (Phase 9 unit 2).
* `binaryPairPalette M a b` records every binary symbol **jointly** and in **both
  directions** `(R(a,b), R(b,a))`; `swapBinaryPairPalette` implements the reversal law
  (`binaryPairPalette_swap`, involutive). `HasBinaryPairPalette M c a b` is the
  palette-color relation, with `∃!` color per ordered pair
  (`existsUnique_hasBinaryPairPalette`) and the partition of unity on any rectangle
  (`sum_pairCount_hasBinaryPairPalette`, `sum_pairDensity_hasBinaryPairPalette`).

Cardinalities: `#BinaryVertexProfile = 2^(#unary + #binary)` and
`#BinaryPairPalette = 4^(#binary)` — `4^m`, not `2^m`, because each binary symbol
contributes the *ordered* truth pair. Three kernel-`decide` falsification examples
(joint-symbol correlation, direction correlation, loop/profile sensitivity) show why
the full two-way palette and the vertex profiles are both necessary.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}

/-! ### Vertex profiles -/

/-- The binary vertex profile: every unary relation at `v`, and every binary loop
`R(v, v)`. -/
abbrev BinaryVertexProfile (L : FirstOrder.Language) [FiniteRelational L] :=
  (L.Relations 1 → Bool) × (L.Relations 2 → Bool)

/-- The profile of a vertex. -/
def binaryVertexProfile (M : FiniteRelModel L V) (v : V) : BinaryVertexProfile L :=
  (fun U => M.rel U ![v], fun R => M.rel R ![v, v])

/-! ### Two-way pair palettes -/

/-- The two-way pair palette: for every binary symbol, the ordered truth pair
`(R(a, b), R(b, a))`. -/
abbrev BinaryPairPalette (L : FirstOrder.Language) [FiniteRelational L] :=
  L.Relations 2 → Bool × Bool

instance : DecidableEq (BinaryPairPalette L) :=
  inferInstanceAs (DecidableEq (L.Relations 2 → Bool × Bool))

instance : Fintype (BinaryPairPalette L) :=
  inferInstanceAs (Fintype (L.Relations 2 → Bool × Bool))

/-- The palette of an ordered pair. -/
def binaryPairPalette (M : FiniteRelModel L V) (a b : V) : BinaryPairPalette L :=
  fun R => (M.rel R ![a, b], M.rel R ![b, a])

/-- Coordinate swap on palettes, implementing direction reversal. -/
def swapBinaryPairPalette (c : BinaryPairPalette L) : BinaryPairPalette L :=
  fun R => (c R).swap

/-- **Reversal law**: swapping the pair swaps every palette coordinate. -/
theorem binaryPairPalette_swap (M : FiniteRelModel L V) (a b : V) :
    binaryPairPalette M b a = swapBinaryPairPalette (binaryPairPalette M a b) := by
  funext R
  simp [binaryPairPalette, swapBinaryPairPalette, Prod.swap]

/-- The swap is an involution. -/
theorem swapBinaryPairPalette_involutive :
    Function.Involutive (swapBinaryPairPalette (L := L)) := by
  intro c
  funext R
  simp [swapBinaryPairPalette, Prod.swap_swap]

/-- The palette-color relation: `a, b` carry palette `c`. -/
def HasBinaryPairPalette (M : FiniteRelModel L V) (c : BinaryPairPalette L)
    (a b : V) : Prop :=
  binaryPairPalette M a b = c

instance (M : FiniteRelModel L V) (c : BinaryPairPalette L) :
    DecidableRel (HasBinaryPairPalette M c) :=
  fun a b => inferInstanceAs (Decidable (binaryPairPalette M a b = c))

/-- **Exactly one palette per ordered pair.** -/
theorem existsUnique_hasBinaryPairPalette (M : FiniteRelModel L V) (a b : V) :
    ∃! c : BinaryPairPalette L, HasBinaryPairPalette M c a b :=
  ⟨binaryPairPalette M a b, rfl, fun _ hc => hc.symm⟩

/-! ### Partition of unity on a rectangle -/

/-- **Palette count partition**: over any rectangle, the per-palette pair counts sum
to `|A|·|B|`. -/
theorem sum_pairCount_hasBinaryPairPalette (M : FiniteRelModel L V) (A B : Finset V) :
    ∑ c : BinaryPairPalette L, pairCount (HasBinaryPairPalette M c) A B
      = A.card * B.card := by
  classical
  have hcongr : ∀ c : BinaryPairPalette L,
      pairCount (HasBinaryPairPalette M c) A B
        = ((A ×ˢ B).filter fun p => binaryPairPalette M p.1 p.2 = c).card :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun c _ => hcongr c,
    ← Finset.card_eq_sum_card_fiberwise
      (fun p _ => Finset.mem_univ (binaryPairPalette M p.1 p.2)),
    Finset.card_product]

/-- **Palette density partition of unity**: over a nonempty rectangle, the per-palette
pair densities sum to `1`. On an empty side every density is `0`, so the sum is `0`
(the honest statement — see the test). -/
theorem sum_pairDensity_hasBinaryPairPalette (M : FiniteRelModel L V) (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B = 1 := by
  have hpos : (0 : ℝ) < (A.card : ℝ) * B.card := by
    have := A.card_pos.mpr hA
    have := B.card_pos.mpr hB
    positivity
  have hsum : ∑ c : BinaryPairPalette L, pairDensity (HasBinaryPairPalette M c) A B
      = (∑ c : BinaryPairPalette L, (pairCount (HasBinaryPairPalette M c) A B : ℝ))
        / ((A.card : ℝ) * B.card) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => pairDensity_eq_count_div
  rw [hsum, ← Nat.cast_sum, sum_pairCount_hasBinaryPairPalette, Nat.cast_mul,
    div_self hpos.ne']

/-! ### Palette cardinalities -/

/-- `#BinaryVertexProfile = 2^(#unary + #binary)`. -/
theorem card_binaryVertexProfile :
    Fintype.card (BinaryVertexProfile L)
      = 2 ^ (Fintype.card (L.Relations 1) + Fintype.card (L.Relations 2)) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    pow_add]

/-- `#BinaryPairPalette = 4^(#binary)` — four two-way colors per binary symbol. -/
theorem card_binaryPairPalette :
    Fintype.card (BinaryPairPalette L) = 4 ^ Fintype.card (L.Relations 2) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]

/-! ### Tests and adversarial examples -/

/-- A one-binary-symbol test model from a Boolean adjacency. -/
private def binModel {V : Type*} [DecidableEq V] (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

/-- A two-binary-symbol test model from two Boolean adjacencies. -/
private def binModel2 {V : Type*} [DecidableEq V] (p q : V → V → Bool) :
    FiniteRelModel (coloredRelLang 2 2) V :=
  ⟨fun {_n} R x =>
    (if R.1 = 0 then p else q) (x (Fin.cast R.2.symm 0)) (x (Fin.cast R.2.symm 1))⟩

section Tests

open FiniteRelModel

-- Empty side: every palette density is 0, so the sum is 0, not 1.
example (M : FiniteRelModel (singleRelLang 2) (Fin 3)) (B : Finset (Fin 3)) :
    ∑ c : BinaryPairPalette (singleRelLang 2),
      pairDensity (HasBinaryPairPalette M c) ∅ B = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [pairDensity_eq_count_div, pairCount]
  simp

/-- **Direction correlation.** Two one-binary-symbol models on `Fin 3` with equal
forward and reverse adjacency counts but different `(true, true)`-palette counts: a
symmetric relation `{(0,1),(1,0),(2,2)}` versus a `3`-cycle `{(0,1),(1,2),(2,0)}`.
One-way colors cannot tell them apart; the two-way palette can. -/
example :
    let sym := binModel (V := Fin 3) fun a b =>
      decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 2))
    let cyc := binModel (V := Fin 3) fun a b =>
      decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0))
    (pairCount (fun a b => sym.Holds (singleRelSymbol 2) ![a, b])
        Finset.univ Finset.univ
      = pairCount (fun a b => cyc.Holds (singleRelSymbol 2) ![a, b])
        Finset.univ Finset.univ)
    ∧ (pairCount (fun a b => sym.Holds (singleRelSymbol 2) ![b, a])
        Finset.univ Finset.univ
      = pairCount (fun a b => cyc.Holds (singleRelSymbol 2) ![b, a])
        Finset.univ Finset.univ)
    ∧ (pairCount (HasBinaryPairPalette sym fun _ => (true, true))
        Finset.univ Finset.univ
      ≠ pairCount (HasBinaryPairPalette cyc fun _ => (true, true))
        Finset.univ Finset.univ) := by decide

/-- **Loop/profile sensitivity.** Two models with identical off-diagonal data
(everything false off the diagonal) but different loops have different vertex
profiles — the loop must be atomized into the profile, not dismissed as collision
error. -/
example :
    let loop := binModel (V := Fin 2) fun a b => decide (a = b)
    let noloop := binModel (V := Fin 2) fun _ _ => false
    (∀ a b : Fin 2, a ≠ b →
        binaryPairPalette loop a b = binaryPairPalette noloop a b)
      ∧ binaryVertexProfile loop 0 ≠ binaryVertexProfile noloop 0 := by
  refine ⟨by decide, by decide⟩

/-- **Joint-symbol correlation.** With two binary symbols, two models can agree on
each symbol's marginal count yet differ on the joint `R ∧ S` palette count — so
per-symbol regularity does not supply induced counting for Boolean combinations. -/
example :
    let both := binModel2 (V := Fin 2) (fun a b => decide (a ≠ b))
      (fun a b => decide (a ≠ b))
    let split := binModel2 (V := Fin 2) (fun a b => decide (a ≠ b))
      (fun a b => decide (a = b))
    (pairCount (fun a b => both.Holds (coloredRelSymbol 2 2 0) ![a, b])
        Finset.univ Finset.univ
      = pairCount (fun a b => split.Holds (coloredRelSymbol 2 2 0) ![a, b])
        Finset.univ Finset.univ)
    ∧ (pairCount (fun a b => both.Holds (coloredRelSymbol 2 2 1) ![a, b])
        Finset.univ Finset.univ
      = pairCount (fun a b => split.Holds (coloredRelSymbol 2 2 1) ![a, b])
        Finset.univ Finset.univ)
    ∧ (pairCount (fun a b => both.Holds (coloredRelSymbol 2 2 0) ![a, b]
          ∧ both.Holds (coloredRelSymbol 2 2 1) ![a, b]) Finset.univ Finset.univ
      ≠ pairCount (fun a b => split.Holds (coloredRelSymbol 2 2 0) ![a, b]
          ∧ split.Holds (coloredRelSymbol 2 2 1) ![a, b])
          Finset.univ Finset.univ) := by decide

-- The cardinality formulas, concretely: one binary symbol gives four palettes.
example : Fintype.card (BinaryPairPalette (singleRelLang 2)) = 4 := by decide

end Tests

end RegularityLemmata
