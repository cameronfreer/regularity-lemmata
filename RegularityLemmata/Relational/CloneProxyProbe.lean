/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.OrientationProbe

/-!
# Route (b) ladder step 2: the clone/proxy gate

`ARCHITECTURE.md` route (b) ladder step 2 (2026-07-27). The transversalization certificate
fails for repeated-cell triples, and the clone/proxy idea is that splitting each coarse
cell into PROXY cells turns those triples into transversal ones. This file tests that idea
on a concrete configuration.

**Modelling only.** No partition is constructed, no rounding, no representatives, no edits,
no cleaning. `IsTransversalizable` remains unachieved and `11B` remains closed.

## The configuration

Carrier `Fin 18`, three coarse cells of six vertices, each split into **three proxy cells
of two vertices**:

* `cpCoarse v = v / 6` — the coarse cell, one of `0, 1, 2`;
* `cpProxy v = v % 6 / 2` — the proxy inside that coarse cell, one of `0, 1, 2`;
* a proxy cell is a pair `(cpCoarse v, cpProxy v)`, so there are nine, each of size two.

The single directed binary symbol carries an **oriented diagonal palette orbit** inside a
coarse cell (forward on the local vertex order, its swap backwards) and a **directed
off-diagonal palette** between coarse cells (forward on the coarse order). Both are
non-symmetric, so orientation is visible.

## What the gate establishes

Every one of the FIVE placement strata transports to a triple in three DISTINCT proxy
cells, via `preservesAndReflects_transport_three`:

| stratum | representative | proxy-distinct target |
| --- | --- | --- |
| all coarse cells distinct | `(0, 6, 12)` | itself |
| `0 = 1` | `(0, 1, 6)` | `(0, 2, 6)` |
| `0 = 2` | `(0, 6, 1)` | `(0, 6, 2)` |
| `1 = 2` | `(6, 0, 1)` | `(6, 0, 2)` |
| all equal | `(0, 1, 2)` | `(0, 2, 4)` |

The moves only ever replace a vertex by another of the SAME coarse cell with the SAME
relative local order, which is why the palettes — and hence the induced patterns — are
unchanged.

## Three sharpness tests

* **Two proxies do not suffice** for the all-equal stratum: three vertices in two proxy
  cells collide by pigeonhole.
* **One proxy does not suffice** for the two-in-one stratum: without splitting, the two
  same-coarse vertices stay in one cell.
* **Ignoring orientation fails** for an asymmetric palette: replacing a within-cell vertex
  by one of the OPPOSITE relative order changes the palette, so a transport that ignores
  the local order does not apply.

## What it does NOT establish

Nothing about an actual partition, an actual cleaning, or arbitrary configurations. In
particular the moves above are exhibited, not constructed by a general lemma; and a real
proxy split must still be shown compatible with representative selection, whose event
index it would change.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

section CloneProxy

/-- A one-binary-symbol model from a Boolean relation. -/
private def binModel {V : Type*} (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

/-- The coarse cell of a vertex: three cells of six. -/
private abbrev cpCoarse (v : Fin 18) : ℕ := (v : ℕ) / 6

/-- The proxy inside the coarse cell: three proxies of two. -/
private abbrev cpProxy (v : Fin 18) : ℕ := (v : ℕ) % 6 / 2

/-- The configuration: an oriented diagonal palette orbit inside each coarse cell, a
directed palette between coarse cells. Both non-symmetric. -/
private abbrev cpModel : FiniteRelModel (singleRelLang 2) (Fin 18) :=
  binModel fun x y =>
    if cpCoarse x = cpCoarse y then decide ((x : ℕ) < (y : ℕ))
    else decide (cpCoarse x < cpCoarse y)

/-! ### The configuration is nondegenerate -/

-- Nine proxy cells of two vertices each: `0` and `1` share one, `0` and `2` do not.
example : cpCoarse 0 = cpCoarse 1 ∧ cpProxy 0 = cpProxy 1 := by decide

example : cpCoarse 0 = cpCoarse 2 ∧ cpProxy 0 ≠ cpProxy 2 := by decide

example : cpCoarse 0 ≠ cpCoarse 6 := by decide

-- Both palettes are non-symmetric, so orientation is visible in each.
example :
    binaryPairPalette cpModel 0 1
      ≠ swapBinaryPairPalette (binaryPairPalette cpModel 0 1) := by decide

example :
    binaryPairPalette cpModel 0 6
      ≠ swapBinaryPairPalette (binaryPairPalette cpModel 0 6) := by decide

-- All vertex profiles agree, which the transport lemma needs.
example : ∀ x y : Fin 18,
    binaryVertexProfile cpModel x = binaryVertexProfile cpModel y := by decide

/-! ### The five placement strata all transport to three distinct proxy cells -/

-- Stratum 1: all coarse cells distinct — already proxy-distinct, nothing to move.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P cpModel ![0, 6, 12] ↔
      PreservesAndReflects P cpModel ![0, 6, 12] := Iff.rfl

example : cpProxy 0 ≠ cpProxy 6 ∨ cpCoarse 0 ≠ cpCoarse 6 := by decide

-- Stratum 2: coordinates `0` and `1` share a coarse cell — and here a proxy cell too.
-- Moving the second to `2` separates the proxies and preserves every palette.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P cpModel ![0, 1, 6] ↔ PreservesAndReflects P cpModel ![0, 2, 6] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- Stratum 3: coordinates `0` and `2` share a coarse cell.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P cpModel ![0, 6, 1] ↔ PreservesAndReflects P cpModel ![0, 6, 2] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- Stratum 4: coordinates `1` and `2` share a coarse cell.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P cpModel ![6, 0, 1] ↔ PreservesAndReflects P cpModel ![6, 0, 2] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- Stratum 5: all three in one coarse cell. Three proxies are exactly enough.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P cpModel ![0, 1, 2] ↔ PreservesAndReflects P cpModel ![0, 2, 4] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- Each target really does occupy three distinct proxy cells.
example : (cpCoarse 0, cpProxy 0) ≠ (cpCoarse 2, cpProxy 2) ∧
    (cpCoarse 0, cpProxy 0) ≠ (cpCoarse 6, cpProxy 6) ∧
    (cpCoarse 2, cpProxy 2) ≠ (cpCoarse 6, cpProxy 6) := by decide

example : (cpCoarse 0, cpProxy 0) ≠ (cpCoarse 2, cpProxy 2) ∧
    (cpCoarse 0, cpProxy 0) ≠ (cpCoarse 4, cpProxy 4) ∧
    (cpCoarse 2, cpProxy 2) ≠ (cpCoarse 4, cpProxy 4) := by decide

/-! ### Sharpness -/

-- **Two proxies do not suffice.** With only two proxy classes per coarse cell, any three
-- vertices of one coarse cell put two in the same class — pigeonhole, stated concretely.
example : ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    ((x : ℕ) / 3 = (y : ℕ) / 3) ∨ ((x : ℕ) / 3 = (z : ℕ) / 3)
      ∨ ((y : ℕ) / 3 = (z : ℕ) / 3) := by decide

-- **One proxy does not suffice.** Without splitting, two vertices of one coarse cell stay
-- in the same cell, so the two-in-one stratum is never transversal.
example : ∀ x y : Fin 18, cpCoarse x = cpCoarse y →
    ((cpCoarse x, (0 : ℕ)) = (cpCoarse y, (0 : ℕ))) := by decide

-- **Ignoring orientation fails.** Replacing a within-cell vertex by one of the OPPOSITE
-- relative local order changes the palette, so the transport hypothesis is violated: an
-- orientation-blind proxy move is unsound for an asymmetric palette.
example :
    binaryPairPalette cpModel 0 2 ≠ binaryPairPalette cpModel 2 0 := by decide

example :
    binaryPairPalette cpModel (![0, 1, 6] 0) (![0, 1, 6] 1)
      ≠ binaryPairPalette cpModel (![2, 0, 6] 0) (![2, 0, 6] 1) := by decide

end CloneProxy

end RegularityLemmata
