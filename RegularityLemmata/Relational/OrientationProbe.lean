/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Transversalization

/-!
# Route (b) ladder step 2: the orientation/profile probe

`ARCHITECTURE.md` route (b) ladder step 2, the sanctioned narrow probe (2026-07-27). The
monochromatic-triple variant of the transversalization gate hinges on one combinatorial
question, asked here and nowhere else:

> When a cell's interior is oriented by the internal vertex order and a triple of cells is
> oriented by the canonical cell order, do the within-cell triple and the cross-cell triple
> induce the SAME three-vertex model?

**This file answers that question on concrete configurations only.** It builds no rounding,
no Ramsey extraction, no representative selection, and no cleaning; it does not prove the
transversalization certificate for any partition. `IsTransversalizable`
(`Relational/Transversalization.lean`) remains unachieved and `11B` remains closed.

## The configuration

Carrier `Fin 6`, cells given by `probeCell = ![0, 0, 0, 1, 2, 3]`: one three-element cell
`{0, 1, 2}` and three singleton cells `{3}`, `{4}`, `{5}`. The relation is a single
DIRECTED binary symbol whose palette is deliberately NON-SYMMETRIC (`R x y` without
`R y x`), since a symmetric palette makes the orientation question vacuous.

* `probeMatched` — within a cell, orient by the internal vertex order; across cells,
  orient by the cell order. **Matched.**
* `probeReversed` — identical except the cross-cell orientation is reversed. This is the
  adversarial test.
* `probeLoops` — matched orientation, but the three-element cell's vertices carry loops
  and the singletons do not, so the vertex profiles differ.

## What the probe establishes

1. **Matched orientation, equal profiles**: the within-cell triple `(0,1,2)` and the
   cross-cell triple `(3,4,5)` induce the SAME `Fin 3` model — the transitive tournament in
   the non-symmetric palette. The orientation convention is therefore compatible, which is
   the step the monochromatic-triple variant needs.
2. **Reversed orientation**: the cross-cell triple no longer induces that model — on the
   fixed tuple `(3,4,5)` it induces the OPPOSITE tournament, a different three-vertex
   model. Aligning the canonical cell order with the internal vertex order is load-bearing,
   not cosmetic.
3. **Differing loop data**: with matched orientation but unequal profiles the cross-cell
   triple again fails to induce the within-cell model. Profile equality across the three
   cells — loops included — is a genuine hypothesis of any monochromatic-triple argument,
   so the extraction that produces the three cells must control profiles as well as
   palettes.

The headline hypotheses are pinned at the APIs a general theorem will quantify over:
profile equality via `binaryVertexProfile` (for ALL vertices of the matched configuration),
and palette non-symmetry via `binaryPairPalette` against `swapBinaryPairPalette`.

## What it does NOT establish

The general lemma — for an arbitrary palette, arbitrary cells, and the actual rounding — is
not proved here. Nor does it touch the exactly-two-in-one-cell stratum, which remains a
separate gate (clone/proxy cells). A positive probe is evidence to continue, not a licence
to build.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

/-! ### The probe configuration -/

section Probe

/-- A one-binary-symbol model from a Boolean relation. -/
private def binModel {V : Type*} (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

/-- The probe's cells: `{0,1,2}` together with the singletons `{3}`, `{4}`, `{5}`. -/
private abbrev probeCell : Fin 6 → Fin 4 := ![0, 0, 0, 1, 2, 3]

/-- **Matched orientation**: inside a cell, orient by the internal vertex order; across
cells, by the cell order. -/
private abbrev probeMatched : FiniteRelModel (singleRelLang 2) (Fin 6) :=
  binModel fun x y =>
    if probeCell x = probeCell y then decide (x < y) else decide (probeCell x < probeCell y)

/-- **Reversed orientation** — the adversarial variant: the cross-cell orientation runs
against the cell order. -/
private abbrev probeReversed : FiniteRelModel (singleRelLang 2) (Fin 6) :=
  binModel fun x y =>
    if probeCell x = probeCell y then decide (x < y) else decide (probeCell y < probeCell x)

/-- **Differing loop data** — matched orientation, but only the three-element cell's
vertices carry loops. -/
private abbrev probeLoops : FiniteRelModel (singleRelLang 2) (Fin 6) :=
  binModel fun x y =>
    if x = y then decide (probeCell x = 0)
    else if probeCell x = probeCell y then decide (x < y)
    else decide (probeCell x < probeCell y)

/-- The target three-vertex model: the transitive tournament in the non-symmetric palette,
without loops. -/
private abbrev tournament3 : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  binModel fun a b => decide (a < b)

/-- The same with loops at every vertex. -/
private abbrev tournament3Loops : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  binModel fun a b => decide (a ≤ b)

/-- The opposite tournament — the model the REVERSED configuration induces. -/
private abbrev tournament3Opp : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  binModel fun a b => decide (b < a)

/-! ### The palette is genuinely non-symmetric -/

-- Without this the orientation question is vacuous: `R 0 1` holds and `R 1 0` does not.
example : tournament3.Holds (singleRelSymbol 2) ![0, 1] := by decide

example : ¬ tournament3.Holds (singleRelSymbol 2) ![1, 0] := by decide

-- The same fact at the PALETTE API the general theorem will use: the two-way palette is
-- not fixed by the reversal law.
example :
    binaryPairPalette tournament3 0 1
      ≠ swapBinaryPairPalette (binaryPairPalette tournament3 0 1) := by decide

/-! ### 1. Matched orientation and equal profiles: the models agree -/

-- The profiles are equal across ALL vertices of the matched configuration — the hypothesis
-- the general theorem will carry, pinned at the profile API rather than left implicit.
example : ∀ x y : Fin 6,
    binaryVertexProfile probeMatched x = binaryVertexProfile probeMatched y := by decide

-- The WITHIN-CELL triple `(0,1,2)` induces the transitive tournament…
example : PreservesAndReflects tournament3 probeMatched ![0, 1, 2] := by decide

-- …and so does the CROSS-CELL triple `(3,4,5)`, on three distinct cells. The two triples
-- induce the SAME `Fin 3` model, which is what the monochromatic-triple variant needs.
example : PreservesAndReflects tournament3 probeMatched ![3, 4, 5] := by decide

-- Both are genuine induced copies of the same pattern in the same model.
example : 0 < inducedEmbeddingCount tournament3 probeMatched := by decide

-- The matching is up to a CHOICE of ordering: the cross-cell triple must be listed in cell
-- order. Permuting it breaks the match, which is harmless for the certificate (it asks
-- only for SOME transversal realization) but must be respected when one is exhibited.
example : ¬ PreservesAndReflects tournament3 probeMatched ![4, 3, 5] := by decide

/-! ### 2. Reversed orientation: the agreement fails -/

-- The within-cell triple still induces the tournament…
example : PreservesAndReflects tournament3 probeReversed ![0, 1, 2] := by decide

-- …but the cross-cell triple does NOT: reversing the canonical cell order against the
-- internal vertex order breaks the match. Orientation alignment is load-bearing.
example : ¬ PreservesAndReflects tournament3 probeReversed ![3, 4, 5] := by decide

-- It induces the OPPOSITE tournament instead — the palette, not just the labelling, has
-- changed, which is exactly why a symmetric palette would have hidden the issue. Stated on
-- the FIXED tuple `(3,4,5)`, so the claim is about the model induced there and not about a
-- relabelling.
example : PreservesAndReflects tournament3Opp probeReversed ![3, 4, 5] := by decide

-- Equivalently, by relabelling: the reversed configuration realizes the original
-- tournament only in the reversed order.
example : PreservesAndReflects tournament3 probeReversed ![5, 4, 3] := by decide

-- And the two three-vertex models genuinely differ.
example : binaryPairPalette tournament3 0 1 ≠ binaryPairPalette tournament3Opp 0 1 := by
  decide

/-! ### 3. Differing loop data: the agreement fails -/

-- With loops on the three-element cell only, the within-cell triple induces the
-- looped tournament…
example : PreservesAndReflects tournament3Loops probeLoops ![0, 1, 2] := by decide

-- …which the cross-cell triple cannot induce, matched orientation notwithstanding.
example : ¬ PreservesAndReflects tournament3Loops probeLoops ![3, 4, 5] := by decide

-- The obstruction is exactly the vertex profile, loops included.
example : binaryVertexProfile probeLoops 0 ≠ binaryVertexProfile probeLoops 3 := by decide

-- So a monochromatic-triple extraction must control profiles as well as palettes: three
-- cells agreeing on palettes but differing in loop data do not serve.
example : binaryVertexProfile probeLoops 3 = binaryVertexProfile probeLoops 4 := by decide

end Probe

end RegularityLemmata
