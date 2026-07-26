/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.DiagonalGate
import RegularityLemmata.Relational.GraphCounting

/-!
# Route (b) ladder step 2: the transversalization certificate (statement and gates)

`ARCHITECTURE.md` route (b) ladder, step 2 (re-freeze 2026-07-26). The redesigned Phase 11
counts only triples of DISTINCT coarse cells and pays for repeated-cell triples with an
edit charge. That retirement of repeated-cell COUNTING is provisional, because an edit
charge on `C × C` changes WHICH pattern a within-cell triple induces without stopping it
inducing one. This file states the obligation that closes the gap, and tests it. **It
proves no cleaning achieves the certificate** — that is the open mathematics.

## The certificate

`IsTransversalizable N Q`: every three-vertex pattern realized ANYWHERE in the cleaned
model `N` is realized on a transversal cell triple of `Q`. Stated on the existing exact
decomposition `globalInducedCount = transversalInducedCount + nontransversal`
(`Relational/DiagonalGate.lean`), it is

    ∀ P, 0 < globalInducedCount P N Q → 0 < transversalInducedCount P N Q

and the converse implication is free (`transversalInducedCount_le_globalInducedCount`), so
the certificate says exactly that the two pattern SETS coincide.

**Why this is the weakest form sufficient for Phase 11.** The pattern-uniform certificate
needs, for each pattern surviving in `N`, a lower bound on its induced count in `M`; the
only counting available is transversal counting on representatives, which needs one
transversal realization of that pattern. It does not need every realization to be
transversal, nor the same triple, nor any statement about patterns absent from `N`.
`exists_transversal_of_isTransversalizable` is that consumption form.

## What the gates below establish

* **It is not automatic** (`G4` configuration, restated for the certificate): a host whose
  every induced path copy lies inside one cell fails it outright. So the certificate must
  be EARNED by the diagonal rounding; it cannot be assumed.
* **It forces at least three cells.** With fewer than three cells there are no transversal
  triples at all, so the certificate degenerates to "`N` realizes no three-vertex pattern"
  — false on any host with three vertices carrying a pattern. This is the small
  one- or two-cell test: the route needs `3 ≤ #Q.parts`, which the equipartition seed
  supplies, and no cleaning can rescue a one- or two-cell partition.
* **It is satisfiable** (singleton cells): when every cell is a singleton no repeated-cell
  triple admits an injective map, so global and transversal counts agree identically. The
  predicate is therefore not vacuous — but the witness is the degenerate partition that
  does no coarsening, which is precisely the tension the open gate must resolve: large
  cells are what make within-cell triples possible in the first place.

## The variants to weigh (recorded, not decided here)

1. *Monochromatic-triple rounding*: orient cell pairs by a linear order and recolor every
   cell interior to a palette orbit that also appears on a transversal triple of large
   cells — a multicolor Ramsey extraction over the cleaned palette assignment
   (`Finite/MulticolorRamsey.lean` already supplies the extraction) makes such a triple
   exist once the number of large cells beats the Ramsey bound. This targets the
   all-three-in-one-cell stratum.
2. *Clone/proxy cells*: split each large cell so that two-in-one-cell triples become
   transversal triples of the refined partition. This changes the representative event
   index, which is why the gate precedes selection.
3. *Separate repeated-cell lower bound*: abandon transversalization and instead bound the
   original-model copy count of repeated-cell realizations directly, which needs
   diagonal-inclusive regularity rather than the off-diagonal layer.

Variants 1 and 2 address different strata — all-three-in-one-cell and exactly-two-in-one-cell
respectively — and neither subsumes the other, so a positive route plausibly needs both.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-! ### The certificate -/

/-- **The transversalization certificate**: every three-vertex pattern realized anywhere in
`N` is realized on a triple of DISTINCT cells of `Q`. This is the obligation that makes the
retirement of repeated-cell counting sound; nothing in this file proves any cleaning
achieves it. -/
def IsTransversalizable (N : FiniteRelModel L V) (Q : Finpartition s) : Prop :=
  ∀ P : FiniteRelModel L (Fin 3),
    0 < globalInducedCount P N Q → 0 < transversalInducedCount P N Q

variable {P : FiniteRelModel L (Fin 3)} {N : FiniteRelModel L V} {Q : Finpartition s}

/-- The transversal count never exceeds the global count — so the converse implication in
the certificate is free, and the certificate says the two pattern sets coincide. -/
theorem transversalInducedCount_le_globalInducedCount :
    transversalInducedCount P N Q ≤ globalInducedCount P N Q := by
  rw [globalInducedCount_eq_transversal_add_nontransversal]
  omega

/-- The certificate, in set form: a pattern occurs in `N` exactly when it occurs
transversally. -/
theorem isTransversalizable_iff :
    IsTransversalizable N Q ↔
      ∀ P : FiniteRelModel L (Fin 3),
        (0 < globalInducedCount P N Q ↔ 0 < transversalInducedCount P N Q) := by
  constructor
  · intro h P
    exact ⟨h P, fun hT => lt_of_lt_of_le hT transversalInducedCount_le_globalInducedCount⟩
  · intro h P hP
    exact (h P).mp hP

/-- **The consumption form.** Under the certificate, a pattern surviving in `N` has an
explicit transversal cell triple carrying it — which is what a transversal counting lower
bound in the original model is applied to. -/
theorem exists_transversal_of_isTransversalizable (h : IsTransversalizable N Q)
    (hP : 0 < globalInducedCount P N Q) :
    ∃ T ∈ transversalCellTriples Q, 0 < inducedEmbeddingCountOn P N T := by
  have hpos := h P hP
  rw [transversalInducedCount] at hpos
  by_contra hcon
  push Not at hcon
  have : ∑ T ∈ transversalCellTriples Q, inducedEmbeddingCountOn P N T = 0 :=
    Finset.sum_eq_zero fun T hT => Nat.le_zero.mp (hcon T hT)
  omega

/-! ### The certificate forces at least three cells -/

/-- With fewer than three cells there is no transversal triple at all. -/
theorem transversalCellTriples_eq_empty_of_card_lt_three (Q : Finpartition s)
    (h : Q.parts.card < 3) : transversalCellTriples Q = (∅ : Finset (Fin 3 → Finset V)) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro T hT
  obtain ⟨hmem, hinj⟩ := mem_transversalCellTriples.mp hT
  have hcard : (Finset.univ : Finset (Fin 3)).card ≤ Q.parts.card :=
    Finset.card_le_card_of_injOn T (fun i _ => hmem i) (Function.Injective.injOn hinj)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **The one- or two-cell test.** Below three cells the certificate degenerates: it asserts
that `N` realizes NO three-vertex pattern anywhere. No cleaning can rescue such a
partition, so the route requires `3 ≤ #Q.parts` — which the equipartition seed supplies. -/
theorem globalInducedCount_eq_zero_of_card_lt_three (h : IsTransversalizable N Q)
    (hcard : Q.parts.card < 3) (P : FiniteRelModel L (Fin 3)) :
    globalInducedCount P N Q = 0 := by
  by_contra hcon
  have hpos : 0 < globalInducedCount P N Q := Nat.pos_of_ne_zero hcon
  have := h P hpos
  rw [transversalInducedCount, transversalCellTriples_eq_empty_of_card_lt_three Q hcard,
    Finset.sum_empty] at this
  omega

/-! ### The certificate is satisfiable (singleton cells) -/

/-- A repeated cell of size at most one admits no injective map, so its box count is zero. -/
theorem inducedEmbeddingCountOn_eq_zero_of_repeat_of_card_le_one {T : Fin 3 → Finset V}
    {i j : Fin 3} (hij : i ≠ j) (hT : T i = T j) (hcard : (T i).card ≤ 1) :
    inducedEmbeddingCountOn P N T = 0 := by
  rw [inducedEmbeddingCountOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf hcon
  rw [Fintype.mem_piFinset] at hf
  have h1 : f i ∈ T i := hf i
  have h2 : f j ∈ T i := hT ▸ hf j
  exact hij (hcon.1 (Finset.card_le_one.mp hcard _ h1 _ h2))

/-- **Satisfiability.** When every cell is a singleton, global and transversal counts agree
identically, so the certificate holds. The witness is the partition that does no
coarsening — which is exactly why satisfiability alone says nothing about the open gate:
large cells are what make within-cell triples possible. -/
theorem isTransversalizable_of_forall_card_le_one (N : FiniteRelModel L V)
    (Q : Finpartition s) (hQ : ∀ C ∈ Q.parts, C.card ≤ 1) : IsTransversalizable N Q := by
  intro P hP
  rw [globalInducedCount_eq_transversal_add_nontransversal] at hP
  have hzero : ∑ T ∈ nontransversalCellTriples Q, inducedEmbeddingCountOn P N T = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [nontransversalCellTriples, Finset.mem_filter, Fintype.mem_piFinset] at hT
    obtain ⟨hmem, hninj⟩ := hT
    rw [Function.not_injective_iff] at hninj
    obtain ⟨i, j, hEq, hne⟩ := hninj
    exact inducedEmbeddingCountOn_eq_zero_of_repeat_of_card_le_one hne hEq (hQ _ (hmem i))
  omega

/-! ### Gates -/

section Gates

/-- The path `0 — 1 — 2` on `Fin 3` (edges `01`, `12`; nonedge `02`). -/
private abbrev pathP : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

/-- A four-vertex host whose induced path copies all live inside `{0, 1, 2}`. -/
private abbrev pathHost4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

/-- The two-cell partition `{{0, 1, 2}, {3}}` of the `Fin 4` host. -/
private noncomputable abbrev cellsG4 : Finpartition (Finset.univ : Finset (Fin 4)) :=
  twoPartition (Finset.univ : Finset (Fin 4)) {0, 1, 2} (by decide) (by decide) (by decide)

-- **G4 restated for the certificate: it is NOT automatic.** Every induced path copy of the
-- host lies inside the cell `{0,1,2}`, so the pattern occurs globally and not transversally.
-- A cleaning that leaves such a configuration alone violates the certificate outright.
example : transversalInducedCount (ofSimpleGraph pathP) (ofSimpleGraph pathHost4) cellsG4
    = 0 := by decide

example : 0 < globalInducedCount (ofSimpleGraph pathP) (ofSimpleGraph pathHost4) cellsG4 := by
  decide

example : ¬ IsTransversalizable (ofSimpleGraph pathHost4) cellsG4 := by
  intro h
  have hpos := h (ofSimpleGraph pathP) (by decide)
  have hzero : transversalInducedCount (ofSimpleGraph pathP) (ofSimpleGraph pathHost4)
      cellsG4 = 0 := by decide
  omega

-- The two-cell partition has exactly two cells, so it is also excluded by the structural
-- three-cell requirement — the same failure seen from the cell-count side.
example : cellsG4.parts.card = 2 := twoPartition_card

example : transversalCellTriples cellsG4 = (∅ : Finset (Fin 3 → Finset (Fin 4))) :=
  transversalCellTriples_eq_empty_of_card_lt_three _ (by rw [twoPartition_card]; norm_num)

-- The starkest one-cell form: on the indiscrete partition every copy is nontransversal.
example : transversalCellTriples (Finpartition.indiscrete
    (show (Finset.univ : Finset (Fin 4)) ≠ ∅ by decide))
      = (∅ : Finset (Fin 3 → Finset (Fin 4))) := by
  refine transversalCellTriples_eq_empty_of_card_lt_three _ ?_
  rw [Finpartition.indiscrete_parts, Finset.card_singleton]
  norm_num

-- Satisfiability, on the discrete partition of the same host: every cell is a singleton,
-- so no repeated-cell triple carries an injective map and the certificate holds.
example : IsTransversalizable (ofSimpleGraph pathHost4)
    (⊥ : Finpartition (Finset.univ : Finset (Fin 4))) :=
  isTransversalizable_of_forall_card_le_one _ _ (by decide)

end Gates

end RegularityLemmata
