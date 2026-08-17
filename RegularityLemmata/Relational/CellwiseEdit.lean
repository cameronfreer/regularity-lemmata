/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Indivisible
import RegularityLemmata.Finite.HomogeneousCell
import RegularityLemmata.Finite.Edit

/-!
# Cellwise edit bounds and majority rounding

Two models over the same carrier are **cellwise `ε`-close** over a partition `P` when, on every
box of cells and at every *positive* arity, they disagree on at most an `ε`-fraction of the
ordered tuples of that box. That is `CellwiseEditBound`. Together with
`FiniteRelModel.IsIndivisibleFor` and `NullaryCompatible` it is the third leg of the triple an
approximate blow-up statement concludes with.

The file then constructs a witness: `FiniteRelModel.majorityRound` rounds each relation to the
cellwise majority bit, and the box-level lemma `editDistance_majorityRound_le_min` bounds its
edit count by `min d (1 - d)` times the box mass. Both the unconditional half bound and the
`ε` bound from cell homogeneity are derived from that one lemma, and
`exists_isIndivisibleFor_of_isHomogeneousCell` packages the three clauses. The converse
`isHomogeneousCell_of_cellwiseEditBound` recovers homogeneity at exactly the same `ε`.

Everything is **arbitrary-arity and stability-free**: no arity bound, no `AtMostBinary`, and no
stability, order-property, ladder, tree, VC, or Littlestone notion appears anywhere.

## `CellwiseEditBound` is packaging, not new capability

The predicate **packages existing density machinery and adds no expressive power.** The clause
is already expressible out of the pinned API — `editDistance` against a product of cell
cardinalities, or equivalently `relativeEditDistance ≤ ε`, which `cellwiseEditBound_iff_relative`
supplies as one rewrite. What the name buys is surface: it bundles a three-fold quantifier plus
two casts, gives `mono`, `symm`, `trans` and the rounding theorems a subject, names the third leg
of a triple whose other two legs are named, and absorbs a later change of internal spelling.
Those are API-stability and compositionality arguments, not capability arguments.

## Frozen conventions

* **Positive arity only.** The definition quantifies over `0 < n`. At `n = 0` the box is the
  singleton `{Fin.elim0}` and the empty product is `1`, so the clause would read
  `editDistance ≤ ε` and would permit a nullary flip as soon as `ε ≥ 1`. Arity zero is governed
  instead by the exact `NullaryCompatible`, which `nullaryCompatible_majorityRound` supplies for
  the rounded model. This mirrors `FiniteRelModel.isIndivisibleFor_iff_pos`.
* **Ordered tuples, diagonals included.** Boxes are `Fintype.piFinset`, so repeated entries
  `x i = x j` are counted and `C` may repeat a cell. No exceptional set is subtracted and no
  injectivity is assumed, matching `Relational/Edit.lean`'s per-symbol edit count and
  `Relational/Indivisible.lean`'s exception-free tiling. An injective-restricted variant is a
  different statement and must not be conflated with this one.
* **The casts.** The comparison type is `ℝ`, dictated by `ε`. There is one outer cast on the
  edit count and one cast **per factor** in the product, `∏ i, ((C i).card : ℝ)` rather than a
  single cast of the product. The per-factor form is the right-hand shape of the pinned
  `card_filter_le_of_tupleDensity_le`, so those lemmas apply without `push_cast`.
* **Empty boxes.** The predicate is guard-free and vacuously true on a box with an empty side
  (`0 ≤ ε * 0`), for every `ε`, negative included. For boxes built from `P.parts` the case does
  not arise, since parts are nonempty; the lemmas below use that internally, so none of them
  carries a nonemptiness hypothesis.
* **Off support, and the tie convention of `majorityRound`.** The threshold is the **ℕ**
  comparison `|box| ≤ 2 * tupleCount`, which keeps the construction computable. Two visible
  consequences, both intended: a tie (`|box| = 2 * tupleCount`) rounds to `true`, and a tuple
  with an entry outside `s` has an empty cell box, so its threshold reads `0 ≤ 0` and it also
  rounds to **`true`**. `majorityRound` is public for a general `Finpartition s`, so this is
  part of its contract, not an internal detail; the test section pins it. A consumer wanting
  "false off support" must say so separately — no such clause is stated here.

## Deliberately not claimed

* **No stability.** Nothing here produces the partition `P`; every statement takes it as given.
* **No refinement monotonicity at fixed `ε`.** Where `IsIndivisible.mono_of_le` passes exact
  indivisibility down to any finer `Q ≤ P`, the approximate clause fails: a refined cell is
  smaller, so the budget `ε * ∏ |cell|` shrinks while the edits can concentrate. A
  `decide`-checked witness is in the test section, labelled as an intentional non-lemma. No such
  lemma may be added.
* **No congruence API.** Congruence in the model collapses to `FiniteRelModel.ext_holds` (two
  models with the same `Holds` are equal) and congruence in the partition to `rfl`, so neither
  carries content. The genuinely generic structure in that family is metric, and it is shipped
  under its honest names, `CellwiseEditBound.symm` and `CellwiseEditBound.trans`.
* **No blow-up object and no uniqueness.** `majorityRound` is a model on the same carrier `V`,
  not a structure on `P.parts`; no quotient `FiniteRelModel` is built. Nothing claims the
  approximating model is unique, or best among the routes considered.

**Placement.** This is the first file in the library that *constructs* a `FiniteRelModel`, and
the construction is computable — no `noncomputable`, no `Classical.dec` in the definition. It is
a separate file rather than an addition to `Relational/Indivisible.lean`, whose frozen docstring
records that approximate indivisibility is not defined there and that no blow-up model is
constructed; both statements stay true.
-/

namespace RegularityLemmata

open Finset FirstOrder

/-! ### The predicate -/

/-- On every box of cells over `P`, at every **positive** arity, the two models disagree on at
most an `ε`-fraction of the ordered tuples. Arity zero is governed separately by
`NullaryCompatible`. This packages the pinned edit-count machinery; see the module docstring for
why it adds no expressive power. -/
def CellwiseEditBound {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}
    [DecidableEq V] {s : Finset V} (M N : FiniteRelModel L V) (P : Finpartition s)
    (ε : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → P.parts),
    (editDistance (M.Holds S) (N.Holds S) (fun i ↦ (C i : Finset V)) : ℝ)
      ≤ ε * ∏ i, ((C i : Finset V).card : ℝ)

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- **The bridge to the pinned density form.** Since every cell is nonempty, the count form of
the definition and `relativeEditDistance ≤ ε` are interchangeable, box by box. Both pinned
spellings are therefore one rewrite apart. -/
theorem cellwiseEditBound_iff_relative {M N : FiniteRelModel L V} {P : Finpartition s}
    {ε : ℝ} :
    CellwiseEditBound M N P ε ↔ ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → P.parts),
      relativeEditDistance (M.Holds S) (N.Holds S) (fun i ↦ (C i : Finset V)) ≤ ε := by
  refine forall_congr' fun n ↦ imp_congr_right fun _ ↦ forall_congr' fun S ↦
    forall_congr' fun C ↦ ?_
  have hne : ∀ i, ((C i : Finset V)).Nonempty := fun i ↦ P.nonempty_of_mem_parts (C i).2
  have hpos : (0 : ℝ) < ∏ i, ((C i : Finset V).card : ℝ) :=
    Finset.prod_pos fun i _ ↦ by exact_mod_cast Finset.card_pos.mpr (hne i)
  rw [relativeEditDistance_eq, Fintype.card_piFinset, Nat.cast_prod, div_le_iff₀ hpos]

/-! ### Tolerance and metric structure

Monotonicity in `ε` is genuinely generic — the box mass is a product of casts, hence
nonnegative — and so are symmetry and the triangle inequality, which come from
`editDistance_comm` and `editDistance_triangle`. -/

/-- The bound only weakens as the tolerance grows. -/
theorem CellwiseEditBound.mono {M N : FiniteRelModel L V} {P : Finpartition s} {ε ε' : ℝ}
    (h : CellwiseEditBound M N P ε) (hε : ε ≤ ε') : CellwiseEditBound M N P ε' := fun n hn S C ↦
  (h n hn S C).trans
    (mul_le_mul_of_nonneg_right hε (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))

/-- Symmetry, from `editDistance_comm`. -/
theorem CellwiseEditBound.symm {M N : FiniteRelModel L V} {P : Finpartition s} {ε : ℝ}
    (h : CellwiseEditBound M N P ε) : CellwiseEditBound N M P ε := by
  intro n hn S C
  rw [editDistance_comm]
  exact h n hn S C

/-- The triangle inequality, at the summed tolerance, from `editDistance_triangle`. -/
theorem CellwiseEditBound.trans {M N N' : FiniteRelModel L V} {P : Finpartition s} {ε₁ ε₂ : ℝ}
    (h₁ : CellwiseEditBound M N P ε₁) (h₂ : CellwiseEditBound N N' P ε₂) :
    CellwiseEditBound M N' P (ε₁ + ε₂) := by
  intro n hn S C
  have htri : (editDistance (M.Holds S) (N'.Holds S) (fun i ↦ (C i : Finset V)) : ℝ)
      ≤ (editDistance (M.Holds S) (N.Holds S) (fun i ↦ (C i : Finset V)) : ℝ)
        + (editDistance (N.Holds S) (N'.Holds S) (fun i ↦ (C i : Finset V)) : ℝ) := by
    exact_mod_cast editDistance_triangle (R₁ := M.Holds S) (R₂ := N.Holds S) (R₃ := N'.Holds S)
      (A := fun i ↦ (C i : Finset V))
  linarith [h₁ n hn S C, h₂ n hn S C]

/-- **Vacuity above `1`.** At tolerance `1` the budget is the whole box, so *any* two models are
cellwise `1`-close. The predicate therefore carries information only below `1`, and — through
`cellwiseEditBound_majorityRound_half` — the rounding witness already meets `1/2`. -/
theorem cellwiseEditBound_of_one_le (M N : FiniteRelModel L V) (P : Finpartition s) {ε : ℝ}
    (hε : 1 ≤ ε) : CellwiseEditBound M N P ε := by
  intro n hn S C
  have hcast : ((Fintype.piFinset fun i ↦ (C i : Finset V)).card : ℝ)
      = ∏ i, ((C i : Finset V).card : ℝ) := by rw [Fintype.card_piFinset, Nat.cast_prod]
  have h1 : (editDistance (M.Holds S) (N.Holds S) fun i ↦ (C i : Finset V) : ℝ)
      ≤ ∏ i, ((C i : Finset V).card : ℝ) := by
    rw [← hcast]; exact_mod_cast editDistance_le_card
  have h2 : (0 : ℝ) ≤ ∏ i, ((C i : Finset V).card : ℝ) :=
    Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _
  nlinarith

/-! ### Cellwise majority rounding

The threshold is a **ℕ** comparison, which keeps the construction computable and makes
`majorityRound_holds_iff` literally `decide_eq_true_iff`. See the module docstring for the tie
and off-support conventions that choice fixes. -/

/-- **Cellwise majority rounding** of `M` along `P`: a symbol holds of a tuple exactly when at
least half the tuples of its cell box satisfy it in `M`. The threshold is the ℕ comparison
`|box| ≤ 2 * tupleCount`, so the construction is computable; ties, and tuples off the support
(whose cell box is empty), round to `true`. -/
def FiniteRelModel.majorityRound {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}
    [DecidableEq V] {s : Finset V} (M : FiniteRelModel L V) (P : Finpartition s) :
    FiniteRelModel L V where
  rel := fun {_n} S x ↦
    decide ((Fintype.piFinset (fun i ↦ P.part (x i))).card
      ≤ 2 * tupleCount (M.Holds S) (fun i ↦ P.part (x i)))

/-- The threshold, readable: no instance-irrelevance step is needed. -/
theorem majorityRound_holds_iff (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ}
    (S : L.Relations n) (x : Fin n → V) :
    (M.majorityRound P).Holds S x
      ↔ (Fintype.piFinset (fun i ↦ P.part (x i))).card
          ≤ 2 * tupleCount (M.Holds S) (fun i ↦ P.part (x i)) :=
  decide_eq_true_iff

/-- The rounded model is indivisible for `P`: its truth value is computed from the tuple of
cells, so entrywise equal cells give equal values. -/
theorem majorityRound_isIndivisibleFor (M : FiniteRelModel L V) (P : Finpartition s) :
    (M.majorityRound P).IsIndivisibleFor P := by
  intro n S x y hx hy hpart
  rw [majorityRound_holds_iff, majorityRound_holds_iff,
    show (fun i ↦ P.part (x i)) = (fun i ↦ P.part (y i)) from funext hpart]

/-- Rounding is the identity at arity zero: the arity-zero box is a singleton, so the threshold
reads `1 ≤ 2 * (1 or 0)`. Hence the nullary datum is preserved exactly. -/
theorem nullaryCompatible_majorityRound (M : FiniteRelModel L V) (P : Finpartition s) :
    NullaryCompatible M (M.majorityRound P) := by
  intro S
  rw [majorityRound_holds_iff]
  have hbox : (Fintype.piFinset (fun i : Fin 0 ↦ P.part (Fin.elim0 i))).card = 1 := by simp
  rw [hbox]
  constructor
  · -- `M` holds of the empty tuple, so the arity-zero count is `1` and `1 ≤ 2 * 1`.
    intro hS
    have h1 : 0 < tupleCount (M.Holds S) (fun i : Fin 0 ↦ P.part (Fin.elim0 i)) := by
      rw [tupleCount]
      exact Finset.card_pos.mpr ⟨Fin.elim0, Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun i ↦ i.elim0, hS⟩⟩
    omega
  · -- `M` fails of it, so the count is `0` and the threshold `1 ≤ 0` cannot hold.
    intro hthr
    by_contra hS
    have h0 : tupleCount (M.Holds S) (fun i : Fin 0 ↦ P.part (Fin.elim0 i)) = 0 := by
      rw [tupleCount, Finset.card_eq_zero]
      refine Finset.filter_false_of_mem fun z _ ↦ ?_
      rwa [show z = Fin.elim0 from funext fun i ↦ i.elim0]
    omega

/-! ### The box-level heart

This is the canonical statement of the rounding estimate: the exact `min d (1 - d)` form, from
which both the unconditional `1/2` bound and the `ε` bound follow in a few lines each. -/

/-- **On a cell box the rounded model differs from `M` exactly on the minority tuples**, so its
edit count is at most `min d (1 - d)` times the box mass, where `d` is the density of the symbol
on that box. Hypothesis-free: nonemptiness of the cells is derived internally from
`Finpartition.nonempty_of_mem_parts`. -/
theorem editDistance_majorityRound_le_min (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ}
    (S : L.Relations n) (C : Fin n → P.parts) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S)
        (fun i ↦ (C i : Finset V)) : ℝ)
      ≤ min (tupleDensity (M.Holds S) (fun i ↦ (C i : Finset V)))
            (1 - tupleDensity (M.Holds S) (fun i ↦ (C i : Finset V)))
        * ∏ i, ((C i : Finset V).card : ℝ) := by
  classical
  set box : Fin n → Finset V := fun i ↦ (C i : Finset V) with hboxdef
  have hne : ∀ i, (box i).Nonempty := fun i ↦ P.nonempty_of_mem_parts (C i).2
  have hcard : ((Fintype.piFinset box).card : ℝ) = ∏ i, ((box i).card : ℝ) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
  have hpos : (0 : ℝ) < ∏ i, ((box i).card : ℝ) :=
    Finset.prod_pos fun i _ ↦ by exact_mod_cast Finset.card_pos.mpr (hne i)
  have hboxpos : 0 < (Fintype.piFinset box).card := by
    rw [← Nat.cast_pos (α := ℝ), hcard]; exact hpos
  -- Every tuple of the box has the box itself as its cell tuple, so rounding is constant on it.
  have hcell : ∀ x ∈ Fintype.piFinset box, (fun i ↦ P.part (x i)) = box := by
    intro x hx
    exact funext fun i ↦ P.part_eq_of_mem (C i).2 (Fintype.mem_piFinset.mp hx i)
  set thr : Prop := (Fintype.piFinset box).card ≤ 2 * tupleCount (M.Holds S) box with hthrdef
  have hconst : ∀ x ∈ Fintype.piFinset box, ((M.majorityRound P).Holds S x ↔ thr) := by
    intro x hx
    rw [majorityRound_holds_iff, hcell x hx]
  -- The density threshold and the ℕ threshold agree.
  have hdthr : (1 : ℝ) / 2 ≤ tupleDensity (M.Holds S) box ↔ thr := by
    rw [tupleDensity_eq_count_div, le_div_iff₀ (by exact_mod_cast hboxpos), hthrdef]
    constructor
    · intro h
      have hle : ((Fintype.piFinset box).card : ℝ) ≤ 2 * (tupleCount (M.Holds S) box : ℝ) := by
        linarith
      exact_mod_cast hle
    · intro h
      have hle : ((Fintype.piFinset box).card : ℝ) ≤ 2 * (tupleCount (M.Holds S) box : ℝ) := by
        exact_mod_cast h
      linarith
  have hdsum : tupleDensity (M.Holds S) box
      + tupleDensity (fun x ↦ ¬ M.Holds S x) box = 1 := tupleDensity_add_neg hne
  by_cases hthr : thr
  · -- Rounded to constantly TRUE on the box: the edits are the tuples where `M` fails.
    have hdhalf : (1 : ℝ) / 2 ≤ tupleDensity (M.Holds S) box := hdthr.mpr hthr
    rw [min_eq_right (by linarith : 1 - tupleDensity (M.Holds S) box
      ≤ tupleDensity (M.Holds S) box)]
    rw [show editDistance (M.Holds S) ((M.majorityRound P).Holds S) box
        = tupleCount (fun x ↦ ¬ M.Holds S x) box from
      congrArg Finset.card (Finset.filter_congr fun x hx ↦ by simp [(hconst x hx).mpr hthr])]
    exact card_filter_le_of_tupleDensity_le
      (show tupleDensity (fun x ↦ ¬ M.Holds S x) box ≤ 1 - tupleDensity (M.Holds S) box from
        by linarith)
  · -- Rounded to constantly FALSE on the box: the edits are the tuples where `M` holds.
    have hdhalf : tupleDensity (M.Holds S) box < 1 / 2 := by
      by_contra hcon
      exact hthr (hdthr.mp (not_lt.mp hcon))
    rw [min_eq_left (by linarith : tupleDensity (M.Holds S) box
      ≤ 1 - tupleDensity (M.Holds S) box)]
    rw [show editDistance (M.Holds S) ((M.majorityRound P).Holds S) box
        = tupleCount (M.Holds S) box from
      congrArg Finset.card (Finset.filter_congr fun x hx ↦ by
        simp [show ¬ ((M.majorityRound P).Holds S x) from fun hh ↦ hthr ((hconst x hx).mp hh)])]
    exact card_filter_le_of_tupleDensity_le le_rfl

/-! ### The two consequences of the box lemma -/

/-- **The unconditional half bound.** A density and its complement cannot both exceed `1/2`, so
majority rounding is within `1/2` of `M` on every cell box, over every partition, with no
homogeneity, extraction, or stability input. -/
theorem cellwiseEditBound_majorityRound_half (M : FiniteRelModel L V) (P : Finpartition s) :
    CellwiseEditBound M (M.majorityRound P) P (1 / 2) := by
  intro n hn S C
  refine (editDistance_majorityRound_le_min M P S C).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))
  rcases le_or_gt (tupleDensity (M.Holds S) (fun i ↦ (C i : Finset V))) (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- **The `ε` form.** Cell homogeneity at every positive arity bounds the rounding error by `ε`:
each disjunct of the homogeneity disjunction bounds one of the two arguments of the `min`. -/
theorem cellwiseEditBound_majorityRound_of_isHomogeneousCell (M : FiniteRelModel L V)
    (P : Finpartition s) {ε : ℝ}
    (hhom : ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → P.parts),
      IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε) :
    CellwiseEditBound M (M.majorityRound P) P ε := by
  classical
  intro n hn S C
  refine (editDistance_majorityRound_le_min M P S C).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _))
  have h := hhom n hn S C
  rw [isHomogeneousCell_def] at h
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-! ### The generic rounding theorem -/

/-- **Cell homogeneity yields an indivisible approximation.** Stability-free and
arbitrary-arity: if every box of cells is `ε`-homogeneous for every positive-arity symbol, then
some model is indivisible for `P`, agrees with `M` on the nullary data exactly, and is within
`ε` of `M` on every cell box.

The witness is `M.majorityRound P`; consumers who want it explicitly can use
`majorityRound_isIndivisibleFor`, `nullaryCompatible_majorityRound`, and
`cellwiseEditBound_majorityRound_of_isHomogeneousCell` directly. No uniqueness is claimed. -/
theorem exists_isIndivisibleFor_of_isHomogeneousCell (M : FiniteRelModel L V)
    (P : Finpartition s) {ε : ℝ}
    (hhom : ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → P.parts),
      IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε) :
    ∃ N : FiniteRelModel L V,
      N.IsIndivisibleFor P ∧ NullaryCompatible M N ∧ CellwiseEditBound M N P ε :=
  ⟨M.majorityRound P, majorityRound_isIndivisibleFor M P, nullaryCompatible_majorityRound M P,
    cellwiseEditBound_majorityRound_of_isHomogeneousCell M P hhom⟩

/-! ### The converse, at exactly the same tolerance -/

/-- **The exact converse.** If `N` is indivisible for `P` and cellwise `ε`-close to `M`, then
every cell box is `ε`-homogeneous for `M`. There is no side condition and no tolerance loss: `N`
is constant on each cell box, so the edits there are exactly the tuples on one side of `M`, and
the edit bound *is* a density bound.

Note the arity guard: this recovers homogeneity at positive arity. At arity `0` the cell is
`0`-homogeneous outright (`isHomogeneousCell_of_isEmpty_index`), so a consumer needing all
arities dispatches on `n` rather than applying this lemma alone. -/
theorem isHomogeneousCell_of_cellwiseEditBound {M N : FiniteRelModel L V}
    {P : Finpartition s} {ε : ℝ} (hN : N.IsIndivisibleFor P)
    (hedit : CellwiseEditBound M N P ε) {n : ℕ} (hn : 0 < n) (S : L.Relations n)
    (C : Fin n → P.parts) :
    IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε := by
  classical
  set box : Fin n → Finset V := fun i ↦ (C i : Finset V) with hboxdef
  have hne : ∀ i, (box i).Nonempty := fun i ↦ P.nonempty_of_mem_parts (C i).2
  have hcard : ((Fintype.piFinset box).card : ℝ) = ∏ i, ((box i).card : ℝ) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
  have hpos : (0 : ℝ) < ∏ i, ((box i).card : ℝ) :=
    Finset.prod_pos fun i _ ↦ by exact_mod_cast Finset.card_pos.mpr (hne i)
  obtain ⟨x₀, hx₀⟩ : (Fintype.piFinset box).Nonempty := Fintype.piFinset_nonempty.mpr hne
  have hconst : ∀ x ∈ Fintype.piFinset box, (N.Holds S x ↔ N.Holds S x₀) := fun x hx ↦
    (hN n S).const_on_cellBox (fun i ↦ (C i).2) hx hx₀
  have hbound := hedit n hn S C
  rw [isHomogeneousCell_def]
  by_cases h0 : N.Holds S x₀
  · -- `N` is constantly true on the box: the edits are exactly the tuples where `M` fails.
    right
    rw [show editDistance (M.Holds S) (N.Holds S) box = tupleCount (fun x ↦ ¬ M.Holds S x) box
      from congrArg Finset.card
        (Finset.filter_congr fun x hx ↦ by simp [(hconst x hx).mpr h0])] at hbound
    have hd : tupleDensity (fun x ↦ ¬ M.Holds S x) box ≤ ε := by
      rw [tupleDensity_eq_count_div, hcard, div_le_iff₀ hpos]
      linarith
    rw [tupleDensity_neg hne] at hd
    linarith
  · -- `N` is constantly false on the box: the edits are exactly the tuples where `M` holds.
    left
    rw [show editDistance (M.Holds S) (N.Holds S) box = tupleCount (M.Holds S) box from
      congrArg Finset.card (Finset.filter_congr fun x hx ↦ by
        simp [show ¬ N.Holds S x from fun hh ↦ h0 ((hconst x hx).mp hh)])] at hbound
    rw [tupleDensity_eq_count_div, hcard, div_le_iff₀ hpos]
    linarith

/-! ### Tests and adversarial examples -/

section Tests

-- **The off-support convention, pinned.** A tuple with an entry outside `s` has an empty cell
-- box, so the ℕ threshold reads `0 ≤ 2 * 0` and the rounded model holds of it. This is the tie
-- convention of `majorityRound`, not a statement about `M`; a consumer wanting "false off
-- support" must impose it separately.
example (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ} (S : L.Relations n)
    (x : Fin n → V) (i : Fin n) (hi : x i ∉ s) : (M.majorityRound P).Holds S x := by
  rw [majorityRound_holds_iff]
  have hzero : (Fintype.piFinset fun j ↦ P.part (x j)).card = 0 := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [P.part_eq_empty.mpr hi, Finset.card_empty])
  have hle := tupleCount_le_card (R := M.Holds S) (A := fun j ↦ P.part (x j))
  omega

-- The same convention concretely: over a partition of the **empty** ground set no vertex is on
-- support, so the rounded model holds of every tuple, whatever `M` is.
example (M : FiniteRelModel (singleRelLang 1) (Fin 3)) (x : Fin 1 → Fin 3) :
    (M.majorityRound (⊥ : Finpartition (∅ : Finset (Fin 3)))).Holds (singleRelSymbol 1) x := by
  rw [majorityRound_holds_iff]
  have hpart : ∀ a : Fin 3, (⊥ : Finpartition (∅ : Finset (Fin 3))).part a = ∅ := fun _ ↦
    (⊥ : Finpartition (∅ : Finset (Fin 3))).part_eq_empty.mpr (by simp)
  simp [hpart, tupleCount]

-- **Arity zero is a separate clause.** `CellwiseEditBound` says nothing at `n = 0` by design;
-- the exact arity-zero statement is `NullaryCompatible`, which rounding preserves.
example (M : FiniteRelModel L V) (P : Finpartition s) :
    NullaryCompatible M (M.majorityRound P) :=
  nullaryCompatible_majorityRound M P

-- **The indiscrete partition.** `⊤` has a single cell, so rounding is one global majority vote,
-- and the half bound still holds — with no homogeneity or stability input.
example (M : FiniteRelModel L V) :
    CellwiseEditBound M (M.majorityRound (⊤ : Finpartition s)) (⊤ : Finpartition s) (1 / 2) :=
  cellwiseEditBound_majorityRound_half M ⊤

-- **The discrete partition.** Indivisibility for `⊥` is free anyway (`isIndivisible_bot`), so
-- at `⊥` all the content of the triple sits in the edit clause.
example (M : FiniteRelModel L V) :
    (M.majorityRound (⊥ : Finpartition s)).IsIndivisibleFor (⊥ : Finpartition s) :=
  majorityRound_isIndivisibleFor M ⊥

-- …and there rounding is exact: every cell is a singleton, so each cell box holds one tuple,
-- its density is `0` or `1`, and the edit bound holds at `ε = 0`.
example (M : FiniteRelModel L V) :
    CellwiseEditBound M (M.majorityRound (⊥ : Finpartition s)) (⊥ : Finpartition s) 0 := by
  classical
  refine cellwiseEditBound_majorityRound_of_isHomogeneousCell M ⊥ fun n hn S C ↦ ?_
  rw [isHomogeneousCell_def]
  have hbox : (Fintype.piFinset fun i ↦ (C i : Finset V)).card = 1 := by
    rw [Fintype.card_piFinset]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    obtain ⟨a, -, ha⟩ := Finpartition.mem_bot_iff.mp (C i).2
    rw [← ha, Finset.card_singleton]
  rcases Nat.lt_or_ge (tupleCount (M.Holds S) fun i ↦ (C i : Finset V)) 1 with h | h
  · left
    rw [tupleDensity_eq_count_div, Nat.lt_one_iff.mp h]
    simp
  · right
    rw [tupleDensity_eq_count_div, le_antisymm (hbox ▸ tupleCount_le_card) h, hbox]
    norm_num

-- **Adversarial: an empty ground set (hence also an empty carrier) and a negative tolerance.**
-- A partition of `∅` has no cells, so at positive arity there is no tuple of cells and the
-- predicate is vacuously true — even at `ε < 0`. Nothing is claimed about `M` and `N` there.
example (M N : FiniteRelModel L V) :
    CellwiseEditBound M N (⊥ : Finpartition (∅ : Finset V)) (-1) := by
  intro n hn S C
  exact absurd (C ⟨0, hn⟩).2 (by simp)

-- **Adversarial: vacuity at `ε = 1`.** Any two models are cellwise `1`-close, so a consumer
-- reading a `CellwiseEditBound` at tolerance `1` or above learns nothing.
example (M N : FiniteRelModel L V) (P : Finpartition s) : CellwiseEditBound M N P 1 :=
  cellwiseEditBound_of_one_le M N P le_rfl

-- Tolerance monotonicity, on the rounding witness.
example (M : FiniteRelModel L V) (P : Finpartition s) :
    CellwiseEditBound M (M.majorityRound P) P (3 / 4) :=
  (cellwiseEditBound_majorityRound_half M P).mono (by norm_num)

-- The metric laws, statement-level.
example (M N : FiniteRelModel L V) (P : Finpartition s) (h : CellwiseEditBound M N P (1 / 3)) :
    CellwiseEditBound N M P (1 / 3) :=
  h.symm

example (M N N' : FiniteRelModel L V) (P : Finpartition s) {ε₁ ε₂ : ℝ}
    (h₁ : CellwiseEditBound M N P ε₁) (h₂ : CellwiseEditBound N N' P ε₂) :
    CellwiseEditBound M N' P (ε₁ + ε₂) :=
  h₁.trans h₂

-- **Round trip at exactly `ε`.** Rounding and then reading homogeneity back off the edit bound
-- loses no tolerance: the two directions compose to the identity on `ε`.
example (M : FiniteRelModel L V) (P : Finpartition s) {ε : ℝ}
    (hhom : ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → P.parts),
      IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε)
    {n : ℕ} (hn : 0 < n) (S : L.Relations n) (C : Fin n → P.parts) :
    IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε :=
  isHomogeneousCell_of_cellwiseEditBound (majorityRound_isIndivisibleFor M P)
    (cellwiseEditBound_majorityRound_of_isHomogeneousCell M P hhom) hn S C

/-! #### INTENTIONAL NON-LEMMA: no refinement monotonicity at fixed `ε`

`IsIndivisible.mono_of_le` passes **exact** indivisibility to any finer partition. The
approximate clause does **not** behave that way at a fixed tolerance: a refined cell is smaller,
so the budget `ε * ∏ |cell|` shrinks while the edits can stay where they are. The four
`decide`/`norm_num` checks below are the witness, stated at the box level (relations rather than
models, to keep them kernel-decidable): with `R₁ x ↔ x 0 = 0`, `R₂` constantly false and
`ε = 1/2`, the coarse box `univ` satisfies the bound and the refined box `{0}` does not. So no
lemma of the form `CellwiseEditBound M N P ε → Q ≤ P → CellwiseEditBound M N Q ε` may be added;
this is the exact-versus-approximate asymmetry already recorded one layer up for goodness. -/

example : editDistance (fun x : Fin 1 → Fin 2 ↦ x 0 = 0) (fun _ ↦ False)
    (fun _ ↦ (Finset.univ : Finset (Fin 2))) = 1 := by decide

example : editDistance (fun x : Fin 1 → Fin 2 ↦ x 0 = 0) (fun _ ↦ False)
    (fun _ ↦ ({0} : Finset (Fin 2))) = 1 := by decide

-- Coarse box: `1 ≤ (1/2) * 2` holds …
example :
    ((1 : ℕ) : ℝ) ≤ (1 / 2) * ∏ _i : Fin 1, ((Finset.univ : Finset (Fin 2)).card : ℝ) := by
  norm_num

-- … refined box: `1 ≤ (1/2) * 1` fails.
example :
    ¬ (((1 : ℕ) : ℝ) ≤ (1 / 2) * ∏ _i : Fin 1, ((({0} : Finset (Fin 2))).card : ℝ)) := by
  norm_num

end Tests

end RegularityLemmata
