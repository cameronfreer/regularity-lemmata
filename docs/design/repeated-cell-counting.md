# Repeated-cell counting: specification of the extension to induced counting over a partition

**Status: specification for review. No theorem signature is frozen until this document is
approved; no Lean implementation accompanies it.** Companion to issue #181 (audit 5d) and to
`docs/design/approximation-to-counting.md`. Everything below is stated in this repository's
existing definitions and audit findings; where a choice remains open it is presented as a
choice, not resolved by an outside requirement.

## 0. Setting and existing definitions (unchanged)

Carrier `s : Finset V`, partition `Q : Finpartition s`, pattern `P : FiniteRelModel L W` with
`[Fintype W] [DecidableEq W]` (the counting theorems take `W = Fin k`), host model
`M : FiniteRelModel L V`.

- `inducedEmbeddingCountOn P M A` (`Relational/BinaryPattern.lean`): the number of
  **injective** `f ∈ Fintype.piFinset A` with `PreservesAndReflects P M f`, where
  `PreservesAndReflects P M f :↔ ∀ (R : RelSymbol L) (x : Fin (arity R) → W), P.Holds R x ↔ M.Holds R (f ∘ x)`
  (`Relational/PatternCounts.lean`). The quantification is over **all** argument tuples `x`,
  including those with repeated arguments and the nullary symbols (`arity R = 0`).
- `IsIndivisible Q R :↔ ∀ x y, (∀ i, x i ∈ s) → (∀ i, y i ∈ s) → (∀ i, Q.part (x i) = Q.part (y i)) → (R x ↔ R y)`
  and `N.IsIndivisibleFor Q` for every symbol (`Relational/Indivisible.lean`). The tuples `x, y`
  range over **all** tuples in `s`, repeated entries included: a tuple with `x i = x j` and a
  tuple with `x i ≠ x j` in the same cell are compared.
- `quotientRel Q R C :↔ ∃ x, (∀ i, x i ∈ C i) ∧ R x` for `C : Fin n → Q.parts`, arbitrary `C`
  (repeats allowed); `N.quotient Q : FiniteRelModel L Q.parts` interprets every symbol by it.
  Under indivisibility the existential equals the universal form
  (`IsIndivisible.quotientRel_iff_forall`).
- The transversal cell law `IsIndivisibleFor.inducedEmbeddingCountOn_cells`: for **injective**
  `C : W → Q.parts`,
  `inducedEmbeddingCountOn P N (fun i ↦ C i) = if PreservesAndReflects P (N.quotient Q) C then ∏ i, |C i| else 0`.
- `quotientInducedCount P N Q := ∑_{C injective, PreservesAndReflects P (N.quotient Q) C} ∏ i, |C i|`;
  `cellTupleVolume T := ∏ i, |T i|` for **every** `T : Fin k → Finset V` (`Relational/DiagonalGate.lean`).
- The composite transfer `abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_of_cellwiseEditBound`
  (`Relational/AggregationBridge.lean`): for `N.IsIndivisibleFor Q`, `NullaryCompatible M N`,
  `CellwiseEditBound M N Q ε`, and `∀ C ∈ Q.parts, |C| ≤ m`,
  `|count_M − quotientInducedCount P N Q| ≤ (∑_{R : arity r > 0} k^r · ε · |s|^r) · |s|^{k−1} + (k choose 2) · m · |s|^{k−1}`.

None of these is changed by this specification. `cellTupleVolume` and the transversal API are
preserved as they are.

## 1. The eligible injective placement count

For an **arbitrary** assignment `C : W → Q.parts` (repeats allowed), write `m_A(C) := |{i : W | C i = A}|`
for the number of pattern vertices assigned to the cell `A ∈ Q.parts`. Define

```
placementCount Q C : ℕ := ∏_{A ∈ Q.parts} (|A|)_{m_A(C)}          -- falling factorial
```

This counts the injective maps `f : W → V` with `f i ∈ C i` for every `i`: the cells are
pairwise disjoint, so `f` is injective if and only if it is injective on each fibre
`C⁻¹ {A}`, and an injective map of an `m`-element fibre into `A` is one of `(|A|)_m`. It counts
**eligible injections**, not pattern realizations.

Elementary laws to be proved with it:

- **Transversal specialization.** If `C` is injective then every `m_A(C) ≤ 1` and
  `placementCount Q C = ∏ i, |C i| = cellTupleVolume (fun i ↦ C i)`.
- **Insufficient capacity.** If some `m_A(C) > |A|` then `(|A|)_{m_A(C)} = 0` and
  `placementCount Q C = 0`; no injective placement exists.
- **Empty pattern.** For `W` empty the product is empty and `placementCount Q C = 1`.
- **Sum over all assignments.** `∑_{C : W → Q.parts} placementCount Q C = (|s|)_{|W|}`, the
  number of injective tuples in `s` (`card_injectiveTuplesOn`); this is the all-placement
  counterpart of `sum_cellTupleVolume_eq : ∑_T cellTupleVolume T = |s|^k`.

Proof route: the injective tuples of the box `fun i ↦ C i` are the product over cells of the
injective tuples of each fibre into its cell; the count of injective maps from a finite type of
size `m` into a finset of size `a` is `a.descFactorial m` (Mathlib's `Fintype.card_embedding_eq`,
already bridged in `Finite/Injective.lean` for the case `W → s`).

## 2. Exact relationship to induced counting under indivisibility

**Claim (general cell law).** For `N.IsIndivisibleFor Q` and **arbitrary** `C : W → Q.parts`,

```
inducedEmbeddingCountOn P N (fun i ↦ C i)
  = if PreservesAndReflects P (N.quotient Q) C then placementCount Q C else 0.
```

Why the agreement condition is the same one as in the transversal law, including repeated
relation arguments: let `f` be an injective map into the box, `R` a symbol of arity `r`, and
`x : Fin r → W` any argument tuple, possibly with repeated arguments. The host tuple `f ∘ x` lies
in `s` with cells `C ∘ x`. By indivisibility, `N.Holds R (f ∘ x)` depends only on the cell tuple
`C ∘ x`, whether or not `f ∘ x` has repeated entries (indivisibility compares a tuple with
repeated entries against one without, provided the cells agree). Hence
`N.Holds R (f ∘ x) ↔ quotientRel Q (N.Holds R) (C ∘ x) ↔ (N.quotient Q).Holds R (C ∘ x)`, and
therefore `PreservesAndReflects P N f ↔ PreservesAndReflects P (N.quotient Q) C`, a condition on
`C` alone. Every injective `f` into the box is then either counted or not, uniformly, which
gives the `if`.

Two points that the transversal law hides and the general law must state:

- **Repeated relation arguments.** For `C i = C j = A` with `i ≠ j` and a symbol with an
  argument tuple `x` using both `i` and `j`, the pattern asks `P.Holds R x` and the host
  answers with the cell's constant on the diagonal-free part of `A × A`, which by
  indivisibility equals its constant on the diagonal of `A` as well. So a pattern that relates
  `i` and `j` by `R` can only be realized in a cell where `R` holds throughout `A × A`
  (diagonal included), and never in a cell where `R` is constant false. The quotient value
  `(N.quotient Q).Holds R (C ∘ x)` is exactly this constant. No separate diagonal condition is
  needed **for `N`**; see §4 for what this does not settle about `M`.
- **Nullary symbols.** For `arity R = 0` the condition reads `P.Holds R ![] ↔ (N.quotient Q).Holds R ![]`,
  and `(N.quotient Q).Holds R ![] ↔ N.Holds R ![]` (`quotient_holds_zero`); it is the
  `NullaryCompatible P N` clause, independent of `C`, as in the transversal case.

**All-placement quotient count.** Define

```
quotientInducedCountAll P N Q : ℕ
  := ∑_{C : W → Q.parts} (if PreservesAndReflects P (N.quotient Q) C then placementCount Q C else 0).
```

**Claim (exactness).** For `N.IsIndivisibleFor Q`:
`inducedEmbeddingCountOn P N (fun _ ↦ s) = quotientInducedCountAll P N Q`, because the boxes
`fun i ↦ C i` over all `C` partition the tuples of `s^W` (this is
`inducedEmbeddingCountOn_eq_transversal_add_nontransversal` with the non-transversal part
evaluated instead of bounded). Its transversal part is the existing `quotientInducedCount`
(`sum_transversalCellTuples_eq_quotientInducedCount`), so

```
quotientInducedCountAll P N Q = quotientInducedCount P N Q + ∑_{C non-injective} [agreement] · placementCount Q C,
```

and the existing bound `|count_N − quotientInducedCount P N Q| ≤ (k choose 2)·m·|s|^{k−1}`
(`IsIndivisibleFor.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le`) is recovered
from `placementCount Q C ≤ cellTupleVolume (fun i ↦ C i)` and `sum_nontransversalCellTuples_weight_le`.

## 3. Endpoints and preserved API

- **Transversal specialization.** On injective `C` the general cell law is literally
  `inducedEmbeddingCountOn_cells`; `quotientInducedCountAll` restricted to injective `C` is
  `quotientInducedCount`. Both existing declarations stay, with their names and statements.
- **Empty pattern** (`W` empty, `k = 0`). There is one assignment `C`, the empty map;
  `placementCount = 1`; the agreement condition reduces to the nullary clause; the count is
  `1` or `0` accordingly, matching `inducedEmbeddingCountOn` on the empty box.
- **Insufficient cell capacity.** If `m_A(C) > |A|` for some `A`, the summand is `0` whatever
  the agreement; in particular for `|W| > |s|` every summand vanishes and both sides of the
  exactness claim are `0`.
- **Diagonal-charge alternative preserved.** Consumers that prefer the transversal count with
  the explicit charge `(k choose 2)·m·|s|^{k−1}` keep it unchanged; the new count is an
  additional, exact alternative for indivisible models.

## 4. What this removes from the error accounting, and what remains

Take the composite of §0 and replace `quotientInducedCount` by `quotientInducedCountAll`.

**Removed.** The placement collision charge `(k choose 2)·m·|s|^{k−1}` disappears entirely: the
count of `N` on the full box is evaluated exactly (§2), so the only remaining discrepancy is
between `M` and `N`.

**What remains, unchanged by this extension.** The edit-transfer term
`(∑_{R : arity r > 0} k^r · ε · |s|^r) · |s|^{k−1}`, from `abs_inducedEmbeddingCountOn_sub_le_editMass`
with `CellwiseEditBound.editDistance_const_le`. Relative to `|s|^k` this is
`∑_R k^r · ε · |s|^{r−1}`, which for a symbol of arity `r ≥ 2` **grows with the host**. Two
separate facts explain this, and neither is touched by repeated-cell counting:

1. The extension lemma `card_filter_comp_mem_le` charges every edited tuple `e` of arity `r`
   with `|s|^{k−1}` embeddings: it fixes one coordinate of `f` through `f ∘ x = e` and lets
   the other `k−1` range freely. For an argument tuple `x` with `j` distinct arguments, the
   equation `f ∘ x = e` fixes `j` coordinates, so the sharp count is `|s|^{k−j}`; the lemma
   uses the worst case `j = 1`, which is attained only when `x` is constant, that is, when
   `e` is a **diagonal** tuple `(v, …, v)`.
2. The cellwise edit bound controls the **density** of edits on each cell box, `≤ ε · ∏ |C i|`.
   It says nothing about how the edits distribute over the diagonal strata of the box. The
   review's obstruction shows the two facts combining: one binary symbol interpreted as
   equality on `n ≥ 3` vertices, one cell; the density is `1/n`, the majority rounding
   `N = M.majorityRound Q` is the empty relation; `CellwiseEditBound M N Q (1/n)` holds; every
   one of the `n` diagonal tuples is an edit; a one-vertex pattern requiring the symbol on its
   repeated argument has `n` embeddings in `M` and `0` in `N`; normalized discrepancy `1`
   while `ε = 1/n → 0`. No pattern vertex is repeated in a cell here; `placementCount` and
   `quotientInducedCountAll` are exact for `N` and do not help.

So eliminating the repeated-cell collision charge does not improve the edit-transfer
coefficient. A host-independent transfer for arbitrary patterns needs an **additional
hypothesis on the diagonal strata of the edit sets**, which this repository does not have; it
is identified here as the missing input, not specified:

- **Option A (stratified cellwise edit bound).** For every symbol of arity `r`, every cell box,
  and every equivalence relation `π` on `Fin r` (the repetition pattern), the edits among the
  tuples of repetition pattern exactly `π` number at most `ε` times the number of such tuples
  in the box. With this, the transfer lemma can be restated stratum by stratum
  (`|s|^{k−|π|}` embeddings per edit of pattern `π`, at most `ε · ∏ |C i|`-type many edits per
  stratum), giving a normalized error of the form `ε · ∑_R c(k, r)` with `c` depending on `k`
  and `r` only. The equality example violates Option A on the diagonal stratum (density `1`).
- **Option B (diagonal-free patterns).** Restrict the transfer to patterns whose symbols are
  never applied with repeated arguments, or to models where all symbols are diagonal-free
  (as the graph adapter is by looplessness); then only the stratum `j = r` occurs and the
  existing lemma sharpened to `|s|^{k−r}` gives a host-independent coefficient. This is a
  restriction of scope, not a new hypothesis on the edits.

Which of A or B (or both, as separate theorems) is wanted is the open choice; it is not
decided here, and nothing in this specification depends on it.

## 5. Proposed compiled consumer (an `example` that a transversal example cannot satisfy)

Under `examples/` or in the test section of the implementing module: the carrier `Fin 4`, the
indiscrete partition `Q = ⊤` on `s = univ` (one cell `A = univ`, `|A| = 4`), the language with
one binary symbol, the host `N` interpreting it as the **complete** relation (true on every
pair, diagonal included; indivisible for `Q`), and the pattern `P` on `Fin 2` with the symbol
true on all four argument tuples `(0,0), (0,1), (1,0), (1,1)`.

- Both pattern vertices are assigned to the single cell: the only assignment `C` has
  `m_A(C) = 2`, and `placementCount Q C = (4)_2 = 12`.
- `PreservesAndReflects P (N.quotient Q) C` holds (every quotient value is true), so the general
  cell law gives `12`, and `quotientInducedCountAll P N Q = 12`.
- `inducedEmbeddingCountOn P N (fun _ ↦ univ) = 12` by `decide` (the injective maps `Fin 2 → Fin 4`).
- The transversal count `quotientInducedCount P N Q = 0`: there is no injective `C : Fin 2 → Q.parts`
  into a one-part partition, so the existing API can only bound the discrepancy by the charge
  `(2 choose 2)·4·4 = 16`, while the new count is exact.

A second, negative instance pins the agreement condition on a repeated argument: the same
setting with `N` the **empty** relation and `P` requiring the symbol on `(0,1)` gives
`placementCount = 12` but agreement fails, so the count is `0`, matching `decide`.

Both instances have two distinct pattern vertices in one cell, so no transversal example
satisfies them; this is the acceptance test for the extension.

## 6. Proposed signatures (for review; not frozen)

```
def placementCount (Q : Finpartition s) (C : W → Q.parts) : ℕ
theorem placementCount_of_injective (hC : Function.Injective C) :
    placementCount Q C = ∏ i, ((C i : Finset V)).card
theorem placementCount_eq_zero_of_lt (hA : (A : Finset V).card < m_A C) : placementCount Q C = 0
theorem sum_placementCount (Q : Finpartition s) :
    ∑ C : W → Q.parts, placementCount Q C = s.card.descFactorial (Fintype.card W)
theorem IsIndivisibleFor.inducedEmbeddingCountOn_cells_general (h : N.IsIndivisibleFor Q)
    (P : FiniteRelModel L W) (C : W → Q.parts) :
    inducedEmbeddingCountOn P N (fun i ↦ (C i : Finset V))
      = if PreservesAndReflects P (N.quotient Q) C then placementCount Q C else 0
def quotientInducedCountAll (P : FiniteRelModel L W) (N : FiniteRelModel L V) (Q : Finpartition s) : ℕ
theorem IsIndivisibleFor.inducedEmbeddingCountOn_eq_quotientInducedCountAll (h : N.IsIndivisibleFor Q)
    (P : FiniteRelModel L (Fin k)) :
    inducedEmbeddingCountOn P N (fun _ ↦ s) = quotientInducedCountAll P N Q
theorem abs_inducedEmbeddingCountOn_sub_quotientInducedCountAll_le_of_cellwiseEditBound … :
    |count_M − quotientInducedCountAll P N Q|
      ≤ (∑_{R : arity r > 0} k^r · ε · |s|^r) · |s|^{k−1}      -- no collision term
```

Placement: `placementCount` and its laws beside `injectiveTuplesOn` in `Finite/Injective.lean`
(it is partition combinatorics) or beside `quotientInducedCount` in `Relational/Indivisible.lean`
(it is stated on `Q.parts`); the choice is open and affects only imports. The general cell law
and `quotientInducedCountAll` go in `Relational/Indivisible.lean` next to their transversal
versions; the composite goes in `Relational/AggregationBridge.lean`.

## 7. Open choices presented, not resolved

1. Home of `placementCount` (§6).
2. Whether `quotientInducedCountAll` should carry the transversal count as a named summand
   (`quotientInducedCount + nontransversal part`) or be defined directly over all `C`.
3. The remaining input for a host-independent edit transfer: Option A or Option B of §4, or
   neither in this repository.
