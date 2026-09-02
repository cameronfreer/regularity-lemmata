# Design: generic approximation-to-counting and edit transfer

Work in progress. Nothing here is a theorem; theorems live in the library and their conventions
in [`ARCHITECTURE.md`](../../ARCHITECTURE.md). This document is the audit-and-freeze deliverable
for issue #84. It records what already exists, what each version actually proves, and the
interface decisions — **no implementation**.

The issue promises three user-facing interfaces, and this document freezes all three — the
**boxwise-constant quotient** with its exact counting relationship (§7), the **edit transfer**
between two models on one carrier (§8), and their **composite** (§9) — supported by the
**aggregation bridge** with its local-error hypothesis (§6). The coefficient audits behind §7 and §8 do *not* trigger the issue's
hard stop — both derivations are uniform in the arity — so no part of the three-part goal needs
to be split off; the hard stop fires only for the local uniformity coefficient (§1).

**Provenance.** This document introduces no new external antecedent. The counting and
exceptional-degree antecedents already cited in [`PROVENANCE.md`](../../PROVENANCE.md) for the
graph layer cover the specialized results audited here.

## 1. The headline finding: the hard stop fires, partially

Write `k` for the pattern's arity and `p(k) = k(k−1)/2` for its number of unordered coordinate
pairs. The arity-3 estimate carries an error of `(7ε + 3β)·#s³` and the diagonal gate a charge of
`3·m·|s|²`. The audit asks whether those constants have a uniform shape in `k`. The answer splits:

| Constant | Arity-`k` form | Status |
| --- | --- | --- |
| Diagonal charge `3·m·|s|²` | `p(k) · m · |s|^(k−1)` | **uniform**; derivation sound, see §4 |
| Bad-pair charge `3β` | `p(k) · β` | **conditionally uniform**, once the positional lift of §4a is proved; unproved today |
| Uniformity charge `7ε` | — | **no uniform closed form found**; see below |

**The `7` is not a product-perturbation constant.** It would be tempting to read it as
`2³ − 1` from a three-factor perturbation, and an earlier draft of this document did exactly
that. It is wrong. Tracing the constant through the source:

- `abs_directedTriangleCount_sub_le` (`Graph/TriangleCounting`) obtains `7ε` as `1ε + 6ε`: one
  `ε` from the apex-fibre step, which replaces the triangle count by a path count weighted by the
  third pair's density, and then
- `abs_directedPathCount_sub_le` (`Graph/PathCounting`) supplies `6ε`, itself `2ε + 4ε`: the `2`
  is a two-factor perturbation on good middle vertices, and the `4` is the two-sided exceptional
  mass of the two middle-degree tails, via `card_degreeExceptional_le`.

So the constant comes from a *nested fibre-plus-exceptional-degree recursion over the pattern's
structure*, not from a closed-form product bound. The library's actual three-factor perturbation
lemma, `abs_mul_mul_sub_mul_mul_le`, gives `|abc − a'b'c'| ≤ |a−a'| + |b−b'| + |c−c'|` — a linear
`3ε`, not `7ε` — and it is used for the density-shift charge in `BinaryStrongCounting`, not for
this coefficient at all.

At `k = 2` the coefficient is `1` and comes directly from `IsUniformPair`, with no fibre step and
no exceptional set. At `k = 3` it is `7` and requires both. **These are different shapes, not two
values of one formula**, which is precisely the condition the issue's hard stop names.

**Recommendation, per the hard stop: supply the local coefficient, do not compute it.** Do not
invent a uniform-looking constant. Precisely:

> The bridge is an **arity-parametric aggregation theorem with an arity-specific local-error
> hypothesis**. The library computes no function `C(k)`.

The theorem itself may quantify over `k` — what is fixed per application is the *local counting
estimate* and its coefficient, not the theorem's arity. The core bridge takes a **local error
budget** `δlocal` as a hypothesis, and arity-specific wrappers instantiate it: `δlocal = ε` at
`k = 2`, `δlocal = 7 * ε` at `k = 3`. That separates generic aggregation from the graph-specific
recursion that produces the `7`.

Two consequences, separable:

1. The **diagonal gate generalizes cleanly and should be generalized on its own merits**, whether
   or not the bridge is stated generically (§4). It is independent of the coefficient question.
2. The **aggregation is generic; only the local estimate is arity-specific** (§6).

What this document does **not** claim: that no uniform coefficient exists. Only that the audit
did not find one, and that the two available data points have structurally different derivations.
A recurrence in `k` may well exist — each additional coordinate plausibly contributes one fibre
step plus one exceptional-degree charge — but establishing that is research, not interface design,
and it must not be assumed by a frozen signature.

## 2. Audit table

What exists, and what each version actually proves.

| Statement | Arity | Normalization | Diagonal treatment | To become an instance |
| --- | --- | --- | --- | --- |
| `inducedEmbeddingCountOn_two` (`Relational/TwoVertexCounting`) | 2 | raw count on a box `![A, B]`; no normalization | avoided: `Disjoint A B` is a hypothesis | already the `k = 2` transversal case, and an **equality** to `pairCount` — no ε at all |
| `abs_inducedEmbeddingCountOn_three_sub_le` (`Relational/ThreeVertexCounting`) | 3 | raw count against a product of three `pairDensity`s times box volume; error `7ε·|A||B||C|` | avoided: pairwise `Disjoint` on all three | the pointwise `k = 3` transversal case; delegates to `abs_binaryPaletteTriangleCount_sub_le` |
| `abs_directedTriangleCount_sub_le` (`Graph/TriangleCounting`) | 3 | `7ε·|A||B||C|` | — | **where the `7` is produced**: `1ε` apex fibre + `6ε` path |
| `abs_directedPathCount_sub_le` (`Graph/PathCounting`) | 3 (as a 2-step path) | `6ε·|A||B||C|` | — | `6 = 2 + 4`: two-factor perturbation on good middles, plus two-sided exceptional-degree mass |
| `abs_representativeInducedCount_sub_estimate_le` (`Relational/GenericTripleEstimate`) | 3 | count against estimate; error `(7ε + 3β)·#s³` | transversal cell-triples only; distinctness from `transversalCellTriples_ne` | **closest existing relative** — already generic in the bad-pair set `D` and the box map `g`; specialized only by arity 3 and the binary palette |
| `sum_nontransversal_weight_le` (`Relational/DiagonalGate`) | 3 (`Fin 3` index) | any real weight dominated by `cellTripleVolume`; bound `3·m·|s|²` | **is** the diagonal charge | generalize `not_injective_fin_three` to `p(k)` collision events — see §4 |
| `card_nonInjectiveMaps_le` (`Finite/Injective`) | any `n` | `|ι|² · |β|^(|ι|−1)` | the collision bound | **already arity-generic**; a coarser cousin of the diagonal gate, over the carrier rather than over cell tuples |
| `abs_mul_mul_sub_mul_mul_le` (`Finite/Inequalities`) | 3 factors | `|a−a'|+|b−b'|+|c−c'|` under `|·| ≤ 1` | — | the genuine product-perturbation lemma; used for the **density-shift** charge, not the uniformity charge |
| `BinaryPaletteStrongWitness.abs_transversalInducedCount_sub_coarseInducedEstimate_le` (`Relational/BinaryStrongCounting`) | 3 | `(10τ + 3η + 3δ/η²)·|s|³` | transversal | witness- and palette-specific; a **consumer** of the bridge, not an instance |
| `relationCount` / `relationDensity` (`Relational/Counts`) | any `n` | all tuples, `/ |V|^n` | diagonals **included** | the all-tuple normalization |
| `injectiveRelationCount` / `injectiveRelationDensity` (`Relational/Counts`) | any `n` | injective tuples, `/ (|V|)_n` | injective by construction | the injective normalization |
| `relationEditCount`, `aggregateEditCount`, `relativeAggregateEdit` (`Relational/Edit`) | per symbol | `/ |V|^arity`; aggregate `/ Σ_s |V|^arity(s)`, every symbol–tuple incidence weight one | diagonals included; `injectiveRelationEditCount` is the separate injective form | the **input** to edit transfer; **no theorem transfers a pattern count across an edit today** — §8 is designed from scratch |
| `quotientRel`, `IsIndivisibleFor` (`Relational/Indivisible`) | any `n` | — | — | the quotient's per-relation core; agreement round-trips proved (`quotientRel_iff`, `quotientRel_part`, `quotientRel_iff_forall`), but **no packaged model on `P.parts` is ever constructed** — §7 |
| `majorityRound`, `CellwiseEditBound` (`Relational/CellwiseEdit`) | every positive `n` | per cell box, guard-free relative form | arity-0 exempt by `nullaryCompatible_majorityRound` | produces the indivisible approximant and its edit bound; the composite's first leg (§9) |
| `homCount`, `copyCount`, `inducedCopyCount` (`Hypergraph/Copies`) | `r`-uniform | raw counts | `copyCount`/`inducedCopyCount` injective; `homCount` not | adapter target via `Relational/HypergraphAdapters` |
| `ofUniformHypergraph`, `ofColoredHypergraph` (`Relational/HypergraphAdapters`) | `r` | count chain to `r!·#edges` | **every non-injective tuple false by construction** | makes the two normalizations agree on the hypergraph side |
| `Graph/StrongTypicality` | — | mass-based | — | the layer a counting consumer sits on; not an instance |

Three observations the table makes visible:

- **Every existing transversal result avoids diagonals by hypothesis, not by charge.** Disjointness
  is assumed pointwise at arity 2 and 3; the diagonal is charged separately and exactly once, in
  `DiagonalGate`. The bridge should keep that separation.
- **The library already has two arity-generic diagonal bounds** — `card_nonInjectiveMaps_le` over
  the carrier, `sum_nontransversal_weight_le` over cell tuples — and they are unconnected. Relating
  them is optional but a cheap consistency check.
- **The uniformity coefficient is produced two layers below the counting statement**, in
  `Graph/PathCounting` and `Graph/TriangleCounting`. Any attempt at a uniform-in-`k` coefficient
  must go through those, not through the relational layer.

## 3. Decision: normalization

**Primitive: ordered injective tuples, normalized by the falling factorial of the carrier being
counted — `(|s|)_k` for the `s`-restricted statements, since their injective tuples are drawn
from `s`.**

- It is what the pattern-count layer already does: `inducedEmbeddingCount` and
  `inducedEmbeddingCountOn` both filter on `Function.Injective`, so an all-tuple primitive would
  disagree with every existing consumer.
- Under it the diagonal contributes nothing, so the transfer coefficient cannot silently absorb a
  diagonal term.
- `injectiveRelationDensity` already commits to the falling factorial (its docstring says "never
  by `|V|^n`") — that is the full-carrier convention `(|V|)_k`, which the restricted form
  recovers at `s = univ`, where `(|s|)_k` rewrites to `(|V|)_k`.

**The conversion must be proved, not left to consumers.** Both halves exist:
`injectiveTupleCount_add_card_nonInjectiveMaps` (exact split) and `card_nonInjectiveMaps_le` with
`nonInjectiveMaps_ratio_le` (the bound). The bridge should export the conversion with a stated
error so a consumer wanting `#s^k` (or, at `s = univ`, `|V|^k`) normalization is not guessing.

### 3a. Two levels, stated separately

Choosing a normalized primitive does **not** mean the aggregation theorem should divide. The
bridge is exposed at two levels, and §6's displayed statement is the first of them:

* a **denominator-free raw theorem**, comparing the injective *count* to the estimate, with the
  error in units of `#s^k` — no division anywhere, so signed weights and degenerate carriers need
  no guard;
* a **normalized corollary**, dividing through by the falling factorial `(|s|)_k` to obtain the
  density form. At `s = univ` this rewrites to `(|V|)_k`, recovering the existing full-carrier
  convention.

**The `|s| < k` endpoint.** When `|s| < k` there are no injective `k`-tuples through `s`, so the
count is `0` and `(|s|)_k = 0`. Under the library's guard-free `x / 0 = 0` convention both sides
of the normalized corollary are `0`, and the inequality holds — so **the corollary needs no
positivity hypothesis**, exactly as `boxDensity_le_one` needs none. This is worth stating
explicitly, because the natural instinct is to guard it.

**Where positivity is genuinely needed** is the *converse* direction: recovering a count bound
from a density bound requires multiplying by `(|s|)_k`, which is informative only when that is
nonzero. `injectiveTupleCount_pos_of_le` supplies it from `k ≤ |s|`. The interface should place
that hypothesis on the inversion lemma alone, never on the corollary.

## 4. Decision: the diagonal and repeated coordinates

**Generalize the diagonal gate; do not replace it. This is worth doing independently of §1.**

`sum_nontransversal_weight_le` is already the right shape — it constrains *any* real weight
dominated by the cell-tuple volume, which is why it serves the actual and predicted sides alike.
The only arity-3-specific ingredient is `not_injective_fin_three`.

The generalization is one lemma — a map `T : Fin k → α` fails to be injective exactly when
`T i = T j` for some `i < j` — followed by the same union bound over `p(k)` events, each
contributing at most `m · |s|^(k−1)`. Unlike the uniformity coefficient, this derivation is
uniform in `k` with nothing hidden.

### 4a. The positional lift of the bad-pair mass

The `p(k)·β` term is **not** free, and its semantics must be stated exactly, because there are
two readings and conflating them multiplies by `p(k)` twice.

**The hypothesis is one already-aggregated bound, not a per-pair family.** In the arity-3
instance the hypothesis is `hmass : Σ_{(A,B) ∈ D} |A|·|B| ≤ β·#s²` — a single bound on the total
*cell-pair* mass of the bad set `D`. There is no per-pair hypothesis and no union bound over
hypothesis instances.

**The `p(k)` is a positional lift, not a hypothesis union bound.** What turns pair mass into
`k`-tuple mass is: a cell `k`-tuple is bad when *some coordinate-pair position* `i < j` lands in
`D`, so its volume is charged to that position; each of the `p(k)` positions carries at most
(mass of `D`) `· #s^(k−2)` from the `k − 2` free coordinates, giving `p(k) · (β·#s²) · #s^(k−2)
= p(k)·β·#s^k`. `badTripleVolume_le` is recovered at `k = 3` by restricting to transversal
tuples, with `p(3) = 3`. The
generic lemma to prove is exactly this positional lift; its `p(k)` index set is the same `i < j`
family as the diagonal gate's collision events, and it should reuse that characterization.

Two consequences for the frozen signature:

* `hbad` in §6 is the aggregated form, in units of `#s²`, matching `hmass` verbatim. Under that
  reading the conclusion's `p(k)·β·#s^k` is correct and the lift is the only missing lemma.
* A consumer holding *per-pair* bounds (`∀ i < j`, the `(i,j)`-bad mass `≤ β'·#s²`) first sums
  them into the aggregated form — at cost `D`'s mass `≤ p(k)·β'·#s²` if the per-pair sets are
  charged separately — and only then applies the lift. Applying a `p(k)` factor at *both* steps
  would be wrong; the bridge therefore takes only the aggregated hypothesis and leaves any
  per-pair-to-aggregate summation to the consumer, where its cost is visible.

Until the positional lift is proved, the `β` coefficient is a supplied parameter like `δlocal`.

**Patterns may repeat a vertex, but that is a different question and is out of scope.**
`inducedEmbeddingCountOn` counts injective maps from the pattern's vertex type, so a pattern with
a repeated vertex is not expressible. Whether to admit non-injective pattern maps is a separate
interface question; this bridge counts embeddings and leaves homomorphism counting to a later
issue. The audit found no existing result needing it.

## 5. Decisions: the remaining three

**Relations or models: models primitive, relations derived.** The counting layer is already stated
for `FiniteRelModel L V` against a pattern `FiniteRelModel L W`, and `PreservesAndReflects` is what
makes the count induced. A relation-only form is recoverable through `singleRelLang`, which
`ofUniformHypergraph` already uses. Stating the bridge for relations first would force a second
pattern notion.

**Boxwise constant: a hypothesis on the model, plus a constructed quotient with an agreement
theorem — in that order.** The hypothesis form is what the existing estimates consume
(`hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0` and relatives), so it must
exist. The quotient object is what makes "approximation yields counting" a composite rather than a
restatement; `Relational/CellwiseEdit`'s `majorityRound` is the existing precedent for constructing
such an object with an agreement theorem (`majorityRound_isIndivisibleFor`,
`editDistance_majorityRound_eq_min`). Freezing only the hypothesis form leaves the composite
unstateable. The quotient interface itself is frozen in §7.

**Edit mass: ordered, matching `Relational/Edit`, and the `k!` conversion stays out of the core.**
That file already froze the cross-arity weighting — every symbol–tuple incidence weight one,
aggregate budget `Σ_s |V|^arity(s)`, guard-free relative edit, explicitly *not* normalized by
`|V|^arityBound` and *not* averaged across symbols. Reopening it would fork the edit calculus.

The ordered-to-unordered factor `k!` is **not** a generic fact about relational models. It is
valid for symmetric, irreflexive, uniform-hypergraph-shaped relations, which is exactly the
setting where `ofUniformHypergraph` already proves
`injectiveRelationCount = … = r!·#edges`. A general `FiniteRelModel L` has no such symmetry, so
stating the conversion in the core bridge would assert something false of most models.

Therefore: **the core bridge carries ordered edit mass only**, and the `k!` conversion is supplied
solely through `Relational/HypergraphAdapters`, under that adapter's structural hypotheses. The
triadic layer's factor-six normalization is the `r = 3` instance of the adapter's conversion, not
of a generic one.

## 6. Proposed interface shape

Generic aggregation, arity-specific local estimate. The theorem quantifies over `k`; the
coefficient does not come from a formula.

### The core: a raw, denominator-free aggregation

```
bridgeRaw (k : ℕ) (δlocal β : ℝ)
  (hlocal  : <the local box estimate holds with error δlocal on each transversal cell tuple>)
  (hbad    : <TOTAL cell-pair mass of the bad set D ≤ β · #s ^ 2>)   -- already aggregated; §4a
  (hdiag   : ∀ C ∈ Q.parts, C.card ≤ m)
  … : |injectiveCount − estimate| ≤ (δlocal + p k · β) · #s ^ k + p k · m · |s| ^ (k − 1)
```

* `δlocal` is **supplied**, never computed. §1.
* `hbad` is the **single aggregated** bound on the bad set's total cell-pair mass, exactly as
  the arity-3 `hmass` is — **not** a per-pair family. The conclusion's `p k` factor is the
  positional lift of §4a, not a union bound over per-pair hypotheses; a consumer with per-pair
  bounds sums them *before* supplying `hbad`, and applying `p k` at both steps would be wrong.
* `p k · β` is computed **only once §4a's positional lift is proved**; until then `β`'s
  coefficient is supplied too.
* `p k · m · |s| ^ (k − 1)` is computed, from §4.
* No division appears, so this level is guard-free and signed-weight-safe.

### The wrappers

```
bridgeTwo   : instantiates δlocal := ε       -- from IsUniformPair directly
bridgeThree : instantiates δlocal := 7 * ε   -- from abs_directedTriangleCount_sub_le
```

Each wrapper's job is to discharge `hlocal` at its arity and nothing else. A later uniform `C(k)`,
if one is ever proved, would add a wrapper and change no existing signature.

### The normalized corollary

Divides `bridgeRaw` through by `(|s|)_k` — the injective tuples are drawn from `s`, so the
denominator is `s`'s falling factorial, rewriting to `(|V|)_k` at `s = univ`. Guard-free, no
positivity hypothesis; see §3a for the `|s| < k` endpoint and for where positivity is genuinely
required.

### What `hlocal` must not be

The local hypothesis is the load-bearing risk in this design. Stated carelessly it becomes *the
conclusion restated box by box*, at which point the bridge proves nothing and merely relabels its
input. `hlocal` must be a statement about a **single cell tuple** — a box estimate against a
product of pair densities, as `abs_inducedEmbeddingCountOn_three_sub_le` is — and the bridge's
content is the aggregation over cell tuples together with the bad-pair and diagonal accounting.
Any formulation of `hlocal` that already quantifies over the partition is disqualified.

### Language scope

Pairwise uniformity does not control arbitrary higher-arity relation symbols, and the audited
instance is binary-palette-specific. The first bridge must therefore be **abstract in a supplied
local box-counting estimate**, and must *not* claim that such an estimate follows for every
`FiniteRelModel L`. The binary-palette case is then one instantiation, not the general theory.

The alternative — stating the first bridge explicitly for binary relational models and pair
palettes — is sound but less reusable. The abstract form is preferred **provided** the previous
paragraph's constraint on `hlocal` is respected; without it, the abstract form is strictly worse,
because it hides the restriction instead of naming it.

### Implementation order

1. collision-event characterization (`not_injective_iff_exists_lt_eq` for `Fin k`);
2. generalized diagonal gate, `p(k) · m · |s|^(k−1)`;
3. positional lift of the bad-pair mass (§4a);
4. injective/all-tuple conversion (§3);
5. raw aggregation bridge;
6. normalized corollary;
7. arity-2 and arity-3 wrappers;
8. packaged quotient model with cellwise agreement (§7);
9. quotient counting theorem (§7);
10. edit-transfer theorem, with the nullary-agreement hypothesis (§8);
11. cellwise-to-aggregate edit conversion (§9);
12. composite theorem and its normalized corollary (§9).

Steps 1–2 are worth doing regardless of whether the bridge is ever built. Steps 8–10 are
mutually independent and independent of 3–7; step 12 needs 5, 9, and 10.

## 7. The quotient interface

The audit found the quotient's per-relation core already proved but never packaged.
`quotientRel P R : (Fin n → P.parts) → Prop` exists in `Relational/Indivisible` — the
choice-free existential form, "some tuple of representatives satisfies `R`" — together with both
agreement round-trips under indivisibility (`IsIndivisible.quotientRel_iff`,
`IsIndivisible.quotientRel_part`) and the existential/universal collapse
(`IsIndivisible.quotientRel_iff_forall`). What does **not** exist is a `FiniteRelModel L P.parts`
bundling them, and without it the composite of §9 has no object to count against.

**Construction.** `FiniteRelModel.quotient (N : FiniteRelModel L V) (P : Finpartition s) :
FiniteRelModel L P.parts`, interpreting each symbol by `quotientRel`. The definition asks for no
hypothesis — `quotientRel` is total — but its *theorems* require `N.IsIndivisibleFor P`; this
mirrors how `majorityRound` is defined unconditionally and acquires content under homogeneity.
Nullary symbols pass through unchanged (`quotientRel_zero` exists already).

**Cellwise agreement.** For indivisible `N`, the quotient's truth at a cell tuple equals `N`'s
truth at every tuple of representatives — this is `quotientRel_iff` verbatim, restated once at
the model level for each symbol. No new mathematics; the theorem is repackaging.

**Weighting of quotient cells.** Each cell is weighted by its cardinality, so a cell tuple
carries the product weight `Π_i |C i|` — the arity-`k` generalization of `cellTripleVolume`, and
precisely `boxMass`/`tupleWeight` from the `ProductSpaces` facade with weight `1` per vertex. No
normalized weighting is introduced at this level; densities enter only through §6's bridge.

**The exact counting relationship.** For `N` indivisible for `Q` and a pattern on `k` vertices,
the induced-embedding count on a *transversal* cell tuple is all-or-nothing: cells are disjoint,
so every tuple through distinct cells is automatically injective, and indivisibility makes the
induced condition constant on the box. Hence on each transversal cell tuple the count is either
`0` or exactly `Π_i |C i|`, according to whether the quotient model matches the pattern there:

> `transversalCount(N) = Σ over transversal cell tuples C matching the pattern in N.quotient of
> Π_i |C i|` — an **equality**, no ε.

**Repeated quotient cells and the diagonal gate.** An injective host tuple may well place two
distinct vertices in the *same* cell, so repeated-cell tuples are not excluded by injectivity —
they are exactly the nontransversal cell tuples. On such a box the injective count for an
indivisible model is a product of falling factorials grouped by cell multiplicity, **not**
`Π_i |C i|`, so no exact quotient formula is attempted there. Instead their entire contribution
is routed through the diagonal gate: their total volume is at most `p(k)·m·#s^(k−1)` (§4), the
charge §6's bridge already carries. So the count form is an inequality with the gate's charge as
its only error:

> `|inducedEmbeddingCountOn P N (fun _ ↦ s) − Σ_{transversal, matching} Π_i |C i||
> ≤ p(k)·m·#s^(k−1)`.

**Carrier scope.** `Q : Finpartition s` controls only tuples lying in `s`, so the left-hand side
is the **`s`-restricted count** `inducedEmbeddingCountOn … (fun _ ↦ s)` — the existing
restricted-count API — and *not* the full-carrier `inducedEmbeddingCount`, which counts over all
of `V`. Tuples using a vertex outside `s` appear in neither the quotient sum nor the diagonal
charge, so a full-count statement would simply be false for `s ≠ univ`. The full-carrier theorem
is the specialization `s = univ`; if a proper-subset/full-count comparison is ever needed, it
must carry an explicit off-`s` charge and is left out of this freeze.

This is why the quotient audit triggers no hard stop: the only constant involved is the diagonal
charge, whose uniform derivation §4 already established.

## 8. The edit-transfer interface

**No count-across-edit theorem exists in the library today**; this section designs one against
`Relational/Edit`'s frozen conventions. Setting: two models `M N : FiniteRelModel L V` on the
same carrier, a pattern on `k` vertices, ordered edit sets with diagonals included.

**The derivation, and its coefficient.** An injective `k`-tuple `T` through `s` is counted by
`M` but not by `N` only if some atom distinguishes them: there is a symbol `R` of arity `n` and
a pattern tuple `w : Fin n → W` on which the two models disagree at the host tuple `T ∘ w` — a
tuple lying in `s`, so the relevant edit mass is the **`s`-box edit count**
`editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s)`, not the full-carrier `relationEditCount`.
Induced counting reads *every* atom on the pattern's vertices — all `k^n` tuples per symbol, not
only the pattern's true atoms — so the double count runs over `Σ_R k^(arity R)` atomic
incidences. For `n ≥ 1`, fixing the edited host tuple pins `T` on at least one coordinate,
leaving at most `#s^(k−1)` extensions through `s`. Hence:

> `|inducedEmbeddingCountOn P M (fun _ ↦ s) − inducedEmbeddingCountOn P N (fun _ ↦ s)|
> ≤ Σ_R k^(arity R) · editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) · #s^(k−1)`.

**The coefficient depends on both `k` and the language's arity profile — it is not `p(k)` and
not a function of `k` alone.** `Σ_R k^(arity R)` is the number of potential atomic incidences on
`k` vertices: `k²` per binary symbol, `k³` per ternary symbol, summed over the (finitely many,
by `FiniteRelational`) symbols. Conflating it with `p(k)` would be wrong at every arity — even
for a single binary symbol it is `k²`, not `k(k−1)/2`, because ordered atoms and diagonal
pattern tuples are both read by induced counting. The frozen form keeps the **per-symbol sum**;
a coarser corollary through `aggregateEditCount` costs the factor `max_R k^(arity R)` and is a
convenience wrapper, not the primitive.

**Arity 0 is a genuine boundary, not a formality.** The pinning argument needs `n ≥ 1`; a
nullary edit flips no tuple but changes every atom evaluation at once, so a single nullary
disagreement can shift the count by the full `(|s|)_k` — no bound of the shape above can absorb
it. The transfer therefore carries **nullary agreement as a hypothesis** (the arity-0 edit sets
are empty), the same exemption `NullaryCompatible` and `nullaryCompatible_majorityRound` already
encode. Since `majorityRound` never edits at arity 0, the hypothesis is free in the composite.

**Conventions.** Ordered edit mass with diagonals included, per `Relational/Edit` — an injective
`T` composed with a repeating pattern tuple `w` produces a diagonal host tuple, so diagonal
edits genuinely matter and the full (non-injective-filtered) `s`-box edit count is the right
input. A sharpening that stratifies by the pattern tuple's repetition profile and consumes an
injective edit count per stratum is available but stays out of the frozen core.

**Carrier scope, matching §7.** The transfer is frozen on the constant box `fun _ ↦ s`, in the
same units as the quotient and composite statements. The full-carrier form — with
`inducedEmbeddingCount` and `relationEditCount` and factor `|V|^(k−1)` — is the specialization
`s = univ`, since `editDistance … (fun _ ↦ univ)` is `relationEditCount`'s defining set. No
mixed statement (restricted count against full-carrier edit mass, or vice versa) is frozen:
either direction of mixing is unsound or lossy without an explicit off-`s` charge.

**Hard-stop verdict: does not fire.** The pinning derivation is one argument uniform in `k` and
in the arity — the coefficient is language-dependent but *computed*, by a closed formula, unlike
§1's local uniformity coefficient.

## 9. The composite theorem

The three parts chain in one order: edit transfer moves the count from `M` to an indivisible
approximant `N`, quotient agreement evaluates `N`'s count exactly up to the diagonal charge, and
§6's bridge estimates the transversal sum. The composite must be **explicit** — a named theorem,
not a proof pattern — because it is the statement issue #84 actually promises.

> Let `N` be indivisible for `Q : Finpartition s` (e.g. `N = M.majorityRound Q`), with nullary
> agreement between `M` and `N`. Then
> `|inducedEmbeddingCountOn P M (fun _ ↦ s) − Σ_{transversal, matching in N.quotient} Π_i |C i||`
> `≤ Σ_R k^(arity R) · editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) · #s^(k−1)
>   + p(k)·m·#s^(k−1)`.

Everything is in the `s`-restricted units of §§7–8 — restricted count, `s`-box edit mass,
extension factor `#s^(k−1)` — so the three terms compose without any off-`s` remainder; the
full-carrier composite is the specialization `s = univ`.

The first summand is §8; the second is §7's diagonal routing. Chaining §6's `bridgeRaw` on the
transversal sum then adds `(δlocal + p(k)·β)·#s^k` when the quotient count is further compared
against a product-density estimate, and the normalized corollary divides the whole chain by
`(|s|)_k` exactly as in §3a — guard-free, with positivity confined to the inversion lemma.

One conversion lemma is needed and is deliberately a separate step: `CellwiseEditBound` speaks
per cell box in relative form, while §8 consumes absolute per-symbol `s`-box edit counts. The
cell boxes of arity `n` partition the `s`-box `(fun _ ↦ s)` exactly, so summing the cellwise
bound over them yields
`editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) ≤ ε · #s^(arity R)` — **exact over the
partition boxes, with no off-`s` remainder**, precisely because §8 is frozen in `s`-restricted
units. That conversion — not a re-derivation of either side — is implementation step 11. With it,
`cellwiseEditBound_majorityRound_of_isHomogeneousCell` instantiates the composite's edit term
under cell homogeneity, which is exactly the "approximation yields counting" statement of the
issue: homogeneity in, counting out, every constant either computed uniformly (`p(k)`,
`Σ_R k^(arity R)`) or supplied locally (`δlocal`).

The composite introduces **no new coefficient of its own** — it is a sum of the three audited
terms — so it inherits the hard-stop verdicts of its parts: only `δlocal` is supplied.

## 10. Would-be instance, with its discrepancy

`abs_representativeInducedCount_sub_estimate_le` is the identified would-be instance. Its error is
`(7ε + 3β)·#s³`, which is `(C·ε + p(3)·β)·#s³` with `C = 7`.

**The discrepancy is twofold.** It is stated against the *binary palette* —
`HasBinaryPairPalette` and `binaryPairPalette P i j` — rather than an arbitrary pattern's induced
structure, and its uniformity hypotheses are three separately named conditions `hD01`, `hD02`,
`hD12` rather than one quantified over pairs `i < j`. Becoming an instance requires the palette to
be replaced by a pair-indexed family and the three hypotheses collapsed into one indexed
condition. Nothing in its proof appears to obstruct that; the specialization is in the statement,
not the argument.

It does **not** exhibit a uniform coefficient, and should not be read as evidence for one: its `7`
is inherited wholesale from `Graph/TriangleCounting`.
