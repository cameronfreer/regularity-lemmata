# Design: generic approximation-to-counting and edit transfer

Work in progress. Nothing here is a theorem; theorems live in the library and their conventions
in [`ARCHITECTURE.md`](../../ARCHITECTURE.md). This document is the audit-and-freeze deliverable
for issue #84. It records what already exists, what each version actually proves, and the
interface decisions — **no implementation**.

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
| Bad-pair charge `3β` | `p(k) · β` | **conditionally uniform**, once the indexed union bound of §4a is proved; unproved today |
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
| `relationEditCount`, `aggregateEditCount`, `relativeAggregateEdit` (`Relational/Edit`) | per symbol | `/ |V|^arity`; aggregate `/ Σ_s |V|^arity(s)`, every symbol–tuple incidence weight one | diagonals included; `injectiveRelationEditCount` is the separate injective form | the **input** to edit transfer |
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

**Primitive: ordered injective tuples, normalized by the falling factorial `(|V|)_k`.**

- It is what the pattern-count layer already does: `inducedEmbeddingCount` and
  `inducedEmbeddingCountOn` both filter on `Function.Injective`, so an all-tuple primitive would
  disagree with every existing consumer.
- Under it the diagonal contributes nothing, so the transfer coefficient cannot silently absorb a
  diagonal term.
- `injectiveRelationDensity` already commits to `(|V|)_k`, and its docstring says "never by
  `|V|^n`".

**The conversion must be proved, not left to consumers.** Both halves exist:
`injectiveTupleCount_add_card_nonInjectiveMaps` (exact split) and `card_nonInjectiveMaps_le` with
`nonInjectiveMaps_ratio_le` (the bound). The bridge should export the conversion with a stated
error so a consumer wanting `|V|^k` normalization is not guessing.

### 3a. Two levels, stated separately

Choosing a normalized primitive does **not** mean the aggregation theorem should divide. The
bridge is exposed at two levels, and §6's displayed statement is the first of them:

* a **denominator-free raw theorem**, comparing the injective *count* to the estimate, with the
  error in units of `#s^k` — no division anywhere, so signed weights and degenerate carriers need
  no guard;
* a **normalized corollary**, dividing through by the falling factorial `(|V|)_k` to obtain the
  density form.

**The `|V| < k` endpoint.** When `|V| < k` there are no injective `k`-tuples, so the count is `0`
and `(|V|)_k = 0`. Under the library's guard-free `x / 0 = 0` convention both sides of the
normalized corollary are `0`, and the inequality holds — so **the corollary needs no positivity
hypothesis**, exactly as `boxDensity_le_one` needs none. This is worth stating explicitly, because
the natural instinct is to guard it.

**Where positivity is genuinely needed** is the *converse* direction: recovering a count bound
from a density bound requires multiplying by `(|V|)_k`, which is informative only when that is
nonzero. `injectiveTupleCount_pos_of_le` supplies it from `k ≤ |V|`. The interface should place
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

### 4a. The indexed bad-pair union bound

The `p(k)·β` term is **not** free, and until it is proved the coefficient is a supplied parameter
like `δlocal`. What must be shown is the generic union bound:

> if every coordinate-pair bad event has mass at most `β`, their union has mass at most `p(k)·β`.

This is a union bound over the `p(k)` events indexed by `i < j`, so it shares its index set with
the diagonal gate's collision events and should reuse the same characterization. Once proved, the
coefficient is **conditionally uniform under the indexed pairwise hypothesis** — conditional
because it presupposes the bad events are given per coordinate pair, which is a real restriction
on how a consumer states its uniformity failure.

Until then the bridge takes the aggregate bad-pair mass as a hypothesis, exactly as
`abs_representativeInducedCount_sub_estimate_le` already does with `hmass`.

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
unstateable.

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
  (hbad    : <aggregate bad-pair mass ≤ β · #s ^ 2>)
  (hdiag   : ∀ C ∈ Q.parts, C.card ≤ m)
  … : |injectiveCount − estimate| ≤ (δlocal + p k · β) · #s ^ k + p k · m · |s| ^ (k − 1)
```

* `δlocal` is **supplied**, never computed. §1.
* `p k · β` is computed **only once §4a is proved**; until then `β`'s coefficient is supplied too.
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

Divides `bridgeRaw` through by `(|V|)_k`. Guard-free, no positivity hypothesis; see §3a for the
`|V| < k` endpoint and for where positivity is genuinely required.

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
3. indexed bad-pair union bound (§4a);
4. injective/all-tuple conversion (§3);
5. raw aggregation bridge;
6. normalized corollary;
7. arity-2 and arity-3 wrappers.

Steps 1–2 are worth doing regardless of whether the bridge is ever built.

## 7. Would-be instance, with its discrepancy

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
