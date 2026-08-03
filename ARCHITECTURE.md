# Architecture and conventions

These conventions are frozen. Changes require an explicit owner decision recorded here.

## Type policy

- **Raw counts live in `ℕ`.** Cardinalities, edit distances, and tuple counts are natural
  numbers.
- **Normalized densities and errors live in `ℝ`.** There is no pervasive `ℚ → ℝ` cast
  layer. Where mathlib's API is `ℚ`-valued (e.g. `SimpleGraph.edgeDensity`,
  `Finpartition.energy`), a bridge states exactly one `Rat.cast` equation at the boundary.

## Denominator policy

- Densities are **zero on an empty denominator**, via real division's `x / 0 = 0`.
  Definitions carry no `if`-guards for emptiness.
- Denominator positivity or support nonemptiness is required as an **explicit
  hypothesis exactly where it is genuinely necessary** — in particular for complement
  and cancellation statements (`d(p) + d(¬p) = 1` is false on the empty support). It is
  NOT added categorically: conversion inequalities such as
  `c ≤ densityOn S p → c·|S| ≤ #filter` hold unconditionally under the convention
  (`c · 0 ≤ 0`), and are stated guard-free.

## Injectivity policy

- All copy-counting intended for removal arguments uses **injective source tuples**.
  Diagonal-sensitive variants must be separate, clearly named, and require exact diagonal
  control. Collision (non-injective) mass is bounded explicitly and loses one ambient
  power of the host size.

## Partition conventions

- Partitions are mathlib `Finpartition`s; the library never introduces a private
  partition type.
- **`P ≤ Q` means `P` is finer than `Q`** (mathlib's order).
- **Energy is mass-weighted.** The partition energy is
  `Σ_{A,B} (|A||B| / |s|²) · d(A,B)²`, **including diagonal blocks**. This is the
  refinement-monotone quantity; the uniform block-mean of `d²` is *not*
  refinement-monotone and is never used as the primary notion. Mathlib's
  `Finpartition.energy` (uniform, `ℚ`-valued, off-diagonal) is bridged only where both
  sides speak `SimpleGraph`.

## Statement discipline

- **No `sorry`, `admit`, or custom `axiom` on committed branches.** All declarations use
  only the standard axioms `propext`, `Classical.choice`, `Quot.sound`
  (enforced by `scripts/check.sh`, which audits every declaration in the library
  namespace).
- **No contentless `Prop` placeholders.** An unproved major result is never represented
  by defining a large `Prop` and treating it as available.
- Major statements pass, in order: a mathematical statement review; small finite
  counterexample tests; a dependency audit; and only then an API freeze.
- Search mathlib before introducing every foundational definition; wrap rather than
  reprove.

## Code organization

- Files stay focused, generally below 600 lines.
- Each file ends with a `/-! ### Tests and adversarial examples -/` section exercising
  its API on small finite types (kernel `decide` preferred; `native_decide` only in
  anonymous `example`s).
- Every green semantic unit becomes a commit and is pushed immediately. Pushed history
  is never rewritten.

## Module dependency direction

Dependencies run one way, and a module may not import from a layer above it:

```
Finite  →  Partition  →  Graph
Finite  →  Hypergraph
{ Graph , Hypergraph }  →  Relational
```

`Graph` and `Hypergraph` are independent of each other; `Relational` sits above both, since
its adapters and counting bridges consume the hypergraph vocabulary as well as the graph
regularity machinery.

`Finite` holds the counting, density, edit, and abstract-selection substrate and imports
only mathlib. Generic machinery discovered while building an upper layer belongs at the
layer where its hypotheses live, not where it was first needed: a lemma mentioning no
partition belongs in `Finite`, and one mentioning no palette or proxy belongs with the
counting substrate rather than with its first consumer.

## Relational substrate conventions

- **Mathlib languages, directly.** No competing first-order syntax. A typeclass
  `RegularityLemmata.FiniteRelational` (kept in the library namespace so the axiom audit
  walks it) supplies `arityBound : ℕ` (an upper bound, not necessarily attained),
  relationality, per-arity `Fintype`/`DecidableEq`, and emptiness above the bound (consumed
  through a theorem, not an aggressive instance). The bounded symbol type
  `RelSymbol L = Σ n : Fin (arityBound + 1), L.Relations n` bridges arbitrary mathlib
  symbols to bounded computation. **Arity zero is supported and permanently tested**: a
  nullary relation has one tuple even on an empty carrier.
- **Boolean model data, explicit mathlib adapter.** `FiniteRelModel L V` stores
  `rel : ∀ {n}, L.Relations n → (Fin n → V) → Bool`; `Holds` is the `Prop` reading.
  `toStructure : L.Structure V` is an **explicit definition, never a global instance** —
  multiple models on one carrier are routine; consumers write `letI := M.toStructure`.
- **Transport before counting**: `pullback` (frozen direction:
  `(pullback M f).Holds R x ↔ M.Holds R (f ∘ x)`), `restrict`, `relabel`, with identity and
  composition laws. Pullback along a noninjective map is allowed; no theorem claims it
  preserves injective counts.
- **Ordered and injective relation counts are separate APIs.** `relationCount` (all tuples,
  diagonals included — the canonical first-order count) versus `injectiveRelationCount`.
  Densities: `relationDensity` normalized by `|V|^n`, `injectiveRelationDensity` by the
  falling factorial — never the injective count by `|V|^n`. No unqualified "copy count"
  names.
- **Per-symbol edits are primitive**; the aggregate is defined afterward with the
  cross-arity weighting frozen: `aggregateEditCount = Σ_s relationEditCount`,
  `aggregateTupleBudget = Σ_s |V|^{arity s}`, relative = count / budget. Every
  symbol–tuple incidence has weight one; not normalized by `|V|^arityBound`, and per-symbol
  relative edits are not averaged. Nullary symbols contribute budget `1` even on an empty
  carrier. House `¬(P ↔ Q)` form.
- **Pattern maps** quantify computationally over `RelSymbol`; counts are
  `homCount`/`injectiveHomCount`/`inducedEmbeddingCount` — never "copyCount", since
  relational inducedness is diagonal-sensitive and includes nullary symbols. Host
  monotonicity holds for homomorphism counts only.
- **Adapters live in their own file** (the core imports only `ModelTheory/Basic`): mathlib's
  `FirstOrder.Language.graph`; a one-symbol arity-`r` language for uniform hypergraphs
  (noninjective tuples false; injective relation count `= orderedCount = r!·#edges`); a
  one-symbol-per-color language for colored hypergraphs. The relational core stays ordered;
  the adapters are exactly where ordered tuples meet unordered edges.

## Binary palette conventions

The load-bearing decision is to regularize the **complete two-way binary palette**, not each
relation symbol independently: separate per-symbol regularity controls neither correlations
*among* symbols nor the *joint* forward/reverse distribution of one symbol, and induced
binary patterns need both. Three kernel-`decide` falsification examples (joint-symbol
correlation, direction correlation, loop/profile sensitivity) are permanent.

- **Vertex profile**: `BinaryVertexProfile L = (L.Relations 1 → Bool) × (L.Relations 2 →
  Bool)`, recording every unary relation at `v` and every binary loop `R(v,v)`. Loop values
  are atomized into profiles, never dismissed as collision error. Nullary symbols are global
  constants; arity `> 2` is out of scope.
- **Pair palette**: `BinaryPairPalette L = L.Relations 2 → Bool × Bool`, recording every
  binary symbol jointly and in **both** directions. Reversal is explicit and involutive.
  `#BinaryPairPalette = 4^(#binary)` — `4^m`, not `2^m`.
- **Palette regularity** is simultaneous over all palette colors, strictly stronger than
  per-symbol regularity.
- **Energy `≤ 1`, not `≤ #colors`.** On each nonempty block the palette densities form a
  probability vector, so `Σ_c d_c² ≤ Σ_c d_c = 1`. This is why the iteration fuel stays
  `⌈1/ε⁵⌉`, independent of the number of palette colors.
- **One bad color per step.** A failure yields one bad palette color and the increment
  applies the directed graph theorem to it; witnesses are **not** atomized for every color
  simultaneously, so the part-count recurrence is exactly the graph recurrence.

## Counting conventions

- **Arity discipline.** A dedicated `AtMostBinary L` class (`∀ n, 2 < n → IsEmpty
  (L.Relations n)`, **not** `arityBound L ≤ 2` — the stored bound is not canonical) gates
  every theorem translating palette data into full relational induced embeddings.
- **The reduction.** For injective `f`, `PreservesAndReflects P M f` iff `P` and `M` are
  nullary-compatible, share vertex profiles along `f`, and share pair palettes on distinct
  indices — proved for arbitrary finite `W`, so pattern-specific counts are bookkeeping over
  the palette machinery rather than model theory.
- **Pattern-local union bounds.** The strong-witness count replaces fine densities with
  coarse ones over only the three required palette colors, not all `4^m`.
- **Transversal versus diagonal.** Regularity controls pairs of *distinct* cells, so counts
  are proved first for transversal embeddings and the diagonal-cell mass is charged
  separately by a derived constant. A count stated without that separation is not a global
  count.

## Triadic conventions

- **Unordered triads, ordered counting.** Objects are unordered `UniformHypergraph 3 V`;
  every counting and testing surface is ordered injective triples, mediated by
  `orderedCount = 3!·#edges`. Observables on triples are set-level, hence
  permutation-invariant by construction.
- **Edit normalization and the factor 6.** The primitive edit count is unordered; the
  ordered edit mass over injective triples equals `6 · editCount` — proved, never assumed.
  Relative quantities divide by `|V|³` under the guard-free convention, not by the
  injective-tuple count.
- **Regularity thresholds are parent-relative** — a `δ` fraction of the parent polyad block,
  never an absolute count.
- **Exceptional triad mass** is ordered and diagonal-free: for a set `E` of keys, the mass is
  `Σ_{key ∈ E} |polyadBlock κ key| / |V|³`.
- Deletion-only edits are made well-defined across all six ordered presentations of an
  unordered triple by permutation closure of the badness predicate.

## Frozen public constants

Selected quantitative choices intentionally frozen by the public API. This table is
**curated, not exhaustive**: many derived counting coefficients also appear in statements
without being design commitments. Changing anything listed here breaks callers.

| Constant | Value | Role |
| --- | --- | --- |
| `familyChunkThreshold` | `100` | Chunk-count threshold in the equitable increment. |
| `familyChunkDensityError` | `ε / 2` | Density error charged to chunking. |
| `familyRetainedFraction` | `1 / 5` | Fraction of the exact-refinement energy gain retained by the equitable increment. |
| one-step family gain | `ε⁵ / 5` | Global family-energy gain per nonregular refinement step. |
| `familyFuel` | `⌈5K / ε⁵⌉₊` | Iteration fuel for the family summit. |
| `familyStepBound` | `n · familyChunksPerPart n` | Part-count recurrence; preserves divisibility by three. |
| `supplierTolerance` | `min (τ/2) (1 / (64(K+1)t))` | Piece-supplier tolerance, derived from its Markov requirement. |
| `supplierParts`, `supplierRetention` | `4t`, `t / (2B)` | Piece-supplier output shape. |
| `triadFuel` | `⌈1/δ⁴⌉₊` | Triadic iteration fuel. |

## Supported theorem boundary

- The relational substrate supports arbitrary finite relational languages and exact
  finite-model counts.
- Regularity and regularity-based counting assume **arity at most two**; the quantitative
  induced-counting theorem treats patterns on **`Fin 3`**.
- There is **no relational induced-removal theorem**. Its design lives in
  [`docs/design/induced-removal.md`](docs/design/induced-removal.md).
- The triadic approximation is a precursor, not a formalization of the full Rödl–Schacht
  theorem.

## Deferred summit statements

Intended results whose proofs are not complete are recorded as prose — never as Lean `Prop`
placeholders.

- **Self-regular almost-refining equipartition.** The proved
  `exists_regular_refinement_and_almostRefining_equipartition` produces a regular exact
  refinement plus an equipartition almost-refining both. The stronger version in which the
  equipartition is *itself* regular requires equitabilising inside the energy-increment loop,
  transporting energy across the exceptional mass, and is deferred.
- **Relational induced removal.** Deferred, with its design and open certificates in
  [`docs/design/induced-removal.md`](docs/design/induced-removal.md).
- **Colored arity-three counting and removal.** Statements will be frozen only after their
  falsification gates.

## Design documents

Work in progress that is not yet a theorem lives under `docs/design/`, one document per
target, stating the goal, the fixed normalizations, the proved inputs, the current
construction, the permanent obstruction gates, the open certificates, and the non-goals.
Rejected routes are recorded there once, by their mathematical obstruction; Git history and
issues preserve the order of discovery.
