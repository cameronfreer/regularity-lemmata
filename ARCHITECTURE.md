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

## Deferred summit statements

Intended results whose proofs are not yet complete are recorded here as prose — never as
Lean `Prop` placeholders.

- **Self-regular almost-refining equipartition**: the proved
  `exists_regular_refinement_and_almostRefining_equipartition` produces a regular exact
  refinement `Q ≤ P₀` plus an equipartition `E` almost-refining both. The stronger
  version in which `E` is *itself* regular requires running equitabilisation
  inside the energy-increment loop (transporting the energy across the exceptional
  mass) and is deferred.
- **Relational induced removal**: fixed-pattern and family induced removal for
  three-vertex patterns over the binary-palette counting layer. The scope and
  normalization are frozen in the Phase 11 section below; the exact quantitative
  signatures remain provisional. Since the 2026-07-26 re-freeze they wait on TWO route (b)
  ladder gates: the transversalization gate (step 2) and the transversal rounding
  certificate (step 5). Repeated-cell counting is only PROVISIONALLY retired — the
  intended edit charge on repeated coarse cells does not by itself show those cells
  induce no surviving pattern, which is exactly what step 2 must settle.
- **Colored arity-three counting/removal**: planned for later releases; statements
  will be frozen only after their falsification gates. (The triadic regular
  approximation itself is no longer deferred: both the weak and the edited summits
  are proved — see the Phase 7 section below.)

## Phase 7 design freeze (triadic regular approximation)

Target: a **weak pair-coloring regularization theorem** using the Rödl–Schacht index
and polyad test surfaces — a *precursor to, not a formalization of*, the full
regular-partition theorem of V. Rödl, M. Schacht, *Regular partitions of
hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007) (their result
concerns families of compatible hypergraph partitions with equitable vertex
partitions, which are deliberately deferred here). Test surfaces are the local
parent-relative predicates `IsDiscRegularAt`/`IsPolyadRegularAt`
(`Hypergraph/PolyadRegularity.lean`), with the canonical own-density form
`IsLocalDiscRegular`. The following choices are frozen in prose first; the summit
statements stay prose until their falsification gates pass.

- **Unordered triads, ordered counting.** The objects are unordered
  `UniformHypergraph 3 V`; every counting and testing surface is ordered injective
  triples, mediated by the realization identity `orderedCount = 3! · #edges`
  (`orderedCount_eq`). Observables on triples are set-level
  (`triadObs H v = tupleRange v ∈ H.edges`), hence permutation-invariant by
  construction. Ordered face/triad structures, if ever wanted, are exposed
  separately, never as this API.
- **Input and edited hypergraphs** are both `UniformHypergraph 3 V`; the edit
  primitive is the unordered symmetric difference of edge sets
  (`UniformHypergraph.symmDiff`).
- **Edit normalization and the factor 6.** The primitive edit count is unordered
  (`editCount H G = #(H ∆ G)`); the ordered edit mass over injective triples equals
  `6 · editCount` — proved (the realization identity applied to `symmDiff`), never
  assumed. Relative quantities divide by `|V|³` under the guard-free `x / 0 = 0`
  convention, not by the injective-tuple count; the injective/total gap is controlled
  by the Phase 1 collision bounds where needed.
- **Regularity thresholds are parent-relative** — a `δ` fraction of the parent polyad
  block, never an absolute count. No absolute thresholds appear in Phase 7
  statements (`IsBlockUnionRegular` is not used by Phase 7).
- **Exceptional triad mass** is ordered and diagonal-free: for a set `E` of keys, the
  mass is `Σ_{key ∈ E} |polyadBlock κ key| / |V|³`. A pair coloring is `δ`-good for
  `H` when the keys on which the required block control fails carry mass at most `δ`.
- **Partition data.** The first release quantifies over pair colorings
  `κ : RSet 2 V → Fin K` only. Compatibility with an equitable vertex partition (and
  equitability of pair cells over vertex-cell triples) is required for the full
  Rödl–Schacht statement but not for the weak (energy-increment) approximation; it is
  a deferred strengthening, to be built on `Partition/Equitable.lean`.
- **Quantifier order (error schedule and bounds).** `∀ δ > 0, ∃ K₀ = bound(δ)`
  host-independent; `∀ H` on a finite `V`, `∃ K ≤ K₀` and a pair coloring `κ` with
  `K` cells satisfying the goodness conclusion. Iteration schedules follow the graph
  ladder's `ErrorSchedule` pattern (`Graph/Strong.lean`). **No quantitative bound is
  frozen yet**: a failing local disc test yields roughly a `δ³` energy gain on its
  block and hence roughly `δ⁴` globally when bad keys carry mass `> δ`, but
  simultaneously resolving witnesses across up to `K³` keys can multiply the pair
  colors by roughly `2^{O(K³)}` per round (a recurrence like `K ↦ K · 2^{3K³}`, not
  a single exponential). The bound is frozen only after Unit 4 derives the actual
  increment and cardinality recurrence.
- **Two summit statements, in order.** First the weak regularization **without
  editing** — now PROVED (`exists_goodColoring`): `∃ κ` with at most `triadBound δ`
  pair colors such that `badTriadMass H κ δ ≤ δ` (bad keys are `IsBadTriad`,
  failures of the own-density local predicate; the mass is the frozen ordered
  normalization). Then the **edited
  regular approximation** — now PROVED (`exists_triadic_regular_approximation`): `∃ κ G` with
  `G.edges ⊆ H.edges`, `6 · editCount H G ≤ δ · |V|³` (the frozen ordered edit
  inequality) and EVERY key locally disc-regular for `G` — with `G` constructed by
  deleting the bad-keyed edges, well-defined via the permutation closure of bad keys
  (`isBadTriad_comp_perm_iff`) so that all six ordered presentations of an unordered
  triple receive the same edit decision.

Planned units, in order: (1) realized triads and mass identities ✓; (2) block
density/edit calculus ✓; (3) refinement energy for pair colorings (mass-weighted,
diagonal included, refinement-monotone, with the exact variance identity
`polyadEnergyNum_comp_variance`) ✓; (4) one-step repair — bad-key mass and
permutation closure ✓, witness selection for failed local regularity ✓
(`DiscWitness`, `exists_discWitness`), simultaneous witness atomisation with its
color-count recurrence ✓ (`cutRefine`, `cutBound j K = K·2^{K^{j+1}(j+1)}` proved by
construction), witness atoms as unions of refined blocks ✓
(`discAtom_eq_biUnion_cutRefine` over `resolvingKeys`, with cardinality corollaries);
the local increment theorem ✓ (`local_variance_gain`: strict
`δ³·|block| <` refinement variance at a witnessed key) AND the simultaneous global
increment ✓ (`polyadEnergy_cutRefine_gain`: `δ⁴ < polyadEnergy refined − polyadEnergy
coarse` when `δ < badTriadMass`, via the chosen simultaneous witness family);
(5) bounded iteration ✓ — the frozen recurrence `triadRegularityBound`
(iterating `cutBound 2`), the existential fuel theorem
`exists_goodColoring_of_fuel`, fuel `triadFuel δ = ⌈1/δ⁴⌉₊`; (6) the **weak summit
is proved**: `exists_goodColoring` — every 3-uniform hypergraph admits a pair
coloring with at most `triadBound δ = triadRegularityBound ⌈1/δ⁴⌉₊ 1` colors and
bad mass at most `δ` (`Hypergraph/TriadIncrement.lean`). The **edited summit is
also proved**: `exists_triadic_regular_approximation` (`Hypergraph/TriadCleanup.lean`) — a
deletion-only subgraph within `δ·|V|³` ordered edits under which EVERY key is
locally disc-regular, with deletion defined by an existential ordering of
each unordered edge — permutation closure keeps it well-defined; the construction is
mathematically finite and classically decidable, not kernel-computable (the badness
predicate is real-valued).

## Phase 8 design freeze (finite relational structures substrate) — COMPLETE

A computable finite relational-structure layer over mathlib's
`FirstOrder.Language` (`Mathlib.ModelTheory.Basic`), ending at counts, edits,
transport, and adapters. **No relational regularity or removal theorem belongs to
this phase**; those are deferred to a later phase, to be built only after this API
passes its falsification gates. All units below are implemented
(`Relational/{Language,Model,Transport,Counts,Edit,PatternCounts,GraphAdapter,
HypergraphAdapters}.lean`); the frozen decisions are recorded for reference.

- **Mathlib languages, directly.** No competing first-order syntax. A typeclass
  `RegularityLemmata.FiniteRelational` (kept in the library namespace so the axiom
  audit walks it) supplies `arityBound : ℕ` (an upper bound,
  not necessarily attained), relationality, per-arity `Fintype`/`DecidableEq`, and
  emptiness above the bound (consumed through a theorem, not an aggressive
  instance). The bounded symbol type `RelSymbol L = Σ n : Fin (arityBound + 1),
  L.Relations n` bridges arbitrary mathlib symbols to bounded computation. **Arity
  zero is supported and permanently tested**: a nullary relation has one tuple even
  on an empty carrier.
- **Boolean model data, explicit mathlib adapter.** `FiniteRelModel L V` stores
  `rel : ∀ {n}, L.Relations n → (Fin n → V) → Bool` (no `Fintype`/`DecidableEq`
  requirements in the structure itself); `Holds` is the `Prop` reading.
  `toStructure : L.Structure V` is an **explicit definition, never a global
  instance** — multiple models on one carrier are routine; consumers write
  `letI := M.toStructure`. The `RelMap ↔ Holds` bridge is exact.
- **Transport before counting**: `pullback` (frozen direction:
  `(pullback M f).Holds R x ↔ M.Holds R (f ∘ x)`), `restrict` (pullback along the
  subtype inclusion), `relabel` (pullback along `e.symm`), with identity/
  composition laws and mathlib `Equiv.inducedStructure` compatibility. Pullback
  along a noninjective map is allowed; no theorem claims it preserves injective
  counts.
- **Ordered and injective relation counts are separate APIs.** `relationCount`
  (all tuples `Fin n → V`, diagonals included — the canonical first-order count)
  vs `injectiveRelationCount` (filtered through `injectiveTuples`). Densities:
  `relationDensity` normalized by `|V|^n`; `injectiveRelationDensity` by the
  falling factorial — never the injective count by `|V|^n`. No unqualified "copy
  count" names.
- **Per-symbol edits are primitive**; the aggregate is defined afterward with the
  cross-arity weighting frozen: `aggregateEditCount = Σ_{s : RelSymbol}
  relationEditCount`, `aggregateTupleBudget = Σ_s |V|^{arity s}`, relative =
  count/budget — every symbol–tuple incidence has weight one. Not normalized by
  `|V|^arityBound`; per-symbol relative edits are not averaged. Nullary symbols
  contribute budget `1` even on an empty carrier. House `¬(P ↔ Q)` form.
- **Pattern maps**: `Preserves`/`PreservesAndReflects` quantify computationally
  over `RelSymbol` (equivalence with the unbounded form via emptiness above the
  bound); counts `homCount`/`injectiveHomCount`/`inducedEmbeddingCount` (never
  "copyCount" — relational inducedness is diagonal-sensitive and includes nullary
  symbols), with conversions to mathlib `Language.Hom` (preserves) and
  `Language.Embedding` (preserves and reflects) and their converses. Host
  monotonicity holds for homomorphism counts only.
- **Adapters live in their own file** (the core imports only `ModelTheory/Basic`):
  mathlib's `FirstOrder.Language.graph` for simple graphs (no second graph
  language); a one-symbol arity-`r` language for uniform hypergraphs (noninjective
  tuples false; injective relation count `= orderedCount = r!·#edges`); a
  one-symbol-per-color language for colored hypergraphs. The relational core stays
  ordered; the adapters are exactly where ordered tuples meet unordered edges.
- **Discipline**: each module lands in the same commit as its root import
  (staging `RegularityLemmata.lean` explicitly, verified via
  `git diff --cached --name-only`) so the axiom audit sees it; small examples close
  by kernel `decide`; no wholesale palette/local-type port.

## Phase 9 design freeze (finite-palette binary relational regularity) — COMPLETE

Regularizing the **binary reduct** of a finite relational model: a directed
adaptation of the mass-weighted graph regularity and strong-regularity machinery
(`Graph/*.lean`) over the finite relational substrate (`Relational/*.lean`), using
mathlib's partition substrate and graph-regularity antecedents. **Not general
relational regularity**: it says nothing about relation symbols of arity `> 2`, and
removal is deferred to a later phase.

The load-bearing decision is to regularize the **complete two-way binary palette**,
not each relation symbol independently — separate per-symbol regularity does not
control correlations *among* symbols, nor the *joint* forward/reverse distribution
of one symbol, and both are needed for induced binary patterns. Loop values
`R(v,v)` are atomized into vertex profiles rather than dismissed as collision error.
Three kernel-`decide` falsification examples (joint-symbol correlation, direction
correlation, loop/profile sensitivity) are permanent, justifying the full palette.

- **Vertex profile**: `BinaryVertexProfile L = (L.Relations 1 → Bool) ×
  (L.Relations 2 → Bool)`, recording every unary relation at `v` and every binary
  loop `R(v,v)`. Nullary symbols are global constants (no partition); arity `> 2` is
  out of scope. `#BinaryVertexProfile = 2^(#unary + #binary)`.
- **Pair palette**: `BinaryPairPalette L = L.Relations 2 → Bool × Bool`, recording
  every binary symbol jointly and in **both** directions `(R(a,b), R(b,a))`. Reversal
  is explicit (`binaryPairPalette M b a = swap …`) and involutive.
  `#BinaryPairPalette = 4^(#binary)` — `4^m`, not `2^m`.
- **Palette regularity**: `IsBinaryPaletteRegular M ε P = ∀ c, IsRegularPartition
  (HasBinaryPairPalette M c) ε P` — simultaneous over all palette colors, strictly
  stronger than per-symbol regularity.
- **Energy `≤ 1`, not `≤ #colors`**: on each nonempty block the palette densities are
  a probability vector, so `Σ_c d_c² ≤ Σ_c d_c = 1`; mass-weighting and summing over
  blocks keeps `binaryPaletteEnergy ≤ 1`. This is why the iteration fuel stays
  `⌈1/ε⁵⌉`, independent of the number of palette colors.
- **One bad color per step**: a failure yields one bad palette color; the increment
  applies the existing directed graph theorem to it (others are refinement-monotone),
  so the part-count recurrence is exactly the graph recurrence — witnesses are **not**
  atomized for every color simultaneously.
- **Summit** (`exists_binaryPalette_regular_refinement`): `∃ Q ≤ P` with
  `Q ≤ binaryProfilePartition M s`, `IsBinaryPaletteRegular M ε Q`, and
  `Q.parts.card ≤ binaryRegularityBound L ε P.parts.card`, host-independent. The
  docstring states explicitly that it asserts nothing about arity `> 2`.
- **Strong palette witness** (`BinaryPaletteStrongWitness`) reuses `ErrorSchedule`,
  refines the profile partition, and exposes per-color `toStrongWitness` /
  `deviant_mass_le` conversions to the existing `StrongWitness` API — the handoff
  consumed by the Phase 10 counting layer (which closed the old strong-witness
  counting item; relational removal is still deferred).

Phase 9 ends at the profile-respecting common partition, simultaneous palette
regularity, host-independent bounds, and the strong palette witness. It contains **no
removal summit**. The following Phase 10 delivered the counting statement freeze
(two-vertex palette counts; colored directed path/triangle counts; induced
three-vertex relational counts); fixed-pattern / finite-family induced removal
remains deferred.

All Phase 9 units are implemented (`Relational/Binary{Palette,Profile,Energy,
Increment,Regularity,Strong,Bridges}.lean`): the two-way palettes and vertex
profiles, the profile partition, the palette energy and regularity surface, the
one-step increment, the weak summit `exists_binaryPalette_regular_refinement`, the
strong witness `exists_binaryPaletteStrongWitness` with its per-color
`toStrongWitness`/`deviant_mass_le` handoff, and the graph bridges. The phase ends
here: **no removal summit**. Phase 10 (below) delivered the counting statement freeze
(two-vertex palette counts; colored directed path/triangle counts; induced
three-vertex relational counts), closing the old strong-witness counting item;
fixed-pattern / finite-family induced removal remains deferred (see the deferred
summit list above).

## Phase 10 design freeze (binary-palette counting through three vertices) — COMPLETE

**Counting only — no removal.** This phase closes the long-deferred strong-witness
counting item: exact two-vertex palette counts, directed colored path and triangle
counts, induced three-vertex relational counts, and a theorem genuinely consuming a
`BinaryPaletteStrongWitness`. Fixed-pattern and finite-family induced **removal** are
deferred to a later phase. Global removal additionally needs control of embeddings
whose vertices land in the same partition cell, so this phase includes the explicit
diagonal-cell gate (an initial equipartition bounding coarse cell sizes and an
explicit diagonal-cell error term — the Unit 8 diagonal gate below); removal itself
remains deferred.

- **Arity discipline.** A dedicated `AtMostBinary L` class
  (`∀ n, 2 < n → IsEmpty (L.Relations n)`, **not** `arityBound L ≤ 2` — the stored
  bound is not canonical) gates every theorem that translates palette data into full
  relational induced embeddings; without it the palette ignores higher-arity
  relations.
- **The reduction.** For an injective `f`, `PreservesAndReflects P M f` iff `P` and
  `M` are nullary-compatible, share vertex profiles along `f`, and share pair palettes
  on distinct indices — proved for arbitrary finite `W`, so every pattern-specific
  count is bookkeeping over the palette machinery, not model theory.
- **The counting chain.** Two-vertex counts are exactly palette pair counts; a generic
  directed regular-degree calculus feeds directed regular path and triangle counting
  (stated for three unrelated directed relations, with palettes as an application and
  the error constant derived, not guessed); induced three-vertex counts reduce to
  colored triangle counts; and the strong-witness theorem replaces fine densities with
  coarse ones using a **pattern-local** union bound over only the three required
  palette colors (not all `4^m`), with error explicit in `E`, `δ/η²`, the `η` product
  perturbation, and cell masses.
- **Transversal versus global.** Regularity controls pairs of *distinct* cells, so the
  strong-witness count is proved first for transversal embeddings (three distinct
  coarse cells); the nontransversal (diagonal-cell) mass is bounded by a *derived*
  constant times `m·|s|²`, controlled by starting from an equipartition with enough
  cells so every later coarse cell inherits the bounded initial cell size — this is
  the key gate before any removal statement.
- **Graph bridges** recover directed/ordinary edge, path, triangle, and induced
  three-vertex simple-graph counts, closing the old deferred checklist item.

Provenance cites the exact counting-lemma source actually followed (mathlib where its
architecture is reused, otherwise the relevant public graph-regularity/counting
reference). The Phase 9 language is unchanged: this is binary-palette counting, not
general relational or hypergraph removal.

All Phase 10 units are implemented: the arity discipline and the reduction
(`Relational/BinaryPattern.lean`), two-vertex counts
(`Relational/TwoVertexCounting.lean`), the directed regular-degree calculus and
directed path/triangle counting (`Graph/RegularDegree.lean`, `Graph/PathCounting.lean`,
`Graph/TriangleCounting.lean`), induced three-vertex counts
(`Relational/ThreeVertexCounting.lean`), the strong-witness counting chain — the
selected-pair lifting calculus (`Relational/StrongCountingLifting.lean`), the
common-index expansions with the `10τ` regularity charge
(`Relational/BinaryStrongRegularityCharge.lean`), and the `3η + 3δ/η²` density-shift
charge with the assembled transversal summit
`BinaryPaletteStrongWitness.abs_transversalInducedCount_sub_coarseInducedEstimate_le`
(`Relational/BinaryStrongCounting.lean`, over the transversal counts of
`Relational/TransversalCounting.lean`) — the
diagonal gate with the global strong-counting corollary
`abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le` and the full-carrier
identity `globalInducedCount_eq_inducedEmbeddingCount`
(`Relational/DiagonalGate.lean`), and the graph bridges
(`Relational/GraphCounting.lean`): adjacency/nonadjacency palettes with the palette
classification, edge, path, and triangle counts with the `6 · #cliqueFinset 3`
conversion, induced three-vertex graph copies in both the disjoint-cell
(adjacency/nonadjacency) form and the full-carrier `inducedCopyCount` bridge, and the
strong-counting corollary specialized to `ofSimpleGraph`. The phase ends here: **no
removal theorem**.

## Phase 11 scope and normalization freeze (relational induced removal, three vertices)

**Scope and invariants are frozen here; the exact quantitative signatures and the
removal modulus remain provisional.** Until 2026-07-26 they waited on the
diagonal/repeated-cell feasibility gate; the re-freeze of that date PROVISIONALLY retires
the repeated-cell COUNTING consumption in favour of an explicit diagonal edit charge —
provisionally, because an edit charge does not by itself show a within-cell triple induces
no surviving pattern. What remains outstanding are therefore the transversalization gate
(ladder step 2), which must settle exactly that, and the transversal rounding certificate
(ladder step 5). The phase runs in two internal stages — 11A (feasibility) and 11B
(removal) — separated by a mandatory re-scope checkpoint; no public removal API lands
before that checkpoint.

**Target.** Induced removal for three-vertex binary-palette patterns, in two forms
produced by ONE construction: a fixed pattern `P : FiniteRelModel L (Fin 3)`, and an
arbitrary `ι`-indexed family `F : ι → FiniteRelModel L (Fin 3)` with **no**
`Finite ι`/`Fintype ι`/`DecidableEq ι` assumption. One cleaned model `N` is
constructed independently of the family; a **pattern-uniform certificate** ("any
three-vertex pattern occurring in `N` had strictly more than `δ·|V|³` induced copies
in `M`", on large hosts) yields the family summit pointwise and the fixed-pattern
theorem via a singleton index. If the family corollary ever becomes substantial,
pattern dependence has leaked into the construction — stop and re-examine. The
removal modulus depends on `L` and the edit budget `ε` only — never on the carrier,
the index type, the family size, or the particular patterns.

**Provisional target shape** (recorded for orientation, NOT frozen):

```
∀ ε > 0, ∃ δ > 0, ∀ {ι V} [Fintype V] [DecidableEq V]
  (F : ι → FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V),
  (∀ i, (inducedEmbeddingCount (F i) M : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 3) →
  ∃ N, relativeAggregateEdit M N ≤ ε ∧ ∀ i, inducedEmbeddingCount (F i) N = 0
```

- **Guard-free endpoint**: the smallness hypothesis uses `≤` and the certificate is
  strict (`δ·|V|³ < count` for surviving patterns on large hosts), so the
  empty-host/nonempty-family instance is a meaningful theorem rather than vacuous at
  the zero-denominator endpoint; a small-host branch (the modulus is small against
  `(N₀+1)⁻³`, forcing the ℕ-valued count to zero) handles the rest.
- **Edit measure**: the frozen `relativeAggregateEdit` (all arities, the Phase 8
  cross-arity weighting). A binary-only measure is FALSE — in a unary-only language a
  rare-profile pattern has order `n²` copies removable only by unary edits.
- `AtMostBinary L` is a hypothesis of every summit; `N` is an arbitrary
  `FiniteRelModel L V` (swap-consistency, profile preservation and the like are proof
  artifacts of the cleaning, never statement-side constraints); host = full carrier.

**Three-layer cleaning (frozen).** (1) Nullary relations are preserved exactly
(`NullaryCompatible P N ↔ NullaryCompatible P M`). (2) Exceptional vertex-profile
cleaning: unary values AND binary loops, via absorption of small or
exceptional-profile coarse cells into a maximal proxy cell (edit-free in the
degenerate no-symbol case). Pairs involving absorbed vertices are classified using
their **post-absorption proxy labels**: the proxy cell's coarse block pair supplies
the density that controls their keep/recolor decision, never the original small or
exceptional cell. (3) Off-diagonal pair-palette cleaning respecting the
reversal law (**representative-driven since 2026-07-26 — both the threshold and the
replacement palette**): keep a pair whose existing palette has REPRESENTATIVE block
density `≥ θ`, otherwise recolor to the REPRESENTATIVE-majority palette
`c(C,D) ∈ argmax_c pairDensity (HasBinaryPairPalette M c) (rep C) (rep D)`, with
`c(D,C) = swap (c(C,D))` holding by construction via a canonical orientation of
unordered coarse-cell pairs. The replacement must NOT be the coarse-majority palette:
on a deviant pair that palette can have ZERO representative density, which destroys the
freeness certificate even though its edit cost is duly charged. For a diagonal coarse pair the recolor target is a
palette ORBIT `{c, swap c}` oriented by a local (noncomputable, non-instance)
ordering of distinct host vertices — a constant palette on `(C,C)` must be symmetric,
and the dense object may be an asymmetric orbit. Loops stay in layer (2). The
principal pair-edit charge is the sparse-palette mass `≤ 4^m·θ·|V|²` plus pairs
incident to profile/proxy-edited vertices.

**Amended 2026-07-26 for the directed redesign.** Representative densities are what the
freeness proof has a floor for, and only on nondeviant pairs — hence both the threshold
and the recolor target above are representative-driven. Coarse pairs whose representative
densities deviate are charged WHOLESALE through the aggregate edit allowance rather than
kept uncharged; the earlier clause "density-deviant fine pairs are NOT recolored"
belonged to the superseded coarse-density cleaner and is withdrawn. Without this the
aggregate deviation bound has no consumer and the freeness argument has no density floor
to stand on. Note the two failure modes are distinct: charging a deviant pair fixes the
EDIT budget, not the certificate — a target palette with zero representative density
still leaves the pattern unrealizable on the representatives.

**Diagonal-inclusive regularity is a parallel additive layer.** Copies with two or
three vertices in one cell require uniformity of diagonal cell pairs `(C,C)`, which
the frozen off-diagonal `IsRegularPartition` deliberately does not control. The
increment machinery is distinctness-agnostic (the witness atomisation and energy
bookkeeping never use cell-distinctness, and the energy is diagonal-inclusive by the
frozen convention above), so a diagonal-inclusive ladder ports with identical fuel
and part-count recurrences. It is added as NEW predicates with a bridge to the
off-diagonal layer; the frozen `IsBadPair`/`IsRegularPartition` surface is unchanged
— an in-place redefinition would break the mathlib uniformity bridge (which cannot
deliver diagonal control) and the frozen counting-charge reindexings, and is
explicitly not taken.

**Off-diagonal representatives (re-frozen 2026-07-26; supersedes the role-indexed
design).** Freeness counting runs in the ORIGINAL model on representative fine cells:
ONE representative per large coarse cell (`rep : coarse.parts → fine.parts`), selected
mass-weighted from candidates with the size guarantee in multiplication form
(`2·q·|rep C| ≥ |C|`, `q` the host-independent fine-part bound — never natural-number
division). Two clauses, deliberately of different strengths:

- **Uniformity, per pair**: `(rep C, rep D)` is uniform for every palette color, for
  every ordered pair of representatives of **DISTINCT** coarse cells, by one simultaneous
  union bound — independent of the pattern family, with `C = D` excluded from the event
  index.
- **Density deviation, in AGGREGATE ONLY**: there is NO per-pair closeness requirement.
  The coarse pairs whose representative densities deviate from their coarse densities by
  more than `η` carry bounded aggregate `|C|·|D|` mass, and nothing further is claimed
  about them.

Consequently the working density floor `ρ = min(θ, 1/4^m) − η` (with
`η < min(θ, 1/4^m)`) applies **only to nondeviant pairs**; deviant pairs are handled by
the edit allowance, not by any density guarantee. Every distinct-realization lower bound
carries an explicit loop/collision subtraction: "density product − regularity error −
collision slack" (full-square densities only; no off-diagonal density variant; no
unqualified `1/4^m` bound for distinct pairs).

**Repeated-cell strata: PROVISIONALLY retired, conditional on a transversalization
certificate.** The intent is that only the all-cells-distinct stratum is counted, through
transversal counting on the representatives, with the four repeated-cell strata paid for
by the diagonal surgery calculus. **Cost control alone does not establish this**, and this
document must not pretend otherwise: recoloring inside `C × C` changes WHICH pattern a
repeated-cell triple induces, but the triple still induces SOME pattern, so the
pattern-uniform certificate does not follow from an edit bound. Gate G4 is the standing
warning — a planted within-cell copy is invisible to transversal counting, and no amount
of internal recoloring makes the transversal count see it.

The obligation, discharged BEFORE representative selection: prove that the proposed
diagonal rounding makes every surviving induced pattern admit a distinct-coarse-cell
realization, or else supply a separate original-copy lower bound for repeated-cell
realizations. Its solution may require clone or proxy coarse cells, which would change the
representative event index — which is why it cannot be deferred until after selection.

**Rejected alternatives (recorded so they are not re-derived).** Pure-majority
recoloring (edit mass ~`(1−4^{-m})·n²`); constant-palette recoloring (no spare
palette — a path pattern in graphs requires both symmetric palettes; on diagonal
pairs a constant palette must be symmetric, forcing orbit orientation);
local-averaging density transfer (its witness-gap tolerance depends on the coarse
part count, which grows with the tolerance — circular); and a SINGLE representative per
coarse cell **while still consuming diagonal events** (that converts the diagonal
bad-mass control `Σ|A|²` into `Σ|A|` at cost `2q` with `q` growing with the regularity
tolerance — the same circularity; no Cauchy–Schwarz argument removes it).

**That last rejection is superseded, conditionally, by the 2026-07-26 re-freeze**, and
the condition is load-bearing: the single-representative design is admissible ONLY
because `C = D` now leaves the event index entirely — no diagonal uniformity is
requested, so there is no diagonal bad-mass control to convert, and the diagonal is paid
for in edit cost instead. If a diagonal event ever re-enters the union bound, the
original rejection applies again verbatim.

**What Phase 10 machinery is consumed.** The strong palette witness (upgraded to its
diagonal-inclusive twin), `deviant_mass_le` (representative selection AND — amended
2026-07-26 — the wholesale edit charge for deviant coarse pairs; the earlier "never to
charge host pairs" belonged to the superseded coarse-density cleaner), the
profile/palette reduction (`preservesAndReflects_iff_profiles_palettes`,
`preservesAndReflects_three_iff`), and the directed triangle lower bound
(`directedTriangleCount_ge`). Also ON the path since 2026-07-26: the **bounded-cell
equipartition seed**, which the diagonal edit bound `Σ_C |C|² ≤ m·|V|` depends on. NOT on
the removal path: the coarse-estimate counting summit, and
`Relational/DiagonalGate.lean`'s `3·m·|s|²` COUNTING theorem — freeness counting happens
in the original model on representatives, and the diagonal is charged by edit cost rather
than by that count.

**Falsification gates (kernel-`decide` where expressible; all must be green before
any 11B statement freezes).** G1 subgraph deletion creates induced copies; G2 a
single pair recolor creates copies, with exact ordered-tuple edit accounting; G3 no
spare palette (the path pattern requires both symmetric palettes; asymmetric palettes
are never realized by graph adapters); G4 a planted within-cell copy is invisible to
transversal counting; G5 unary-only rare profile — removal achievable only by unary
edits; G6 rare loop profile with constant off-diagonal data — loop edits belong to
the profile layer; G7 a swap-inconsistent palette assignment is realized by no model;
G8 nullary incompatibility forces count zero unconditionally; G9 scope degeneracies
(hosts with fewer than three vertices; the meaningful empty-host instance under the
`≤` endpoint; duplicate patterns; the empty family; an infinite constant family).

**Feasibility gate (the 11A→11B checkpoint).** 11B begins only when: the diagonal
increments and bounds are proved; the TRANSVERSALIZATION certificate above is proved (or
the repeated-cell original-copy lower bound is supplied in its place) and the
all-cells-distinct stratum counting statement is proved with explicit errors; the
profile/loop gates are green; an actual pattern-independent SINGLE-representative system
is constructed with its size guarantee, its per-pair uniformity for distinct coarse cells,
and its aggregate-only deviation bound; one uniform lower-bound certificate covers the
counted stratum on those representatives in both palette orientations; nothing depends on the family index type; the explicit
constants are viable; and the selection's union bound introduces no hidden dependence
of the strong-witness tolerance on the fine-part bound. The exact modulus freezes
only after the surgery primitives' edit formulas AND their composition into the total
relative aggregate-edit bound are proved — if that composition needs
cleaning-specific facts, the freeze is delayed rather than constants guessed.

**Checkpoint status (2026-07-19): re-scope required; aggregate proposal not yet
validated.** The 11A units are landed and sound, but the gate is NOT passed: the
current parameter hierarchy cannot close uniformly using the available fixed-gap
witness bound together with the per-pair density-closeness requirement
(`deviant_condition_forces_gap_lt` proves the necessary inequality at a realized
coarse complexity; `exists_selection_schedule` shows the uniformity half alone is
schedulable). The candidate re-scope — an aggregate deviant-cost clause consumed only
in the edit budget — carries two open mathematical obligations before any 11B unit
may land: (1) the conditioned cost bound, now proved abstractly
(`exists_piFinset_forall_not_mem_bad_cost_le`, factor `1/(1−σ)`, sharpness test
attaining it) with the `6·K` role/palette multiplicity bounded in
`sum_selEvent_deviantMass_le` and the `24K`/`48K` constants composed in prose from
the proved generic lemmas (not packaged as one relational theorem); and
(2) **role consistency** — the
cleaner assigns one palette per coarse block pair while a placement may realize it
through any of six representative role pairs, and without per-pair closeness those
role pairs can have disjoint palette supports (gate G10), so a role-independent
rounding certificate (every realizable palette positively dense on the representative
boxes of every placement, and at least one such palette available) must be proved or
refuted before choosing between a complexity-dependent/scheduled-gap strong witness
and a stronger one-subset-per-cell lemma with self-regularity. The Unit 7/8 theorems
stay as sound conditional results; the frozen cleaning rule is amended only after one
route proves both the freeness certificate and the aggregate edit bound.

**Route decision (2026-07-20): checkpoint signed off as re-scope; route (b) chosen —
the one-subset-per-cell route. 11B remains closed.** Gate G10 killed the aggregate-cost
cleaner in its role-indexed form, and the role-indexed conditional theorems stay as
sound diagnostics (G10 is permanent: it records why that route cannot drive a
role-independent cleaner without density coherence). Between the two candidate
routes, the scheduled-gap alternative (a) was REJECTED for a new termination problem:
with permitted gap `D(k)` at complexity `k`, bounded energy proves termination only
when the forced increments along the complexity recurrence `kᵢ₊₁ ≈ monoStepBound E kᵢ`
have partial sum exceeding `1`, and the required `D(k)` shrinks polynomially in an
explosively growing `k` — positivity of every `D(k)` does not preclude summability,
so without that numerical termination certificate route (a) is another prospective
circularity, not a solution. Route (b) matches the published architecture
(Conlon–Fox survey, arXiv:1211.3487, §3.1, Lemmas 3.2–3.3; self-regular subsets as
in its Lemmas 3.6–3.7): ONE representative subset `W C` per coarse cell, every
ordered pair `(W C, W D)` regular INCLUDING self-pairs, only aggregate closeness
exceptions, and every placement consulting the same density table `d(W C, W D)` —
which removes G10 structurally. (**The self-pair clause is SUPERSEDED by the
2026-07-26 re-freeze below**: gate G-U5 refutes it for directed relations. What
removes G10 is the *one representative per cell shared by every role*, which the
re-freeze keeps; self-regularity was never what removed it.)

**Route (b) ladder — RE-FROZEN 2026-07-26 (option (b): preserve arbitrary directed
binary relations).** The 2026-07-20 ladder is superseded: its step 1 (self-regular
subsets) is FALSE in the directed setting (gate G-U5, correction recorded below), and its
step 5 consumed repeated coarse cells. Restricting to symmetric palettes was rejected as
abandoning the scope the relational API was built for. The replacement, frozen in order;
no `Recolor.lean` and no cleaning until step 5 composes:

1. *Docs-only route re-freeze* (this entry).
2. *Transversalization gate* (**inserted 2026-07-26 after review; it PRECEDES selection
   because its solution may require clone or proxy coarse cells, which would change the
   representative event index**): prove that the proposed diagonal rounding makes every
   surviving induced pattern admit a distinct-coarse-cell realization, or else supply a
   separate original-copy lower bound for repeated-cell realizations. Until this has a
   credible statement, the retirement of repeated-cell counting is PROVISIONAL — an edit
   bound on `C × C` changes which pattern a within-cell triple induces but does not stop
   it inducing one (gate G4).
3. *Off-diagonal representative selection*: ONE candidate fine cell `W C` per large
   coarse cell — **not** three role-indexed choices — with (i) `W C ⊆ C` and a linear
   size floor in multiplication form; (ii) `(W C, W D)` uniform for every palette for
   every ordered pair with **`C ≠ D`** — self-pairs are neither required nor provided;
   (iii) an AGGREGATE off-diagonal density-deviation bound, never a per-pair closeness
   requirement, consumed through `Finite/WeightedChoice.lean`. The simultaneous union
   bound conditions on all off-diagonal uniformity events and **excludes `C = D` from the
   event index**. The same `W C` serves every pattern role, which is what removes G10's
   role-consistency failure structurally.
4. *Diagonal surgery calculus*: the aggregate EDIT cost of recoloring all within-cell
   tuples, derived from `Σ_C |C|² ≤ m·|V|` with `m` the maximum cell size inherited from
   the bounded-cell equipartition seed, under the frozen per-symbol weighting of
   `relativeAggregateEdit`. Kept SEPARATE from `Relational/DiagonalGate.lean`, which
   controls counts, not edit cost.
5. *Transversal rounding certificate*: consumes only triples of DISTINCT coarse cells,
   through the existing three-vertex transversal counting APIs on the `W C`. The abstract
   freeness certificate and the aggregate edit inequality are proved BEFORE `Recolor.lean`
   begins.
6. *Only after that succeeds*: the cleaning construction, the removal modulus, and 11B.

**Hard stops (permanent).** No self-uniformity assumption anywhere; no role-indexed
representatives; no per-pair density-closeness requirement; no tolerance depending on the
produced fine complexity.

**What carries over.** The slicing/inheritance API (`Graph/UniformSlicing.lean`) stays as
proved infrastructure for size trimming. The piece supplier, density buckets, multicolor
Ramsey extraction, and union theorems remain valid and are retained for a later
explicitly symmetric self-regular-subset theorem; they are **no longer Phase 11
blockers**.


**Route (b) step 1 correction (2026-07-26 review): the frozen self-regular-subset
statement is FALSE for arbitrary directed relations, and step 1 as specified above does
not compose.** Two independently valid units do not join:
`exists_bucketAligned_subfamily` (`Finite/DensityBuckets.lean`) aligns a FORWARD density
class and a REVERSE class, while `isUniformPair_self_union` (`Graph/UniformUnion.lean`)
requires ONE common center `d` for every ordered pair of distinct pieces. Gate G-U3
already recorded that the two orientations need not agree.

The counterexample is decisive, not technical. For the strict order `<` on any linearly
ordered `W` with `|W| ≥ 2`, `d(W, W) = (|W| − 1)/(2|W|) ≤ 1/2`, while the lower and upper
halves are `1/4`-large with density `1`; so `(W, W)` is not `1/4`-uniform and NO
positive-linear-size self-uniform subset exists. With singleton pieces the forward class
is `1` and the reverse class is `0`: Ramsey alignment succeeds and the union theorem
still cannot be instantiated. Permanent gate **G-U5** (`Graph/UniformUnion.lean`) records
this on `Fin 4`, with a `Fin 8` instance showing the gap does not close as the host grows.

What remains valid and useful: the piece supplier, the density buckets, the multicolor
Ramsey extraction, and the union theorems. What fails is only their proposed DIRECTED
self-union composition. The Conlon–Fox Lemma 3.6 route is an undirected/symmetric
argument and does not extend to arbitrary directed palettes in its present form.

**Scope decision TAKEN (2026-07-26): option (b).** Arbitrary directed binary relations
are preserved and Phase 11 is redesigned around transversal counting plus separately
charged diagonal cells; restricting to symmetric palettes was rejected as abandoning the
scope the relational API was built to support. `11B` stays closed pending BOTH the
transversalization gate (ladder step 2, which precedes representative selection) and the
transversal rounding certificate (ladder step 5).
The two options as they were weighed:

- *(a) Symmetric restriction* — an explicitly symmetry-restricted self-regular-subset
  theorem for symmetric relation families, where the two orientation classes coincide and
  the existing composition goes through unchanged.
- *(b) Directed redesign* — for arbitrary binary relational structures, drop the
  `(W_C, W_C)` self-regularity requirement and rebuild around transversal counting with
  separately charged diagonal cells, likely reusing `Relational/DiagonalGate.lean`.

`11B` and `Unit 7` stay closed pending those gates.

**Supplier checkpoint (2026-07-22): statement frozen; NOT provable from the current
API — stopped for review.** The route (b) step-1 assembly is NOT one commit: before
the self-regular-subset summit, the piece supplier must exist. Delivered: (1) the
abstract greedy/independent-set substrate with EXPLICIT unweighted counting
hypotheses (`Finite/IndependentSet.lean` — symmetrized bad-neighborhoods, the greedy
`1/(D+1)` core, the Markov half, and the `1/(2(D+1))` summit; the bad-degree total
carries the `2·K` palette/orientation factor); (2) the supplier obligation frozen as
`PieceSupplierStatement` (`Graph/PieceSupplier.lean`): pairwise-disjoint EQUAL-size
pieces, every ordered distinct pair `τ`-uniform for every relation, a linear mass
floor, with the retention floor `κ` and threshold `N₀` depending on `(K, t, τ)` only
— fixed before any partition, no inequality letting `τ` depend on its own output
complexity. Feasibility finding, why the current API cannot prove it: (i) the
diagonal-palette regularity ladder controls bad pairs by WEIGHTED mass `|C|·|D|`
with no size control, and weighted mass does not bound the unweighted bad-pair
count the extraction consumes — gate G-S1 (one heavy cell, seven unit cells, all
pairs bad) passes a `τ = 3/49` regularity-style mass test while every
pairwise-clean subfamily is a singleton; (ii) the available fine candidate cells
retain only a `1/(2q)` fraction of their coarse cell with `q` the OUTPUT fine-part
bound, so trimming plus slicing would need a supplier tolerance `≤ target/(2q)` —
recreating the circularity route (b) exists to avoid; (iii) `Graph/Bridge.lean`
produces an `ε`-regular refinement AND a separate almost-refining equipartition,
explicitly NOT one partition simultaneously regular and equitable
("equitabilisation inside the increment loop" is deferred there), and transferring
uniformity from regular cells to equitable cells again retains only
output-complexity-dependent fractions; mathlib's equitable Szemerédi is
single-relation and symmetric, unusable for `K` directed palettes. The missing
mathematics is an equitable/multi-relation regularity supplier or a nontrivial use
of the almost-refining equipartition — not a small finite combinatorics lemma. The
self-regular-subset assembly and 11B stay closed pending review.

**Supplier route decision (2026-07-22 review): build the equitable finite-family
regularity supplier; the almost-refining route is rejected.** Rationale for the
choice: it yields equal/comparable cells BEFORE independent-set extraction (directly
neutralizing G-S1); its parameters are acyclic (internal tolerance `ρ` from
`(K, t, τ)`, then a host-independent part bound `B`, only then `κ` and `N₀`); after
an equitable output with cell sizes `m` or `m+1`, trimming every selected cell to
`m` retains at least half, so slicing needs only `2ρ ≤ τ` — no output-complexity
factor; and it is ORDINARY off-diagonal regularity for finitely many directed
relations, not equitable strong regularity (that deferral stands). Mathlib's
`Regularity/Chunk`, `Increment`, and `Lemma` provide the Apache-compatible
architecture to adapt, with attribution, from one symmetric graph to a finite
directed family. The almost-refining route is rejected because its uncovered-mass
bound is roughly `#Q · ⌊|A|/r⌋`, so many equitable cells inside regular parents
require `r` to dominate the output complexity `#Q`, and uniformity transfer then
retains fractions around `1/r` — the same circularity in different clothing, absent
a new fixed-fraction containment theorem. Implementation sequence (frozen; the
single-relation-per-step design and the deferred final bound are the 2026-07-24
hardening): (1) the `t = 0` repair and the placeholder-policy resolution; (2) generic
finite-family surfaces in `Graph/` — `IsFamilyRegular Rk ε P := ∀ k,
IsRegularPartition (Rk k) ε P`, `familyEnergy` (sum; ceiling `K`), the **lifting
lemma** `familyEnergy_add_le_of_component` (a one-relation gain lifts to the family
sum, so the iteration resolves ONE offending relation per step), and the schedule in
SEPARATE provisional pieces — `familyInitialBound C ε l` (ε-dependent floor meeting
`C ≤ 4^(·)·ε⁵`, `C` the K-independent chunk constant), the **K-free** single-relation
`familyStepBound n`, and `familyRegularityBoundAux fuel initial` — with **no final
bound frozen**; (3) the equitable chunk adaptation for the ONE selected nonregular
relation (witness cuts over both ordered directions; equitabilise each parent chunk;
every new cell of size `m` or `m+1`; bounded discarded remainder; the numerical
condition `C ≤ 4^(#P)·ε⁵` met by `familyInitialBound`); (4) the one-step theorem
(nonregular equitable partition → bounded larger equipartition; the exact-refinement
`ε⁵` gain degrades to a RETAINED gain `c·ε⁵` with `c < 1` derived from the chunk
remainder, lifted to the family sum by the lifting lemma; ceiling `K`, quantitative
optimality irrelevant); (5) the iterate — freeze the fuel `⌈K/(c·ε⁵)⌉` (now that `c`
is proved) and the final bound
`familyRegularityBoundAux (fuel) (familyInitialBound C ρ l)`, yielding an
equipartition, `l ≤ #parts ≤ (that bound)`, family-`ρ`-regular; (6) discharge the
piece supplier (weighted-to-unweighted conversion via `m ≤ |C| ≤ m+1`;
`Finite/IndependentSet.lean`; trim `m+1` cells to `m`; slicing at fixed retention
`1/2`; `κ ≈ t/(2B)`; `N₀` making `m > 0`); (7) only then the self-regular-subset
assembly (buckets, Ramsey, union). Permanent tests must include `K = 0`, an
asymmetric relation, exact `m`/`m+1` trimming, the `t = 0` rejection (G-S2), and a
theorem-level check that `ρ` is defined before — and does not mention — the final
part-count bound. 11B and Unit 7 stay closed until the supplier theorem is actually
inhabited.

**Supplier constants frozen (2026-07-25 review, step 4 proved).** The numerical schedule
left open by steps 2–3 is now closed, and these values are frozen (changing them requires
an owner decision recorded here):

- `familyChunkThreshold = 100` — the K-independent threshold `C` that `familyInitialBound`
  is instantiated at. Its content, proved: at every part count at or above the floor,
  `100 · r ≤ ε⁵ · |C|` for every cell, where `r` is the per-witness-side chunk remainder.
- `familyChunkDensityError ε = ε / 2` — the density error `δ` charged for replacing a
  witness side by the chunks it contains.
- `familyRetainedFraction = 1 / 5` — the retained fraction `c`. **Uniform**: independent
  of the relation, the partition, the cells, the host, and `ε`. The proof delivers
  `9801/40000 ≈ 0.245`, so `1/5` is claimed with slack; the constants are robust, not
  tuned. A `c` depending on output complexity is the circularity this route rejects, so
  the uniformity is guarded by a permanent test.
- **The one-step gain is therefore `ε⁵/5`**: a non-family-regular equipartition admits a
  refinement that is again an equipartition, has exactly `familyStepBound #P.parts` parts,
  and gains `ε⁵/5` of family energy (`exists_familyEnergy_increment_equitable`).

**Step 5 proved (2026-07-25).** The fuel is `familyFuel K ε = ⌈5K/ε⁵⌉₊ = ⌈K/(c·ε⁵)⌉₊`,
from the family-energy ceiling `K` and the gain above, and the final part-count bound is
`familyRegularityBound K ε l = familyRegularityBoundAux (familyFuel K ε)
(familyInitialBound 100 ε l)` — host-independent, mentioning only `K`, `ε`, and `l`. The
summit `exists_familyRegular_equipartition` delivers, for `0 < ε ≤ 1`, an equipartition
that is `ε`-regular for every relation of the family with `l ≤ #parts ≤ familyRegularityBound
K ε l`.


Its host requirement is `familyRegularityBound K ε l ≤ #s` — room for the partition the
iteration actually produces, and nothing beyond it. No room is required for a further
step: the terminal fuel-zero argument contradicts the ceiling `K` using the energy gain
alone, which carries no host hypothesis. That is the `N₀` obligation step 6 must meet; it
is stated, never hidden, and a permanent test records both that it fails on small hosts
and that the signature has not been strengthened. No tower-type claim is made or implied.

**Step 6 proved (2026-07-25): the piece supplier is inhabited.** The obligation frozen
at the 2026-07-22 checkpoint — for every palette count `K`, target `t` with **`0 < t`**,
and tolerance `τ > 0`, a retention floor `κ > 0` and a host threshold `N₀` depending on
`(K, t, τ)` ONLY, such that every host `A` with `N₀ ≤ |A|` admits a common size `m > 0`
and pieces with `IsPieceFamily Rk A τ m P` and the mass floor `κ·|A| ≤ t·m` — is proved
(`Graph/PieceExtraction.lean`, `Graph/PieceSchedule.lean`). The schedule, frozen:

- `supplierTolerance K t τ = min (τ/2) (1/(64(K+1)t))` — the internal `ρ`, from
  `(K, t, τ)` only. It does NOT mention the part-count bound; the bound is defined from
  it, and the reverse dependency is the circularity route (b) exists to avoid. The factor
  `64(K+1)t` is DERIVED: it is what makes `16Kρn ≤ n/(4t)` in the independent-set
  estimate.
- `supplierParts t = 4t` — the requested part count, which is what keeps the
  natural-number division `n/(2t)` in the degree budget from losing more than half.
- `supplierBound K t τ = familyRegularityBound K ρ (4t)`, `supplierThreshold = that
  bound`, `supplierRetention = t/(2·supplierBound)`.

What defeats gate **G-S1**: the equipartition's `m ≤ |C| ≤ m+1 ≤ 2m` converts weighted
bad mass to an unweighted bad-pair count (`|F| ≤ 4ρn²`), which is exactly the step the
gate shows is false without equal sizes. Trimming every selected cell to `m` retains at
least half, so slicing costs only the factor `2` (`2ρ ≤ τ`) — no output-complexity
factor anywhere. Gate **G-S2** stays permanent: `0 < t` is required, and the zero-target
instance remains false.

Still closed: the self-regular-subset assembly (route (b) step 1), 11B, and Unit 7.

**Non-goals.** Patterns on carriers other than `Fin 3` (even two-vertex removal);
languages varying after `ε` or moduli depending on the family (the language is fixed
before `ε`; the family is quantified after `ε` and may be arbitrary);
property-testing formulations; arity `> 2` or hypergraph removal; quantitative
optimality of the modulus; equitable strong regularity (stays deferred — this route
avoids it); deletion-only edits; box-relative removal; computable cleaning.

**Provenance.** The route adapts the Lemma 3.6 self-regular-subset construction of
the Conlon–Fox survey (arXiv:1211.3487, §§3.1–3.2), together with its Lemma 3.2
representative-set architecture, to directed finite binary palettes and three-vertex
induced removal (the original argument being Alon–Fischer–Krivelevich–Szegedy). Both
are now cited in `PROVENANCE.md` — with the precise scope map and explicit
NON-formalized items: the strong cylinder lemma (their 3.5), the quantitative bounds
of their 3.6–3.9 (the piece supplier here follows the weaker
regularity-plus-independent-set route, so no tower-type bound is claimed), their 3.7
partition, arbitrary-size counting, their Theorem 3.1, and infinite removal — and in
the route (b) unit docstrings. Mathlib is the architectural source only for the
reused regularity machinery already credited.
