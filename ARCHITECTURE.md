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
- **Relational induced removal**: fixed-pattern and finite-family induced removal over
  the binary-palette counting layer. The counting inputs — including the strong-witness
  counting theorems and the diagonal-cell gate — are complete (see the Phase 10
  section); removal receives its own statement freeze and falsification gates in a
  later phase.
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
deferred to a later phase — global removal additionally needs control of embeddings
whose vertices land in the same partition cell (an initial fine equipartition or an
explicit diagonal-cell error term), which gets its own freeze.

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
density-shift charge (`Relational/BinaryStrongRegularityCharge.lean`), the lifting
calculus (`Relational/StrongCountingLifting.lean`), and the transversal summit
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
