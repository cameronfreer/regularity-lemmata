# A reader's guide to RegularityLemmata

This guide is written for a mathematician who wants to know what the library proves and how
to reuse it, and only secondarily how the Lean is organized. It inventories what exists as of
the release named in each section; it designs nothing. Conventions are in
[`ARCHITECTURE.md`](../ARCHITECTURE.md), sources in [`PROVENANCE.md`](../PROVENANCE.md), and
the theorem statements themselves are the authority whenever this text is coarser than they are.

Every declaration named below is reachable from `import RegularityLemmata` (the public root)
unless it is marked as living under the gates umbrella (§ Open campaigns). Generated pages for
every module live at <https://cameronfreer.github.io/regularity-lemmata/docs/>: `latest/` follows the newest release, `main/` is the most recently
published documentation snapshot of `main` (the workflow runs on releases and on manual
dispatch, not on every push), and a module `Dir/File` is at
`docs/<version>/RegularityLemmata/Dir/File.html`, with declaration search on each version's
`search.html`. Links in this guide point at the **v0.13.0** pages for current material (every
anchor verified against the published pages); the sections "Additions released in v0.13.0" and
"Additions released in v0.12.0" use source links pinned to their release tags. Where a curated
facade bundles a stack, the facade is named, because importing it is the advertised way in.

## Contents

- [Start here, by task](#start-here-by-task)
- [House vocabulary](#house-vocabulary)
- [What can I reuse, by release?](#what-can-i-reuse-by-release)
- [Additions released in v0.13.0](#additions-released-in-v0130)
- [Additions released in v0.12.0](#additions-released-in-v0120)
- [Main theorems and entry points](#main-theorems-and-entry-points)
- [Part I. Counts, densities, edits, diagonals](#part-i-counts-densities-edits-diagonals)
- [Part II. Partitions, sampling, completion](#part-ii-partitions-sampling-completion)
- [Part III. Weighted kernels: two different outputs](#part-iii-weighted-kernels-two-different-outputs)
- [Part IV. Which counting and removal theorems exist](#part-iv-which-counting-and-removal-theorems-exist)
- [The five facades](#the-five-facades)
- [Independent tools](#independent-tools)
- [Open campaigns (not reusable yet)](#open-campaigns-not-reusable-yet)

## Start here, by task

- **I have a directed relation or a finite family of them and want a regular partition.**
  [`exists_regular_refinement`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Graph/Regularity.html#RegularityLemmata.exists_regular_refinement)
  for one relation; [`exists_familyRegular_equipartition`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Graph/EquitableFamilyRegularity.html#RegularityLemmata.exists_familyRegular_equipartition)
  for a family with an equitable output; [`exists_familyStrongWitness`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Graph/FamilyStrong.html#RegularityLemmata.exists_familyStrongWitness)
  for a strong (energy-gap) witness. Part IV.
- **I have a weighted matrix or kernel and want a low-complexity approximation.**
  [`rect_frieze_kannan_cutDiscrepancy`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Partition/RectKernelFriezeKannan.html#RegularityLemmata.rect_frieze_kannan_cutDiscrepancy)
  for a step partition, [`kernel_frieze_kannan_cutDecomposition`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Finite/RectKernelCutDecomposition.html#RegularityLemmata.kernel_frieze_kannan_cutDecomposition)
  for a sum of few rectangles; import `RegularityLemmata.Kernel`. Part III.
- **I want to count induced copies of a small pattern in a finite relational model.**
  Exact characterizations on two and three vertices, the three-vertex estimate against a strong
  witness, and counting from a cellwise approximation at any arity. Part IV.
- **I want to move pattern counts across a small edit of the model.**
  [`abs_homCountOn_sub_le_of_simple`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/UniformPatternCounts.html#RegularityLemmata.abs_homCountOn_sub_le_of_simple) and
  [`abs_injectiveHomCountOn_sub_le_of_simple`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/UniformPatternCounts.html#RegularityLemmata.abs_injectiveHomCountOn_sub_le_of_simple) for homomorphism
  counts of a simple pattern (nullary agreement only; the all-homomorphism form keeps the
  collision term), [`abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/UniformPatternCounts.html#RegularityLemmata.abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement)
  for induced counts of any pattern, which additionally needs diagonal agreement. Part IV.
- **I want to approximate a finite relational model by an indivisible one with a bounded part count.**
  [`exists_equitable_isIndivisibleFor`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/DisplacedTransport.html#RegularityLemmata.exists_equitable_isIndivisibleFor): one equipartition with a
  requested number of parts and one model for all symbols, its edit cost the majority-rounding
  cost at the old partition ([`editDistance_majorityRound_le`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/MajorityAssembly.html#RegularityLemmata.editDistance_majorityRound_le))
  plus a displacement term; for arbitrary coordinate partitions,
  [`editDistance_majorityRound_coordinateJoin_le`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Relational/CoordinatePartitionRounding.html#RegularityLemmata.editDistance_majorityRound_coordinateJoin_le)
  charges each coordinate in its own partition through the partition defect
  ([`partitionDefect_eq_add_refinementVariance`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Partition/PartitionDefect.html#RegularityLemmata.partitionDefect_eq_add_refinementVariance)). Part IV; import
  `RegularityLemmata.RelationalApproximation`.
- **I want equal-size blocks on which given sets keep their density.**
  [`exists_balanced_slicing`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Partition/BalancedSlicing.html#RegularityLemmata.exists_balanced_slicing) and, since v0.12.0, its
  named-parameter wrapper [`exists_balanced_slicing_of_threshold`](https://cameronfreer.github.io/regularity-lemmata/docs/v0.13.0/RegularityLemmata/Partition/SlicingThreshold.html#RegularityLemmata.exists_balanced_slicing_of_threshold). Part II.
- **I want to move between an ordinary graph or hypergraph and this library's objects.**
  The adapters `Relational/GraphAdapter`, `Relational/HypergraphAdapters`, `Relational/GraphCounting`,
  and `Graph/RemovalBridge` (the one removal theorem, mathlib's). Part IV.
- **I only need a finite Ramsey theorem, a forecaster, or density buckets.** Independent tools.

## House vocabulary

- **Summit.** A major theorem whose constants are visible in its statement, so it can be
  instantiated and its bounds inspected. The main-theorem table below lists them; two of its
  rows (balanced slicing, indivisible approximation) are *entry points* rather than regularity
  theorems, because the first is a sampling theorem and the second takes its partition as input.
- **Gate.** A module that keeps counterexamples, impossibility results, and feasibility probes
  machine-checked, so that a rejected interface cannot be reopened silently. Gates carry
  identifiers (`G1`, `G-S1`, `G-H2a`, …). The word is also used for the review process: a
  statement passes a review-and-falsification gate before its API freezes.
- **Gates umbrella.** The second library root, `RegularityLemmataGates`: probe, obstruction, and
  feasibility modules of in-progress campaigns. Same namespace, same proof and axiom gates, but
  the public root does not import them. What separates the two roots is role, not rigour.
- **Facade.** A module that imports a curated stack and documents it, defining nothing. There
  are five: `Kernel`, `FiniteSetSystems`, `RelationalApproximation`, `FiniteRamsey`,
  `ProductSpaces`.
- **Seam.** A deliberate interface boundary where a quantity is *derived* on one side and
  *consumed* as a hypothesis on the other, so neither side needs the other's machinery. The
  aggregate-to-per-event conversion in `Finite/WeightedChoiceBudget` and the separate left and
  right part counts of the rectangular Frieze–Kannan iteration are the two named seams.
- **Race.** An inequality between a polynomial event count and a geometric per-event failure
  fraction, discharged beyond an explicit host threshold; the sampling layer runs a constant-count
  race and a linear-count race.
- **Guard-free.** Densities and averages are `0` on an empty denominator through real division
  `x / 0 = 0`, and definitions carry no `if`-guards. Positivity or nonemptiness is assumed only
  where it is genuinely needed (complement identities, cancelling a mass), never categorically.
  A recurring consequence: a nonempty set can have zero mass, so positive-mass hypotheses are
  stated as `0 < finsetMass w A`, not as nonemptiness.
- **Diagonal separation.** Ordered counts over all tuples (diagonals included) and counts of
  injective tuples are separate APIs with separate names, and both are global counts. Removal
  arguments use the injective count. The conversion between the two is explicit: the collision
  mass is at most `(k choose 2)·|s|^(k−1)`, one ambient power of the host size below the count,
  so the `|s|^k` and falling-factorial normalizations differ by a bounded additive term.

## What can I reuse, by release?

| Release | Reusable output (entry points) |
|---|---|
| v0.1.0 | Graph-side regularity engine and the binary-palette relational regularity: `exists_regular_refinement`, `exists_binaryPalette_regular_refinement`, strong (energy-gap) witnesses, the three-vertex induced counting theorem for patterns on `Fin 3`, triadic polyad regularization and deletion-only approximation, the relational substrate with exact finite-model counts. |
| v0.2.0 | Rectangular weighted-kernel stack (`Kernel` facade): stepping over independent partitions, energy with the parallel-axis identity, cut discrepancy with contraction constant 1. Balanced slicing `exists_balanced_slicing` with leftover and chunk absorption. Heterogeneous homogeneity `IsHomogeneousPair`, `IsHomogeneousCell`. Relational approximation (`RelationalApproximation` facade): indivisibility, `CellwiseEditBound`, majority rounding. Equitable family regularity with a multiple-of-three seed; piece supplier. |
| v0.3.0 | Rectangular Frieze–Kannan step-partition summit `rect_frieze_kannan_cutDiscrepancy` with separate left and right part bounds; guard-free averages and almost-constancy; slicing thresholds and races, average slicing, common blocks. |
| v0.4.0 | Complete heterogeneous homogeneity API including `AreHomogeneousPartitions`; the binary finite-model adapter; the `FiniteSetSystems` facade (relation fibers, trace families over Mathlib's VC dimension, support-sensitive Sauer–Shelah). |
| v0.5.0 | Binary-tree Ramsey layer (`FiniteRamsey` facade): the additive two-colour subtree theorem. Heterogeneous weighted product boxes. |
| v0.6.0 | The heterogeneous weighted-box stack complete (`ProductSpaces` facade): coordinate splits, box unions with symmetric-difference error, box partitions. |
| v0.7.0 | Approximation-to-counting complete: the arity-generic diagonal gate, quotient counting, count transfer across an edit, the aggregation bridge, and the composite theorem from a cellwise approximation to an induced count. Analytic homogeneity. |
| v0.8.0 | The Hedge forecaster and its regret bound `hedge_regret`. |
| v0.9.0 | Multicolour tree Ramsey `binaryTreeRamsey_proper` and its equal-height form. |
| v0.10.0 | Predecessor-ceiling bucket closeness `le_add_of_ceil_div_pred_eq`. |
| v0.11.0 | The cut-matrix decomposition `kernel_frieze_kannan_cutDecomposition` and the partition-free cut norm; three compiled examples under `examples/`; this guide, the generated documentation, and the consumer fixture. |
| v0.12.0 | Sharp assignment extension counts, uniform induced and homomorphism transfers with their diagonal/nullary/collision hypotheses, the immediate-child to proper-embedding bridge, named-parameter slicing, and the compiled three-vertex composition. |
| v0.13.0 | The global-approximation stack: majority-rounding cost from summed coordinate defects (`editDistance_majorityRound_le`), the partition defect with the exact refinement variance identity and the join bound for arbitrary coordinate partitions, representative maps with displaced-coordinate transport and the equitable composition `exists_equitable_isIndivisibleFor`, five compiled consumers including the counting recipe with its diagonal boundary, and the environment-based public inventory. |

The version in the root module (`RegularityLemmata.version`) and the Git tag agree; pin a
tag, because `main` moves between tags.

## Additions released in v0.13.0

These additions were merged after v0.12.0 and are included in v0.13.0. Source links below
are pinned to the `v0.13.0` tag.

- Majority rounding at any partition, costed by summed coordinate defects:
  [`Relational/MajorityAssembly.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/RegularityLemmata/Relational/MajorityAssembly.lean)
  (`editDistance_majorityRound_le`, the labelled-fibre adapter `labelPartition`), on the
  substrate `Finite/SectionDefect` (inclusive decency) and `Finite/ProductHybrid` (the
  prefix-swap identity and the minority bound over heterogeneous coordinate types).
- The partition defect and the exact refinement variance identity
  ([`Partition/PartitionDefect.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/RegularityLemmata/Partition/PartitionDefect.lean)),
  the join of coordinate partitions (`coordinateJoin`, `Partition/Basic`), and the majority
  bound for arbitrary coordinate partitions
  ([`Relational/CoordinatePartitionRounding.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/RegularityLemmata/Relational/CoordinatePartitionRounding.lean)).
- Representative maps with an explicit displaced set, the one-way bridges to the
  almost-refinement charge, the free-part equitable construction
  ([`Partition/RepresentativeMap.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/RegularityLemmata/Partition/RepresentativeMap.lean)),
  and displaced-coordinate transport with the composition `exists_equitable_isIndivisibleFor`
  ([`Relational/DisplacedTransport.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/RegularityLemmata/Relational/DisplacedTransport.lean)).
- Five compiled consumers under `examples/`, including
  [`GlobalApproximationCounting.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/examples/GlobalApproximationCounting.lean):
  homomorphism-count transfer from the global approximation with constants displayed, and the
  induced-count boundary (diagonal agreement is required and rounding does not supply it).
- The environment-based public inventory (`lake exe public_inventory`).

## Additions released in v0.12.0

These additions were merged after v0.11.0 and are included in v0.12.0. Source links below
are pinned to the `v0.12.0` tag.

- [`exists_balanced_slicing_of_threshold`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.12.0/RegularityLemmata/Partition/SlicingThreshold.lean)
  and `exists_balanced_slicing_of_threshold_self`: balanced slicing
  at the named parameters with every side condition discharged; the zero-block case documented,
  the nonvacuous specialization at `n = |A|`, `μ ≤ 1`.
- [`examples/CompositionCertificates.lean`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.12.0/examples/CompositionCertificates.lean):
  the compatibility check and the prescribed-error endpoint chaining strong-witness existence
  with three-vertex counting.
- Two approved, unimplemented specifications: `docs/design/repeated-cell-counting.md` and
  `docs/design/retaining-completion.md`; no declaration exists for either yet.
- The non-implications list (Part IV) and the wording corrections of the proper-embedding
  documentation.
- Uniform counting transfers: see [the exact hypotheses and names](uniform-pattern-counts.md).
- Tree conventions: see [the one-way bridge](tree-embedding-conventions.md).

## Main theorems and entry points

The declarations to reach for, and the module each lives in. Every bound is visible in the
statement. The last rows are entry points rather than regularity theorems: balanced slicing is
a sampling theorem; `exists_isIndivisibleFor_of_isHomogeneousCell` takes its partition as an
input; the equitable composition `exists_equitable_isIndivisibleFor` takes an old partition as
input and **constructs** a new equipartition (with a requested part count) as output; and the
transfer theorems take the edit bound as an input.

| Theorem | Declaration | Module |
| --- | --- | --- |
| Regular refinement of a directed relation | `exists_regular_refinement` | `Graph.Regularity` |
| Equitable regularity for a finite family, with a multiple-of-three part count | `exists_familyRegular_equipartition_triple` | `Graph.TripleSeed` |
| Large equal-size regular pieces | `exists_pieceFamily` | `Graph.PieceSchedule` |
| Strong (energy-gap) regularity for a finite family, simultaneously in every relation | `exists_familyStrongWitness` | `Graph.FamilyStrong` |
| Boundedly-colored coloring of `j`-sets with small bad mass, any observable | `exists_goodPolyadColoring` | `Hypergraph.PolyadIncrement` |
| Boundedly-colored pair coloring with small bad mass | `exists_goodColoring` | `Hypergraph.TriadIncrement` |
| Deletion-only triadic approximation, locally disc-regular | `exists_triadic_regular_approximation` | `Hypergraph.TriadCleanup` |
| Simultaneous palette regularity, host-independent bound | `exists_binaryPalette_regular_refinement` | `Relational.BinaryRegularity` |
| Three-vertex induced counting against a strong palette witness | `BinaryPaletteStrongWitness.abs_transversalInducedCount_sub_coarseInducedEstimate_le` | `Relational.BinaryStrongCounting` |
| Rectangular Frieze–Kannan step partition: separate left and right part bounds, uniform cut discrepancy | `rect_frieze_kannan_cutDiscrepancy` | `Partition.RectKernelFriezeKannan` |
| Cut-matrix decomposition: at most `⌈1/ε²⌉₊` weighted rectangles, coefficients at most `1/ε`, residual cut norm at most `ε · mass` | `kernel_frieze_kannan_cutDecomposition` | `Finite.RectKernelCutDecomposition` |
| Balanced slicing: exact equal-size blocks, simultaneously typical for a trace family | `exists_balanced_slicing` | `Partition.BalancedSlicing` |
| Indivisible approximation from cellwise homogeneity, with exact nullary compatibility | `exists_isIndivisibleFor_of_isHomogeneousCell` | `Relational.CellwiseEdit` |
| Majority-rounding cost from summed coordinate defects, `(n+1)·|s|^(n+1)·(2θ + γ/2 + λ/2)` | `editDistance_majorityRound_le` | `Relational.MajorityAssembly` |
| Exact refinement variance identity of the partition defect, with monotonicity | `partitionDefect_eq_add_refinementVariance` | `Partition.PartitionDefect` |
| Majority rounding at the join of arbitrary coordinate partitions, each coordinate charged in its own partition | `editDistance_majorityRound_coordinateJoin_le` | `Relational.CoordinatePartitionRounding` |
| Equitable representative map with displacement at most `(#P.parts − 1)·⌊|s|/t⌋` | `exists_equitable_representativeMap` | `Partition.RepresentativeMap` |
| One equitable partition and one indivisible model for all symbols, with the combined edit bound | `exists_equitable_isIndivisibleFor` | `Relational.DisplacedTransport` |
| Homomorphism-count transfer for a simple pattern across an edit (nullary agreement; collision term retained) | `abs_homCountOn_sub_le_of_simple` | `Relational.UniformPatternCounts` |
| Induced-count transfer for any pattern across an edit, under diagonal and nullary agreement | `abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement` | `Relational.UniformPatternCounts` |

## Part I. Counts, densities, edits, diagonals

**Counting is exact and lives in `ℕ`; densities are real and guard-free.** A density is a count
divided by a support size, and the empty support has density `0` (`Finite/Density`,
`Finite/PairDensity`). The complement identity `d(p) + d(¬p) = 1` is *false* on the empty
support and is stated only under nonemptiness. Density is not monotone under enlarging the
support, and no such lemma is offered; counts are monotone, and the library says so with
separate names.

**Heterogeneous from the start.** A binary relation `R : α → β → Prop` between two carriers,
with rectangle counts `pairCount R A B` and densities `pairDensity R A B`; the box
`Fintype.piFinset A` over an arbitrary finite index type replaces `Fin k` wherever arity is
not the point (`Finite/Tuple`, `Finite/Density`). Averages `averageOn S φ` are one-variable,
guard-free, and every density is the average of an indicator (`Finite/Average`).

**Diagonals are a first-class quantity.** `Finite/Injective` counts injective tuples by the
falling factorial and bounds the non-injective ones: at most `(k choose 2)·|s|^(k−1)` of the
`|s|^k` tuples in a `k`-box collide, so the conversion between `n^k` and `(n)_k`
normalizations is additive with an explicit error. This is the fact behind every "global"
counting statement in Part IV.

**Edits.** Two relations disagree on an *edit set*; the edit distance is its raw count and the
relative edit its density (`Finite/Edit`). The house form of disagreement is `¬(R₁ x ↔ R₂ x)`,
which keeps everything decidable. Chains of edits add, and a full-box edit distance splits into
an injective part and a collision count.

**Homogeneity.** A rectangle is `ε`-homogeneous for `R` when its density is within `ε` of `0`
or `1` (`IsHomogeneousPair`, `Finite/HomogeneousPair`); the `n`-ary version on a cell box is
`IsHomogeneousCell`. Both predicates are instance-free and keep their symmetries on empty
rectangles. The analytic counterpart is Conant–Terry's almost-constancy
(`IsAlmostConstantOn`, `IsAlmostConstantPair`, `Finite/AlmostConstant`) with the separation
lemma outside almost-constant sets, and the `(δ, ε)`-homogeneous kernel predicate with
Proposition A.5 in both directions, each direction doubling the `δ`-constant parameter
(`Finite/AnalyticHomogeneous`).

**Set systems.** Fibers of a relation on a supplied finite support, trace families, and
support-sensitive Sauer–Shelah bounds over Mathlib's `Finset.vcDim`, through the
`FiniteSetSystems` facade. No parallel VC dimension is defined.

**Inequalities you will meet everywhere.** Cauchy–Schwarz in Engel form with nonnegative
denominators (`titu_three`, `engel_defect_lower`), the two- and three-factor perturbation
bounds, and the bilinear bound `abs_sum_bilinear_le` that makes the cut-norm contraction
constant `1` (`Finite/Inequalities`).

## Part II. Partitions, sampling, completion

**Partitions are Mathlib's `Finpartition`, and `Q ≤ P` means `Q` is finer.** The library adds
part unions, refinement on a part, predicate and cut refinements, and the parent reindexing
`sum_over_parents` (`Partition/Basic`). Within-cell splitting `refineBySplit` adds exactly one
part; equitable chunking is Mathlib's `equitabilise`, re-exported only where consumed
(`Partition/Equitable`).

**Energy.** The mass-weighted partition energy `Σ (|A||B|/|s|²) d(A,B)²`, diagonal blocks
included, is monotone under refinement (`energy_mono`, `Partition/Energy`), because block
energy is superadditive under disjoint covers (`Partition/BlockEnergy`). The *uniform* block
mean of `d²` is not monotone, and a three-element counterexample is kept in the tests.

**Almost refinement.** `AlmostRefinesAt Q P m` says each part of `P` has at most `m` elements
not covered by `Q`-parts inside it, exactly the shape Mathlib's `equitabilise` produces;
`AlmostRefines Q P ε` is its normalized form, additive under composition
(`Partition/AlmostRefines`). Compression by fiber type gives cellwise-constant relations with at
most `2^|D|` cells (`Partition/Fiber`).

**Sampling without probability.** Equal-size blocks of a finite set are encoded by
permutations, so "a random block" is a counting statement over `Fin n ≃ α`
(`Partition/EqualBlockEncoding`); the probabilistic method is the deterministic statement that
event cardinalities summing below `n!` leave a permutation avoiding all events
(`Partition/FiniteProbabilisticMethod`). Without-replacement concentration is proved by binomial
moments and double counting in `ℕ`, with no reals (`Partition/HypergeometricTail`), then
converted to a division-free geometric inequality (`Partition/HypergeometricGeometric`).
Polynomial trace counts are eventually beaten by geometric concentration, with explicit
thresholds (`Partition/PolyGeometricThreshold`, `Partition/ExplicitPolyGeometricThreshold`).
One permutation can be made to split every member of a finite family within prescribed
windows simultaneously (`Partition/SimultaneousSampling`), one-sided proportional windows are
upgraded to two-sided ones by closing the family under complements at cost a factor `2`
(`Partition/ProportionalTraceForm`, `Partition/TraceComplementClosure`), and the coupled tail
in `Partition/ActiveTraceSchedule` yields a genuine geometric factor at slack `t` with
exponent `t/8`. Transport to a parent subtype is lossless (`Partition/ParentSubtypeRekey`), and
the divisibility requirement is removed by sampling the first `m` blocks
(`Partition/PrefixBlockSampling`).

**The slicing summit.** `exists_balanced_slicing` (`Partition/BalancedSlicing`): a finite set
`A` is partitioned into blocks of *exact* size `s` plus a leftover of size `A.card % s`, so
that every test set of a finite family keeps its density within `β` on every block. Its one
quantitative hypothesis is a ratio inequality that the consumer discharges; the named
parameters `sliceBlockSize`, `sliceSlack`, `sliceThreshold` and the two races
(`slice_sampling_race`, `slice_sampling_race_linear`) discharge it beyond explicit host sizes
(`Partition/SlicingThreshold`). Since v0.12.0 (see
[Additions released in v0.12.0](#additions-released-in-v0120)), `exists_balanced_slicing_of_threshold`
packages the whole thing, so a consumer supplies the carrier, the family, `μ`, `ν`, a family-size
ceiling, and a host size beyond the threshold, and receives the blocks with every side condition
discharged. Averages of a `[0,1]`-valued family are controlled within
`2ν + (1+ν)β` (`exists_average_slicing`), and every piece of a partition can be sliced into
blocks of one common exact size (`exists_common_blocks`).

**Completion.** Equal-size blocks covering all but a small complement extend to an
equipartition with part sizes `s` or `s+1` when the leftover is at most the number of blocks,
and otherwise by splitting the leftover into near-equal chunks, one per block
(`exists_equipartition_absorb_leftover`, `exists_equipartition_absorb_chunks`,
`Partition/AbsorbLeftover`).

**Product boxes.** Boxes over a coordinate-indexed family of carriers with raw tuple weights,
product factorization as a theorem, coordinate splits, unions with symmetric-difference error,
and independent per-coordinate partitions, through the `ProductSpaces` facade.

## Part III. Weighted kernels: two different outputs

The `Kernel` facade is the import for this part. A **rectangular kernel** is a function
`f : X → Y → ℝ` on two possibly different carriers, each with raw nonnegative weights;
`rectSum f wX wY A B` is the primitive, and averages, restriction, and transpose (`op`) are
defined from it (`Finite/RectKernel`). Weights are never normalized: a probability is a ratio
formed at the point of use, guard-free. Nonnegativity of the weights is a hypothesis, stated
exactly where a mass is cancelled (`rectAverage · mass = rectSum` fails for signed weights,
`Partition/RectKernel`).

**The step-partition theorem.** Stepping `f` over a pair of *independent* partitions predicts
each rectangle sum by cell averages (`steppedRectSum`); the error against a test rectangle is
`rectError`, and its supremum over test rectangles is the cut discrepancy
`rectCutDiscrepancy` (`Partition/RectKernelCut`). Stepping contracts the cut norm with constant
`1`, not `2`. Energy against the partition pair obeys an exact parallel-axis identity under
refinement (`Partition/RectKernelEnergy`), and a witness rectangle with large error forces an
energy gain of order `ε²` times the mass. Iterating gives the rectangular Frieze–Kannan
summit `rect_frieze_kannan_cutDiscrepancy` (`Partition/RectKernelFriezeKannan`): a pair of
refinements with `#P ≤ #P₀·2^t` and `#Q ≤ #Q₀·2^t` *separately*, and uniform cut discrepancy
at most `ε` times the mass, after `t = O(ε⁻²)` rounds. The factor `4^t` appears only in the
same-carrier adapter that multiplies the two. The prediction it produces is a rectangle
combination with the *product* term count `#P·#Q`.

**The cut-matrix decomposition.** The same paper's second statement is a different reusable
output: `kernel_frieze_kannan_cutDecomposition` (`Finite/RectKernelCutDecomposition`) writes an
absolutely unit-bounded kernel as a sum of at most `⌈1/ε²⌉₊` weighted rectangle indicators
with coefficients of absolute value at most `1/ε`, plus a residual whose *partition-free* cut
norm (`rectCutNorm`, `Finite/RectKernelCutNorm`) is at most `ε` times the mass. It is produced
by a greedy residual iteration that records one rectangle per round and forms no partition, so
its term count is `O(ε⁻²)` rather than a product of part counts; the budget has no `+1`, and no
nonemptiness, positive-mass, or `ε ≤ 1` hypothesis is needed. The two summits meet on the
residual: the cut discrepancy of a partition pair is the cut norm of the stepped residual
(`rectCutDiscrepancy_eq_rectCutNorm_rectResidual`). Normalized and transposed forms are
corollaries.

Which to use: the step-partition theorem when the downstream argument needs a *partition* (to
count within cells, to refine further, to seed another iteration); the decomposition when it
needs *few terms* and a residual measured against nothing. Three compiled specializations under
`examples/` show the decomposition on an ordinary matrix, a weighted bipartite graph, and a
signed centred residual, importing only the `Kernel` facade.

**The unweighted graph versions** remain available: `frieze_kannan` and its seeded form on a
single vertex set with at most `4^(⌈1/ε²⌉+1)` parts (`Graph/FriezeKannan`), and the cut
deviation estimate against a regular partition with the diagonal term charged explicitly
(`Graph/CutNorm`).

## Part IV. Which counting and removal theorems exist

**Regularity engines (graphs and directed relations).** Uniformity of an ordered pair of
blocks is `≤ ε` (Mathlib's is strict), so failure produces a strict witness as *data*
(`Graph/Uniformity`). The Szemerédi-style summit `exists_regular_refinement` iterates an `ε⁵`
energy increment for `⌈1/ε⁵⌉` rounds with the `k·4^k` step bound (`Graph/Regularity`); the
diagonal-inclusive twin `exists_regularDiag_refinement` reuses the same fuel and bound
(`Graph/RegularityDiag`). Finite families of directed relations are handled simultaneously,
non-equitably as an exact refinement of any seed (`exists_familyRegular_refinement`) and
equitably with a host-independent bound (`exists_familyRegular_equipartition`, fuel
`⌈5K/ε⁵⌉₊`), including a multiple-of-three seed (`exists_familyRegular_equipartition_triple`).
Strong, energy-gap witnesses exist for one relation and for families (`exists_strongWitness`,
`exists_familyStrongWitness`), with typicality of coarse pairs by a second Markov step. The
bridge to Mathlib's regularity costs a factor `4` in `ε`, and the same-`ε` converse is false
(`Graph/Bridge`).

**Relational regularity is binary.** A finite relational language carries an arity bound
(`FiniteRelational`, arity `0` supported); models store Boolean relations and are computable;
transport (pullback, restriction, relabeling) is built before any counting
(`Relational/Language`, `Model`, `Transport`). Ordered counts include diagonals and are the
canonical first-order counts; injective counts are a separate API normalized by the falling
factorial (`Relational/Counts`). Edits are per-symbol primitives aggregated with unit weight per
symbol-tuple incidence (`Relational/Edit`). Regularity for a language of arity at most two
proceeds through the binary palette, which colours every ordered pair by every binary symbol
in both directions and every vertex by its unary and loop profile
(`Relational/BinaryPalette`); the summit `exists_binaryPalette_regular_refinement` is
simultaneously regular for every colour, with fuel independent of the palette size because
palette densities on a block form a probability vector (`binaryPaletteEnergy_le_one`). It
asserts nothing about symbols of arity greater than two.

**Counting theorems that exist.**

- *Exact two-vertex and three-vertex characterizations.* An induced embedding of a pattern on
  `Fin 2` or `Fin 3` is exactly a palette-colour pair or a directed triangle in three forward
  colour relations (`preservesAndReflects_iff_profiles_palettes`,
  `preservesAndReflects_three_iff`; `Relational/BinaryPattern`, `TwoVertexCounting`,
  `ThreeVertexCounting`).
- *Directed paths and triangles under uniformity.* Two-step path density within `6ε` of the
  product, and directed triangle counts within `7ε·|A||B||C|` of the product of three
  densities, with `7 = 1 + 2 + 4` derived term by term (`Graph/PathCounting`,
  `Graph/TriangleCounting`).
- *The quantitative induced counting theorem on `Fin 3`.* Against a strong witness, the induced
  count of a three-vertex pattern is within an explicit charge of the coarse step estimate:
  `10τ` for regularity (`7τ + 3τ`), `3η + 3δ/η²` for the density shift, and `3m|s|²` for the
  non-transversal triples (`Relational/BinaryStrongRegularityCharge`,
  `Relational/BinaryStrongCounting`, `Relational/DiagonalGate` — public despite its name).
- *Counting from a cellwise approximation, any arity, any fixed pattern.* Given a model `N`
  indivisible over a partition `Q`, nullary-compatible with `M`, and cellwise `ε`-close to it,
  the induced count of any `k`-pattern in `M` is within an explicit error of the quotient count
  of `N`: the sum over positive-arity symbols `R` of `k^(arity R)·ε·|s|^(arity R)`, times
  `|s|^(k−1)`, plus the diagonal charge `(k choose 2)·m·|s|^(k−1)` for parts of size at most
  `m` (`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_of_cellwiseEditBound`,
  `Relational/AggregationBridge`). No separate local-error coefficient is required. Majority
  rounding produces such an approximation from a homogeneous partition,
  with the exact edit identity `editDistance_majorityRound_eq_min` (`Relational/CellwiseEdit`).
- *Aggregating a supplied local estimate.* Separately, the aggregation bridge
  `abs_inducedEmbeddingCountOn_sub_sum_est_le` takes a caller-supplied estimate `est T` that is
  within `δ·vol T` of the induced count on every good transversal cell tuple `T`, together with
  an aggregate bad-pair mass at most `β·|s|²`, and returns the global count within
  `(δ + (k choose 2)·β)·|s|^k + (k choose 2)·m·|s|^(k−1)` of the sum of the estimates. The
  library computes no local coefficient `δ`; the arity-2 and arity-3 wrappers supply theirs.
- *Hypergraph precursors.* Ordered injective realizations of `r`-uniform hypergraphs
  (`orderedCount_eq`, `Hypergraph/Uniform`), polyad regularity local to a parent polyad after
  Nagle–Rödl–Schacht, an arity-generic `δ⁴` polyad energy increment
  (`exists_goodPolyadColoring`, `Hypergraph/PolyadIncrement`), and the deletion-only triadic
  regular approximation `exists_triadic_regular_approximation` (`Hypergraph/TriadCleanup`).

**Removal theorems that exist.** Exactly one: Mathlib's triangle removal lemma for simple
graphs, re-exported with the conversions between this library's counts and Mathlib's
(`Graph/RemovalBridge`). Nothing else in the library is a removal theorem.

**The boundary, stated plainly.**

1. The relational substrate supports arbitrary finite relational languages and exact counts.
2. Regularity and regularity-based counting assume arity at most two; the quantitative induced
   counting theorem treats patterns on `Fin 3`.
3. There is no general relational induced-removal theorem. The design record is
   `docs/design/induced-removal.md`; the gates that constrain it (deletion alone cannot
   remove induced copies; recolouring creates copies) are under the gates umbrella.
4. The triadic approximation is a precursor, not the Rödl–Schacht theorem.
5. Regularity-based counting for general fixed patterns and for arities above two, and
   general hypergraph removal, are outside the current API. Counting from a supplied cellwise
   approximation exists at every arity and for every fixed pattern (above). Deferred
   statements are recorded as prose, never as `Prop` placeholders.
6. The global approximation (majority rounding, then transport along an equitable
   representative map) supplies **homomorphism-count transfer** for simple patterns. The
   uniform **induced-count** corollary additionally requires diagonal agreement, which rounding
   does not guarantee: the compiled six-vertex counterexample in
   `examples/GlobalApproximationCounting.lean` meets every other hypothesis at the actual edit
   rate and violates the induced bound.

**Non-implications, stated once.** Each pair below names two things that sound alike and are
different theorems here; the contracts keep them apart, and no result of the first kind
should be read as the second.

- An equitable almost-refinement is not automatically regular: `AlmostRefines` controls
  uncovered mass, regularity controls densities on pairs of parts.
- A global exceptional-mass bound (a sum over bad pairs at most `β|s|²`) is not a bound inside
  every parent cell; the aggregation bridge consumes the global form only.
- Quotient counting over transversal placements is not an all-placement count formula: a
  placement putting two pattern vertices in one cell is charged, not evaluated; and repeated
  arguments inside one relation atom are a third, separate matter.
- A count-transfer theorem (counts within an explicit error of a quotient count) is not a
  removal theorem; the library has exactly one removal theorem, Mathlib's, re-exported.
- Completing a partition by enlarging existing blocks (the absorption theorems) is not the
  same as retaining prescribed exact-size blocks and partitioning the remainder; only the
  first exists.
- The step-partition theorem (a stepped prediction with product term count) and the cut-matrix
  decomposition (a bounded sum of rectangle indicators) are different outputs; both exist.
- Counting from a cellwise approximation is not producing that approximation: the library
  rounds a homogeneous partition to an indivisible model, but for general models it does not
  construct a homogeneous partition with host-independent size and tolerance guarantees (the
  discrete partition is trivially indivisible, and says nothing).
- A global approximation with small edit mass is not diagonal agreement: majority rounding can
  change loops and repeated-entry tuples, so the induced-count corollary is invoked only with
  its diagonal-agreement premise, never inferred from simplicity of the pattern.
- An embedding example that fails a stronger constraint (a tree embedding with the root moved
  or depth changed) shows what the structure allows; it is not a proof that no monochromatic
  embedding satisfies the stronger constraint, which would need a colouring counterexample.

## The five facades

Each facade imports a curated stack and defines nothing; every listed module remains directly
importable, and direct imports of a module are as advertised as the facade.

- `RegularityLemmata.Kernel`: the rectangular weighted-kernel layer (raw weights, kernels,
  relation and rectangle indicators, the partition-free cut norm, one-variable averages and
  almost-constancy, stepping, energy and the refinement-variance identity, cut discrepancy, the
  Frieze–Kannan step-partition theorem, and the cut-matrix decomposition). Three of the
  examples compile against this facade alone.
- `RegularityLemmata.FiniteSetSystems`: heterogeneous relation fibers, finite trace families,
  mathlib's VC dimension under restriction, support-sensitive Sauer–Shelah bounds, and
  polynomial bounded-subset estimates.
- `RegularityLemmata.RelationalApproximation`: homogeneous cells, finite relational models,
  indivisibility, cellwise edit bounds with the majority-rounding theorems, the edit calculus
  with count transfer, the approximation-to-counting aggregation bridge, and (since v0.13.0)
  the global-approximation stack: majority-rounding cost from summed coordinate defects, the
  partition defect with its refinement variance identity and the join bound, representative
  maps with displaced-coordinate transport, and the equitable composition.
- `RegularityLemmata.FiniteRamsey`: multicolour Ramsey for ordered-pair colourings, finite full
  binary trees as words, arbitrary-root subtree embeddings and their proper extensions, and the
  additive subtree theorems (two colours at host height `a + b + 1`, `m` colours at
  `(∑ tᵢ) + 1`, the equal-height form at `m·t + 1`).
- `RegularityLemmata.ProductSpaces`: raw weights and masses, boxes and their tuples, predicate
  mass and guard-free density, independent coordinate partitions with exact cell decompositions,
  finite unions with a weighted symmetric-difference error, and the coordinate-split adapter.

For the substrate rather than the theorems: `Finite.Tuple`, `Finite.Injective`, `Finite.Density`
for counting, densities, and edits; `Partition.Basic` and `Partition.BlockEnergy` for partitions
and weighted energy; `Relational.Language` for the finite relational layer.

## Areas at a glance

| Area | Public capability |
| --- | --- |
| **Finite foundations** | Tuple boxes, injective counts, densities, edits, homogeneous rectangles and `n`-index cell boxes, dependent coordinate splits, relation fibers and trace families with support-sensitive VC and Sauer–Shelah estimates, abstract weighted selection. |
| **Partitions and sampling** | Equitable refinements, weighted block energy, hypergeometric tails by exact binomial moments, balanced slicing, average-preserving slicing and common blocks with named thresholds and geometric races, leftover and chunk absorption into equipartitions. |
| **Weighted kernels** | Heterogeneous rectangular kernels with raw carrier weights: sums and averages, restriction, transpose, relation indicators, stepping over independent partitions, energy with the exact refinement-variance identity, residuals, cut discrepancy, the cut-norm contraction of stepping with constant 1, the partition-free cut norm, and the cut-matrix decomposition. |
| **Graphs** | Directed pair regularity, weak and strong regularity, equitable finite-family regularity, path and triangle counting, graph-removal bridges. |
| **Hypergraphs** | Uniform and colored vocabulary, copy counts, polyads and disc regularity, weak and edited triadic approximations. |
| **Relational structures** | Computable finite relational models, transports, counts, edits, binary-palette regularity, three-vertex induced counting, indivisibility with the quotient reading and exact nullary compatibility, cellwise edit bounds with a computable majority rounding whose box-level edit count is computed exactly. |
| **Adapters** | Bridges to mathlib's `SimpleGraph` and to this library's uniform and colored hypergraphs. |

## Independent tools

- **Finite Ramsey** (`FiniteRamsey` facade): multicolour Ramsey for ordered pairs by greedy
  pigeonhole with bound `(r+1)^(r·s+1)`, and the binary-tree subtree theorems: two colours at
  height `a + b + 1`, `m` colours in the additive form, embeddings with arbitrary root and
  preserved branch direction, proper embeddings mapping source leaves to target leaves. No lower bound is
  formalized, so no optimality is claimed.
- **Density buckets** (`Finite/DensityBuckets`): half-open buckets with a Ramsey extraction of
  a bucket-aligned subfamily, and the one-sided predecessor-ceiling closeness lemma.
- **Hedge** (`Finite/Hedge`): the multiplicative-weights forecaster with regret
  `log|ι|/η + ηT/2` for losses in `[0,1]` and any `η > 0`, over an arbitrary finite expert type.
- **Weighted choice** (`Finite/WeightedChoice`, `WeightedChoiceBudget`): selection under
  aggregate mass constraints with all constants exposed and no probability vocabulary.
- **Independent sets** (`Finite/IndependentSet`): greedy independent sets under a degree cap.

## Open campaigns (not reusable yet)

Modules under the gates umbrella record the state of the induced-removal campaign: the
transversalization obligation with the proof that no cleaning achieves it, the proxy selection
steps and the hierarchy gates, and the positivity gate for removal. They compile, they are
audited, and they are not API. Promotion out of the umbrella is a reviewed move of one import
line.
