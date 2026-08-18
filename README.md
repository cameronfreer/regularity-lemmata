# RegularityLemmata

[![CI](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml/badge.svg)](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml)

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on [mathlib](https://github.com/leanprover-community/mathlib4).

**Status:** pre-1.0 research library. Committed code carries no placeholders and no custom
axioms; CI enforces that on every commit.

## Purpose

When a large finite structure is partitioned so that most pairs of parts look random, what
can be counted, approximated, or removed — and with which explicit constants? This library
develops that machinery for graphs, hypergraphs, and finite relational structures. Bounds
are carried in the statements rather than hidden behind existentials, so a summit can be
instantiated and its constants inspected.

## What the library provides

| Area | Public capability |
| --- | --- |
| **Finite foundations** | Tuple boxes, injective counts, densities, edits, homogeneous rectangles and `n`-index cell boxes, dependent coordinate splits, abstract weighted selection. |
| **Partitions and sampling** | Equitable refinements, weighted block energy, hypergeometric tails by exact binomial moments, **balanced slicing** (exact equal-size blocks simultaneously typical for a supplied trace family), leftover and chunk absorption into equipartitions. |
| **Weighted kernels** | Heterogeneous rectangular kernels with raw carrier weights: sums and averages, restriction, transpose, relation indicators, stepping over independent partitions, energy with the exact refinement-variance identity, residuals, cut discrepancy, and the constant-kernel contraction. |
| **Graphs** | Directed pair regularity, weak and strong regularity, equitable finite-family regularity, path and triangle counting, graph-removal bridges. |
| **Hypergraphs** | Uniform and colored vocabulary, copy counts, polyads and disc regularity, weak and edited triadic approximations. |
| **Relational structures** | Computable finite relational models, transports, counts, edits, binary-palette regularity, three-vertex induced counting; **indivisibility** (cellwise-constant models, with the quotient reading and exact nullary compatibility) and **cellwise edit bounds** with a computable majority rounding whose box-level edit count is computed exactly. |
| **Adapters** | Bridges to mathlib's `SimpleGraph` and to this library's uniform and colored hypergraphs, so an existing structure can enter the machinery without being re-encoded. |

## Current theorem boundary

- The relational substrate supports **arbitrary finite relational languages** and exact
  finite-model counts. The **regularity** and regularity-based **counting** layers currently
  assume **arity at most two**, and the quantitative induced-counting theorem treats patterns
  on **`Fin 3`**.
- There is **no general relational induced-removal theorem** yet.
- The triadic approximation is a **precursor**, not a formalization of the full
  Rödl–Schacht theorem.
- Regularity-based counting estimates for **general fixed patterns**, higher relational
  arities, and general hypergraph removal are **outside the current API**.

Counterexamples, impossibility results, and feasibility probes that constrain the API are
retained as named **gate** modules. This keeps rejected interfaces machine-checkable and
prevents closed questions from being reopened silently. These modules live under the
separate umbrella `RegularityLemmataGates` — built and audited by the same CI, directly
importable by module name, but not pulled in by `import RegularityLemmata`.

## Proved summits

The declarations to reach for, and the module each lives in. A summit's constants are visible
in its statement.

| Summit | Declaration | Module |
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
| Balanced slicing: exact equal-size blocks, simultaneously typical for a trace family | `exists_balanced_slicing` | `Partition.BalancedSlicing` |
| Indivisible approximation from cellwise homogeneity, with exact nullary compatibility | `exists_isIndivisibleFor_of_isHomogeneousCell` | `Relational.CellwiseEdit` |

For the substrate rather than the summits: `RegularityLemmata.Finite.Tuple`,
`RegularityLemmata.Finite.Injective` and `RegularityLemmata.Finite.Density` for counting,
densities and edits; `RegularityLemmata.Partition.Basic` and
`RegularityLemmata.Partition.BlockEnergy` for partitions and weighted energy;
`RegularityLemmata.Relational.Language` for the finite relational layer.

Two curated **facades** import a stack whole:

- `RegularityLemmata.Kernel` — the rectangular weighted-kernel layer (raw weights, kernels,
  relation indicators, stepping, energy and the refinement-variance identity, cut
  discrepancy).
- `RegularityLemmata.RelationalApproximation` — homogeneous cells, finite relational models,
  indivisibility, and cellwise edit bounds with the majority-rounding theorems.

## Using as a dependency

```toml
[[require]]
name = "RegularityLemmata"
git = "https://github.com/cameronfreer/regularity-lemmata"
rev = "v0.1.0"
```

Pin a tag. `main` is the development branch and its API moves between tags.

Then `import RegularityLemmata`, a curated facade such as `RegularityLemmata.Kernel` or
`RegularityLemmata.RelationalApproximation`, or an individual module such as
`RegularityLemmata.Relational.GraphCounting`.

## Building

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

Your project's toolchain should match this library's — see
[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json) for the
pinned Lean and mathlib versions.

CI enforces the repository's proof and axiom policies on every commit.

## Project documentation

| File | Contents |
| --- | --- |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Frozen design conventions and invariants. |
| [`docs/design/`](docs/design/) | Design documents for work that is not yet a theorem, including its permanent obstruction gates. |
| [`PROVENANCE.md`](PROVENANCE.md) | Mathematical and formal antecedents, and the scope of each adaptation. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Per-unit cadence, gates, and documentation rules. |
| [`SECURITY.md`](SECURITY.md) | Reporting policy. |
| [`CITATION.cff`](CITATION.cff) | How to cite this library. |

## Stability and license

Statements pass a review-and-falsification gate before their API freezes, but names and
signatures may still change between tags. Pin a tag.

Apache License 2.0 — see [`LICENSE`](LICENSE).
