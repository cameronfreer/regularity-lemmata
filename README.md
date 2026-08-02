# RegularityLemmata

[![CI](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml/badge.svg)](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml)

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on [mathlib](https://github.com/leanprover-community/mathlib4).

## Purpose

When a large finite structure is partitioned so that most pairs of parts look random, what
can be counted, approximated, or removed — and with which explicit constants? This library
develops that machinery for graphs, hypergraphs, and finite relational structures. Bounds
are carried in the statements rather than hidden behind existentials, so a summit can be
instantiated and its constants inspected.

## What the library provides

| Area | Public capability |
| --- | --- |
| **Finite foundations** | Tuple boxes, injective counts, densities, edits, partitions, equitable refinements, weighted energy, abstract weighted selection. |
| **Graphs** | Directed pair regularity, weak and strong regularity, equitable finite-family regularity, path and triangle counting, graph-removal bridges. |
| **Hypergraphs** | Uniform and colored vocabulary, copy counts, polyads and disc regularity, weak and edited triadic approximations. |
| **Relational structures** | Computable finite relational models, transports, counts, edits, graph and hypergraph adapters, binary-palette regularity, three-vertex induced counting. |

## Current theorem boundary

- Binary relational regularity and counting are restricted to **arity at most two** and
  patterns on **`Fin 3`**.
- There is **no general relational induced-removal theorem** yet.
- The triadic approximation is a **precursor**, not a formalization of the full
  Rödl–Schacht theorem.
- General fixed-pattern counting, higher relational arities, and general hypergraph removal
  are **outside the current API**.

Refuted routes are not deleted. They are kept in the tree as named **gates** — modules whose
theorems are machine-checked counterexamples and impossibility statements — so that a closed
question cannot be quietly reopened, and so that an interface's shape can be traced to the
obstruction that forced it.

## Where to start

| Module | For |
| --- | --- |
| `RegularityLemmata.Finite.*` | Counting, density, and edit substrate. |
| `RegularityLemmata.Partition.*` | `Finpartition` machinery and weighted energy. |
| `RegularityLemmata.Graph.Regularity` | The graph regularity summit. |
| `RegularityLemmata.Graph.EquitableFamilyRegularity` | Simultaneous regularity for a finite family of relations. |
| `RegularityLemmata.Hypergraph.TriadCleanup` | Triadic approximation. |
| `RegularityLemmata.Relational.Language` | The finite relational substrate. |
| `RegularityLemmata.Relational.BinaryRegularity` | Palette regularity. |
| `RegularityLemmata.Relational.BinaryStrongCounting` | Counting through three vertices. |

## Using as a dependency

```toml
[[require]]
name = "RegularityLemmata"
git = "https://github.com/cameronfreer/regularity-lemmata"
rev = "v0.1.0"
```

Pin a tag. `main` is the development branch and its API moves between tags.

Then `import RegularityLemmata`, or an individual module such as
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
| [`PROVENANCE.md`](PROVENANCE.md) | Mathematical and formal antecedents, and the scope of each adaptation. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Per-unit cadence, gates, and documentation rules. |
| [`SECURITY.md`](SECURITY.md) | Reporting policy. |
| [`CITATION.cff`](CITATION.cff) | How to cite this library. |

## Stability and license

Pre-1.0. Statements pass a review-and-falsification gate before their API freezes, but
names and signatures may still change between tags.

Apache License 2.0 — see [`LICENSE`](LICENSE).
