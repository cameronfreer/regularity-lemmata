# RegularityLemmata

[![CI](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml/badge.svg)](https://github.com/cameronfreer/regularity-lemmata/actions/workflows/ci.yml)

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on [mathlib](https://github.com/leanprover-community/mathlib4). When a
large finite structure is partitioned so that most pairs of parts look random, what can be
counted, approximated, or removed, and with which explicit constants? The library develops that
machinery for graphs, hypergraphs, and finite relational structures, with every bound visible
in the theorem statement.

**Status:** pre-1.0 research library. Committed code carries no placeholders and no custom
axioms; CI enforces that on every commit. Names and signatures may change between tags, so pin a
tag.

**[Reader's guide](docs/GUIDE.md)** · **[API documentation](https://cameronfreer.github.io/regularity-lemmata/docs/)** · **[Examples](examples/README.md)** · **[Latest release](https://github.com/cameronfreer/regularity-lemmata/releases/latest)** · **[Changelog](CHANGELOG.md)**

## Installation

Add the library to your `lakefile.toml`, pinned to a tag:

```toml
[[require]]
name = "RegularityLemmata"
git = "https://github.com/cameronfreer/regularity-lemmata"
rev = "v0.11.0"
```

Your project's toolchain must match the library's: see [`lean-toolchain`](lean-toolchain) and
the mathlib revision in [`lake-manifest.json`](lake-manifest.json). Then import the public root,
a facade, or a module:

```lean
import RegularityLemmata.Kernel
```

A complete, compiled use. The file below is [`examples/ReadmeSnippet.lean`](examples/ReadmeSnippet.lean)
verbatim (built by the gate on every commit, and checked against the v0.11.0 release): a matrix
with entries in `[-1, 1]` is a sum of at most `⌈1/ε²⌉₊` weighted submatrix indicators with
coefficients at most `1/ε`, up to a residual of cut norm at most `ε·m·n`.

```lean
import RegularityLemmata.Kernel

open RegularityLemmata

/-- A real matrix with entries in `[-1, 1]`, indexed by `Fin m × Fin n`, is a sum of at most
`⌈1/ε²⌉₊` weighted submatrix indicators with coefficients of absolute value at most `1/ε`, up to
a residual whose cut norm (the largest absolute submatrix sum) is at most `ε · m · n`. -/
example {m n : ℕ} (M : Fin m → Fin n → ℝ) (hM : ∀ i j, |M i j| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset (Fin m)) (T : Fin k → Finset (Fin n)),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧ (∀ l, |c l| ≤ 1 / ε) ∧ (∀ l, S l ⊆ Finset.univ ∧ T l ⊆ Finset.univ) ∧
      rectCutNorm (fun i j => M i j - rectCombination c S T i j) (fun _ => 1) (fun _ => 1)
          Finset.univ Finset.univ
        ≤ ε * (finsetMass (fun _ : Fin m => (1 : ℝ)) Finset.univ
            * finsetMass (fun _ : Fin n => (1 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition (A := Finset.univ) (B := Finset.univ) M
    (fun _ => 1) (fun _ => 1) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun i _ j _ => hM i j) hε
```

To build the library itself:

```bash
lake exe cache get
lake build
bash scripts/check.sh   # build, sorry scan, axiom audit, roots gate
```

The external consumer fixture under [`consumer/`](consumer/README.md) is a separate Lake package
that depends on this repository by Git at a full commit; it is rebuilt against every release
commit.

## What you can reuse

- **Regularity for directed relations and finite families**: Szemerédi-style regular
  refinements, equitable finite-family regularity with host-independent bounds, and strong
  (energy-gap) witnesses, all with explicit fuel and part-count bounds.
- **Weighted rectangular kernels**: the Frieze–Kannan step partition with separate left and
  right part bounds, and the cut-matrix decomposition (at most `⌈1/ε²⌉₊` weighted rectangles,
  coefficients at most `1/ε`, residual cut norm at most `ε · mass`), two different reusable
  outputs.
- **Counting**: exact two- and three-vertex characterizations of induced patterns in finite
  relational models, the three-vertex counting theorem against a strong witness with every
  error term explicit, and counting from a cellwise approximation at any arity with the
  collision term computed.
- **Sampling and completion**: exact equal-size blocks on which every member of a supplied
  family keeps its density (balanced slicing), average-preserving slicing, and completion of
  block families into equipartitions.
- **Hypergraph precursors**: polyad regularity with an arity-generic energy increment and the
  deletion-only triadic approximation.
- **Independent tools**: finite multicolour Ramsey and binary-tree subtree Ramsey theorems, the
  Hedge forecaster's regret bound, density buckets, weighted selection.

The [reader's guide](docs/GUIDE.md) inventories all of this, mathematics first, with the
declarations to reach for and a release-indexed table of what is reusable at each tag.

## Main theorems and entry points

The declarations to reach for, and the module each lives in. Every bound is visible in the
statement. The final two rows are entry points rather than regularity theorems: balanced
slicing is a sampling theorem, and the indivisible-approximation theorem takes its partition as
an input.

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

Five curated **facades** bundle a stack behind one import (`RegularityLemmata.Kernel`,
`.FiniteSetSystems`, `.RelationalApproximation`, `.FiniteRamsey`, `.ProductSpaces`); each is
described in the guide, and every module remains directly importable.

## What is proved, and what is not

- The relational substrate supports **arbitrary finite relational languages** and exact
  finite-model counts. The **regularity** and regularity-based **counting** layers assume
  **arity at most two**, and the quantitative induced-counting theorem treats patterns on
  **`Fin 3`**.
- There is exactly **one removal theorem**, mathlib's triangle removal for simple graphs,
  re-exported; there is **no general relational induced-removal theorem**.
- The triadic approximation is a **precursor**, not a formalization of the full Rödl–Schacht
  theorem.
- Regularity-based counting for **general fixed patterns**, higher relational arities, and
  general hypergraph removal are **outside the current API**.

Counterexamples, impossibility results, and feasibility probes that constrain the API are
retained as machine-checked modules under the separate umbrella `RegularityLemmataGates`,
built and audited by the same CI but not pulled in by `import RegularityLemmata`.

## Project documentation

| File | Contents |
| --- | --- |
| [`docs/GUIDE.md`](docs/GUIDE.md) | The reader's guide: start here by task, what is reusable by release, the mathematics in four parts, and the boundary of what is proved. |
| [Generated API documentation](https://cameronfreer.github.io/regularity-lemmata/docs/) | doc-gen4 pages on GitHub Pages, one directory per version: `docs/latest/` follows the newest release, `docs/main/` is the most recently published documentation snapshot of `main` (the workflow runs on releases and on manual dispatch), and every module has a page at `docs/<version>/RegularityLemmata/<Dir>/<File>.html`; the build recipe is `docbuild/`. |
| [`examples/README.md`](examples/README.md) | The compiled examples: theorem specializations, concrete computations, and composition certificates. |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | Frozen design conventions and invariants. |
| [`CHANGELOG.md`](CHANGELOG.md) | Release notes, aggregated from the GitHub Releases, newest first. |
| [`docs/design/`](docs/design/) | Design records, each with a status banner: implemented (with links to the declarations), approved but not implemented, or deferred (with its permanent obstruction gates). |
| [`PROVENANCE.md`](PROVENANCE.md) | Mathematical and formal antecedents, and the scope of each adaptation. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Per-unit cadence, gates, and documentation rules. |
| [`SECURITY.md`](SECURITY.md) | Reporting policy. |
| [`CITATION.cff`](CITATION.cff) | How to cite this library. |

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
