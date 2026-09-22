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

**[Reader's guide](docs/GUIDE.md)** · **[API reference](https://cameronfreer.github.io/regularity-lemmata/docs/)** · **[Examples](examples/README.md)** · **[Latest release](https://github.com/cameronfreer/regularity-lemmata/releases/latest)** · **[Changelog](CHANGELOG.md)**

## What you can use, and current limits

- **Regularity for directed relations and finite families**: Szemerédi-style regular
  refinements, equitable finite-family regularity with host-independent bounds, and strong
  (energy-gap) witnesses, all with explicit fuel and part-count bounds.
  [Guide, Part IV](docs/GUIDE.md#part-iv-which-counting-and-removal-theorems-exist).
- **Weighted rectangular kernels**: the Frieze–Kannan step partition with separate left and
  right part bounds, and the cut-matrix decomposition (at most `⌈1/ε²⌉₊` weighted rectangles,
  coefficients at most `1/ε`, residual cut norm at most `ε · mass`), two different reusable
  outputs. [Guide, Part III](docs/GUIDE.md#part-iii-weighted-kernels-two-different-outputs).
- **Counting**: exact two- and three-vertex characterizations of induced patterns in finite
  relational models, the three-vertex counting theorem against a strong witness with every
  error term explicit, and counting from a cellwise approximation at any arity with the
  collision term computed.
  [Guide, Part IV](docs/GUIDE.md#part-iv-which-counting-and-removal-theorems-exist).
- **Global approximation of a relational model**: majority rounding at any partition with its
  edit cost bounded by summed coordinate defects (the partition defect, with the exact
  refinement variance identity), transport along an equitable representative map with an
  explicit displaced set, and the composition giving one equitable partition and one model for
  all symbols. Homomorphism-count transfer for simple patterns follows; the uniform induced-count
  corollary additionally requires diagonal agreement, which rounding does not guarantee.
  [Guide, Part IV](docs/GUIDE.md#part-iv-which-counting-and-removal-theorems-exist).
- **Sampling and completion**: exact equal-size blocks on which every member of a supplied
  family keeps its density (balanced slicing), average-preserving slicing, and completion of
  block families into equipartitions.
  [Guide, Part II](docs/GUIDE.md#part-ii-partitions-sampling-completion).
- **Hypergraph precursors**: polyad regularity with an arity-generic energy increment and the
  deletion-only triadic approximation.
  [Guide, Part IV](docs/GUIDE.md#part-iv-which-counting-and-removal-theorems-exist).
- **Independent tools**: finite multicolour Ramsey and binary-tree subtree Ramsey theorems, the
  Hedge forecaster's regret bound, density buckets, weighted selection.
  [Guide, Independent tools](docs/GUIDE.md#independent-tools).

The limits, stated plainly: the relational substrate supports arbitrary finite relational
languages and exact finite-model counts, but the regularity and regularity-based counting
layers assume **arity at most two**, and the regularity-based induced-counting theorem treats
patterns on **`Fin 3`** (the transfer theorems above are not so restricted). There is exactly **one removal theorem**, mathlib's triangle removal for
simple graphs, re-exported; there is **no general relational induced-removal theorem**. The
triadic approximation is a **precursor**, not the full Rödl–Schacht theorem. Regularity-based
counting for general fixed patterns, higher arities, and general hypergraph removal are
**outside the current API**. The guide's
[boundary section](docs/GUIDE.md#part-iv-which-counting-and-removal-theorems-exist) has the
longer explanation, and its table of
[main theorems and entry points](docs/GUIDE.md#main-theorems-and-entry-points) names the
declarations to reach for.

## Quick start

Add the library to your `lakefile.toml`, pinned to a tag:

```toml
[[require]]
name = "RegularityLemmata"
git = "https://github.com/cameronfreer/regularity-lemmata"
rev = "v0.13.0"
```

Your project's toolchain must match the pinned release's: see its
[`lean-toolchain`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/lean-toolchain)
and the mathlib revision in its
[`lake-manifest.json`](https://github.com/cameronfreer/regularity-lemmata/blob/v0.13.0/lake-manifest.json).
Then import the public root, a facade, or a module:

```lean
import RegularityLemmata.Kernel
```

Five curated facades bundle a stack behind one import (`RegularityLemmata.Kernel`,
`.FiniteSetSystems`, `.RelationalApproximation`, `.FiniteRamsey`, `.ProductSpaces`); the guide
describes each, and every module remains directly importable.

<details>
<summary><b>Example: approximating a matrix</b> (a complete, compiled file)</summary>

The file below is [`examples/ReadmeSnippet.lean`](examples/ReadmeSnippet.lean) verbatim, built
by the gate on every commit (the v0.13.0 release included) and checked against v0.11.0 as well: a matrix with entries in `[-1, 1]` is
a sum of at most `⌈1/ε²⌉₊` weighted submatrix indicators with coefficients at most `1/ε`, up to a
residual of cut norm at most `ε·m·n`.

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

</details>

## Documentation and contributing

- **Learn and use**: the [reader's guide](docs/GUIDE.md) (start here by task, what is reusable
  by release, the mathematics in four parts, the boundary), the
  [API reference](https://cameronfreer.github.io/regularity-lemmata/docs/) (generated by
  doc-gen4, one directory per version), and the [examples](examples/README.md) (theorem
  specializations and composition certificates, compiled on every commit).
- **Develop**: [`CONTRIBUTING.md`](CONTRIBUTING.md) (building and checking the repository, the
  per-unit cadence, gates, release verification), [`ARCHITECTURE.md`](ARCHITECTURE.md) (frozen
  conventions and invariants), and the [design records](docs/design/) (each with a status
  banner: implemented, approved but not implemented, or deferred with its obstruction gates).
- **Reference**: the [changelog](CHANGELOG.md), [`PROVENANCE.md`](PROVENANCE.md) (mathematical
  and formal antecedents, and the scope of each adaptation), [`SECURITY.md`](SECURITY.md).

## Citation and license

Cite with [`CITATION.cff`](CITATION.cff). Apache License 2.0; see [`LICENSE`](LICENSE).
