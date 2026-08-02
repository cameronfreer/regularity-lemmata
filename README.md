# RegularityLemmata

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on [mathlib](https://github.com/leanprover-community/mathlib4).

The organizing question is quantitative: when a large finite structure is partitioned so
that most pairs of parts look random, what can be counted, approximated, or removed — and
with which explicit constants. Every summit here carries its bounds in its statement rather
than hiding them behind an existential.

## What is here

The library is organized by namespace, and each module's docstring is the record of what
that module establishes.

| Namespace | Covers |
| --- | --- |
| `RegularityLemmata.Finite` | Heterogeneous tuple boxes, injective tuple counting and collision bounds; densities over finite supports with a fixed zero-on-empty convention; edit sets and normalized edit distance; abstract weighted selection with forbidden-event and cost channels; multicolor Ramsey and independent-set tools. |
| `RegularityLemmata.Partition` | Machinery over mathlib's `Finpartition`: part unions, equitable splitting and grouping, mass-weighted block energy with refinement monotonicity, quantitative almost-refinement. |
| `RegularityLemmata.Graph` | Directed pair regularity and the energy-increment ladder; Szemerédi-style summits with explicit host-independent bounds; equitable regularity for a finite family of relations; a piece supplier producing large regular sub-partitions. |
| `RegularityLemmata.Hypergraph` | Uniform and colored hypergraphs, polyads and disc regularity, and the weak and edited triadic regularization precursors built on the Rödl–Schacht index and polyad test surfaces. |
| `RegularityLemmata.Relational` | A computable Boolean-valued layer over mathlib's `FirstOrder.Language`: finite models with a mathlib-structure bridge, transport, relation counts and densities, a per-symbol edit calculus; two-way pair palettes and vertex profiles; simultaneous palette regularity; counting through three vertices; and the transversal-counting and representative-selection machinery for the removal route. |

`ARCHITECTURE.md` is the canonical record of design decisions, frozen constants, and the
current state of work in progress. `PROVENANCE.md` records which published arguments
materially informed which proofs.

## What is not here

Stated plainly, because the boundary matters more than the inventory:

- **No relational removal lemma.** The relational layer counts; it does not yet remove.
  Removal is deferred to its own phase with its own statement freeze.
- **The triadic layer is a precursor**, not a formalization of the full Rödl–Schacht
  regularity method.
- **Pre-1.0.** Statements pass a review gate before their API freezes, but names and
  signatures may still change. Pin a tag or revision.

## Conventions

See [`ARCHITECTURE.md`](ARCHITECTURE.md). The three that shape every signature: raw counts
live in `ℕ` and normalized densities and errors in `ℝ`; densities are zero on an empty
denominator, with positivity required explicitly only where it is genuinely needed; and
partition energy is mass-weighted and diagonal-inclusive, because that is the
refinement-monotone quantity.

## How the library is developed

Statements are frozen only after a review-and-falsification pass, and a refuted route is
not deleted — it is kept in the tree as a named **gate**: a module whose theorems are the
machine-checked counterexamples and impossibility statements that ruled the route out.
Several modules exist for no other purpose. Reading them is the fastest way to learn why
an interface has the shape it does, and they are what stops a closed question from being
quietly reopened.

Committed code contains no `sorry` and no custom axioms; `scripts/check.sh` enforces this,
along with an axiom audit of every declaration in the library namespace, and CI runs the
same script. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the per-unit cadence.

## Using as a dependency

Add to your `lakefile.toml` (your project's toolchain should match this library's
`lean-toolchain`):

```toml
[[require]]
name = "RegularityLemmata"
git = "https://github.com/cameronfreer/regularity-lemmata"
rev = "main"
```

Then `import RegularityLemmata` (or individual modules such as
`RegularityLemmata.Relational.GraphCounting`).

## Building

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

Toolchain: `leanprover/lean4:v4.32.0` with mathlib `v4.32.0`.

## References

Sources that materially informed the development. This is a reading list for the
mathematics, not a claim that any of these papers is formalized in full; `PROVENANCE.md`
records the per-unit correspondence.

- E. Szemerédi, *Regular partitions of graphs*, Problèmes combinatoires et théorie des
  graphes (Colloq. Internat. CNRS, Univ. Orsay, 1976), 1978.
- A. Frieze and R. Kannan, *Quick approximation to matrices and applications*,
  Combinatorica 19 (1999).
- W. T. Gowers, *Hypergraph regularity and the multidimensional Szemerédi theorem*,
  Ann. of Math. 166 (2007).
- V. Rödl, B. Nagle, J. Skokan, M. Schacht, Y. Kohayakawa, *The hypergraph regularity
  method and its applications*, Proc. Natl. Acad. Sci. USA 102 (2005).
- T. Tao, *A variant of the hypergraph removal lemma*, J. Combin. Theory Ser. A 113 (2006).
- V. Rödl and J. Skokan, *Regularity lemma for k-uniform hypergraphs*, Random
  Structures Algorithms 25 (2004); B. Nagle, V. Rödl, M. Schacht, *The counting lemma
  for regular k-uniform hypergraphs*, Random Structures Algorithms 28 (2006)
  (the `(δ, d, r)` polyad regularity form).
- V. Rödl and M. Schacht, *Regular partitions of hypergraphs: Regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
- F. R. K. Chung and R. L. Graham, *Quasi-random hypergraphs*, Random Structures
  Algorithms 1 (1990) (discrepancy quasirandomness).
- Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022
  (the mathlib development this library builds on — see
  `Mathlib.Combinatorics.SimpleGraph.Regularity.*`).
- C. Edmonds, A. Koutsoukou-Argyraki, L. C. Paulson, *Szemerédi's Regularity Lemma*,
  Archive of Formal Proofs (an independent machine-checked energy-boost proof).
- N. Alon and A. Shapira, *Testing subgraphs in directed graphs*, J. Comput. System
  Sci. 69 (2004) (directed regularity).
- Y. Zhao, *Graph Theory and Additive Combinatorics*, MIT lecture notes / CUP 2023
  (the energy-increment presentation followed by the directed development here).
- A. Schrijver, *Szemerédi's regularity lemma*, CWI notes (the mass-weighted local
  quantity `e(A,B)²/(|A||B|)` behind `blockEnergy`).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).
