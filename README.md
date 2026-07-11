# RegularityLemmata

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on [mathlib](https://github.com/leanprover-community/mathlib4).

## Scope

The first release concerns **finite combinatorial regularity**, developed in layers:

1. **Finite tuple and counting substrate** — heterogeneous tuple boxes `Fin j → Finset V`,
   injective tuple counting, falling factorials, collision bounds, coordinate deletion and
   lower faces.
2. **Density and edit calculus** — densities over finite supports with an explicit
   zero-on-empty-denominator convention, edit sets, and normalized edit distance.
3. **Partitions and weighted energy** — machinery over mathlib's `Finpartition`:
   part-union lemmas, equitable splitting, mass-weighted block energy with refinement
   monotonicity, and a quantitative almost-refinement predicate.
4. **Graph regularity ladder** (subsequent releases) — directed pair regularity, bridges
   to mathlib's Szemerédi regularity lemma, finite weak (Frieze–Kannan) regularity,
   and strong regularity with counting.
5. **Hypergraph vocabulary and local complex counting** (subsequent releases) — uniform
   and colored hypergraphs, graded faces, polyads, and disc regularity.

## Conventions

See [`ARCHITECTURE.md`](ARCHITECTURE.md). Highlights: raw counts live in `ℕ`, normalized
densities and errors in `ℝ`; densities are zero on an empty denominator, with positivity
required explicitly in substantive theorems; committed code contains no `sorry` and no
custom axioms (enforced by `scripts/check.sh` in CI).

## Building

```bash
lake exe cache get
lake build
bash scripts/check.sh
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` with mathlib `v4.32.0-rc1`.

## References

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
  Combin. Probab. Comput. 16 (2007) (the triadic phase builds a precursor using
  their index and polyad test surfaces, not a formalization of the full theorem).
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
