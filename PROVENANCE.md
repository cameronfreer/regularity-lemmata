# Provenance

Public intellectual dependencies of this library. All Lean source was authored by the
copyright holder; no third-party source text is copied into this repository (see
`LICENSE` and the per-file SPDX headers). The entries below record the formal
developments and publications whose results, interfaces, or proof architectures
materially inform it; mathlib and other dependencies are consumed through Lake as
ordinary imports. Every public mathematical antecedent materially informing a
definition or proof is cited publicly, in the relevant file docstring and here.

## Formal developments

- **mathlib** (Apache-2.0). Imported throughout. Architectural antecedents beyond
  ordinary imports, cited in the relevant file docstrings:
  - `Mathlib.Combinatorics.SimpleGraph.Regularity.*` (Y. Dillies, B. Mehta) — pair
    uniformity, witness selection, atomisation bounds, and the bounded
    energy-increment iteration (`Graph/Uniformity.lean`, `Graph/Atomise.lean`,
    `Graph/Regularity.lean`, `Graph/Bridge.lean`);
  - `Mathlib.Order.Partition.Finpartition` / `….Equipartition` and `equitabilise` —
    the partition substrate (`Partition/*.lean`);
  - `Mathlib.Combinatorics.SimpleGraph.Triangle.*`, `….DegreeSum` — triangle
    counting/removal and edge-count conversions (`Graph/RemovalBridge.lean`);
  - `Mathlib.Combinatorics.Hypergraph.Basic` (E. Spotte-Smith, B. Mehta) — mathlib's
    set-based hypergraph type, targeted by the `UniformHypergraph.toHypergraph` bridge;
    the finite arity-indexed representation here is deliberately separate
    (`Hypergraph/Uniform.lean` records the rationale).
- **Graphons in Lean 4** (C. Freer, Apache-2.0,
  <https://github.com/cameronfreer/graphon>) — the finite Frieze–Kannan iteration in
  `Graph/FriezeKannan.lean` ports the architecture of
  `Graphon/Regularity.lean` (`energy_increment_quantitative`: witness rectangle,
  double split, conditional variance + Cauchy–Schwarz) from measurable partitions to
  finite ones.
- **Szemerédi's Regularity Lemma**, Isabelle Archive of Formal Proofs (C. Edmonds,
  A. Koutsoukou-Argyraki, L. C. Paulson) — an independent machine-checked antecedent
  of the energy-boost argument (`Graph/Increment.lean`).

## Publications

- E. Szemerédi, *Regular partitions of graphs*, Colloq. Internat. CNRS 260, 1978.
- A. Frieze, R. Kannan, *Quick approximation to matrices and applications*,
  Combinatorica 19 (1999).
- T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006) —
  the strong-regularity energy-gap iteration (`Graph/Strong.lean`).
- Y. Zhao, *Graph Theory and Additive Combinatorics* (MIT notes / CUP 2023) — the
  energy-increment presentation followed throughout the graph ladder.
- A. Schrijver, *Szemerédi's regularity lemma*, CWI notes — the mass-weighted local
  quantity behind `blockEnergy`.
- N. Alon, A. Shapira, *Testing subgraphs in directed graphs*, JCSS 69 (2004) —
  directed regularity.
- Y. Dillies, B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022.
- W. T. Gowers, *Hypergraph regularity and the multidimensional Szemerédi theorem*,
  Ann. of Math. 166 (2007); V. Rödl, B. Nagle, J. Skokan, M. Schacht, Y. Kohayakawa,
  *The hypergraph regularity method and its applications*, PNAS 102 (2005); T. Tao,
  *A variant of the hypergraph removal lemma*, JCTA 113 (2006) — the hypergraph
  phases' mathematical background.
- V. Rödl, J. Skokan, *Regularity lemma for k-uniform hypergraphs*, Random Structures
  Algorithms 25 (2004); B. Nagle, V. Rödl, M. Schacht, *The counting lemma for regular
  k-uniform hypergraphs*, Random Structures Algorithms 28 (2006) — the `(δ, d, r)`
  polyad regularity condition (`IsPolyadRegular` in `Hypergraph/Polyad.lean`; the
  coarser `IsBlockUnionRegular` there is repository-specific and NOT the published
  condition).
- V. Rödl, M. Schacht, *Regular partitions of hypergraphs: Regularity lemmas*,
  Combin. Probab. Comput. 16 (2007) — the public target of the triadic phase
  (Phase 7 design freeze in `ARCHITECTURE.md`; `Hypergraph/Triad.lean`).
- F. R. K. Chung, R. L. Graham, *Quasi-random hypergraphs*, Random Structures
  Algorithms 1 (1990) — the discrepancy (DISC) quasirandomness tradition behind
  disc regularity (`Hypergraph/Polyad.lean`).
- L. Lovász, *Large Networks and Graph Limits*, AMS 2012 — cut-norm background.
