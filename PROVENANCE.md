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
    counting/removal and edge-count conversions (`Graph/RemovalBridge.lean`); and the
    private lower-tail exceptional-degree architecture of `….Triangle.Counting`
    (`badVertices`, `card_badVertices_le`; Y. Dillies, B. Mehta) is the cited antecedent
    for the independently authored directed, two-sided exceptional-degree bound in
    `Graph/RegularDegree.lean` and the apex-neighborhood triangle-counting architecture in
    `Graph/TriangleCounting.lean` (a directed, two-sided absolute-error generalization;
    mathlib's theorem is a positive-density lower bound);
  - `Mathlib.Combinatorics.Hypergraph.Basic` (E. Spotte-Smith, B. Mehta) — mathlib's
    set-based hypergraph type, targeted by the `UniformHypergraph.toHypergraph` bridge;
    the finite arity-indexed representation here is deliberately separate
    (`Hypergraph/Uniform.lean` records the rationale);
  - `Mathlib.ModelTheory.Basic` (A. Anderson and the mathlib community) — first-order
    languages, structures, homomorphisms, and embeddings, on which the finite
    relational layer is built (`Relational/Language.lean`, `Relational/Model.lean`,
    `Relational/PatternCounts.lean`);
  - `Mathlib.ModelTheory.Graph` (A. Anderson) — the language of graphs and the
    graph structure, used directly by the simple-graph adapter (no second graph
    language is introduced; `Relational/GraphAdapter.lean`).
    The finite `FiniteRelational` typeclass, the Boolean-valued `FiniteRelModel`
    wrapper, and the relational counts, edits, transports, and adapters
    (`Relational/*.lean`) are this repository's implementation over that foundation.
    The binary-palette regularity layer
    (`Relational/Binary{Palette,Profile,Energy,Increment,Regularity,Strong,
    Bridges}.lean`) is a finite-palette, directed binary adaptation of this
    repository's own mass-weighted graph regularity and strong-regularity machinery
    (`Graph/*.lean`), using mathlib's partition substrate and graph-regularity
    antecedents; it is **not** a formalization of a general relational removal
    theorem — higher arities and removal are explicitly deferred. Its mathematical
    antecedents are those already cited for the graph ladder (Szemerédi;
    Dillies–Mehta / mathlib; Zhao for the energy increment; Tao for the strong
    energy-gap stopping; Alon–Shapira for the directed/induced context).
    The binary-palette counting layer (`Relational/BinaryPattern.lean`,
    `Relational/TwoVertexCounting.lean`, `Relational/ThreeVertexCounting.lean`,
    `Relational/TransversalCounting.lean`, `Relational/StrongCountingLifting.lean`,
    `Relational/BinaryStrongRegularityCharge.lean`,
    `Relational/BinaryStrongCounting.lean`, `Relational/DiagonalGate.lean`,
    `Relational/GraphCounting.lean`) is likewise this repository's own composition
    of already documented APIs: it specializes the independently authored directed
    exceptional-degree, path-, and triangle-counting lemmas
    (`Graph/RegularDegree.lean`, `Graph/PathCounting.lean`,
    `Graph/TriangleCounting.lean`; antecedents cited above) to palette relations,
    lifts them through the Phase 9 strong palette witness, and bridges the results
    to simple graphs through the Phase 8 adapters and the hypergraph copy API
    (`Relational/GraphAdapter.lean`, `Hypergraph/Copies.lean`). It involves no
    antecedent beyond those already cited, and contains no removal theorem.
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
  polyad regularity condition (`IsPolyadRegularAt` in
  `Hypergraph/PolyadRegularity.lean`; the coarser `IsBlockUnionRegular` there is
  repository-specific and NOT the published condition).
- V. Rödl, M. Schacht, *Regular partitions of hypergraphs: Regularity lemmas*,
  Combin. Probab. Comput. 16 (2007) — the triadic phase builds a **precursor** using
  their index and polyad test surfaces, not a formalization of their full
  regular-partition theorem (Phase 7 design freeze in `ARCHITECTURE.md`;
  `Hypergraph/Triad.lean`, `Hypergraph/PolyadEnergy.lean`,
  `Hypergraph/PolyadWitness.lean`, `Hypergraph/TriadIncrement.lean`,
  `Hypergraph/TriadCleanup.lean`).
- F. R. K. Chung, R. L. Graham, *Quasi-random hypergraphs*, Random Structures
  Algorithms 1 (1990) — the discrepancy (DISC) quasirandomness tradition behind
  disc regularity (`Hypergraph/PolyadRegularity.lean`).
- L. Lovász, *Large Networks and Graph Limits*, AMS 2012 — cut-norm background.
