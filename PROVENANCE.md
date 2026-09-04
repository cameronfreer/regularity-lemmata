# Provenance

Public intellectual dependencies of this library. As of the initial public release,
all Lean source was authored by the copyright holder; no third-party source text is
copied into this repository (see `LICENSE` and the per-file SPDX headers; external
contributions after that release are recorded in the Git history and are licensed
under Apache-2.0 per `CONTRIBUTING.md`). The entries below record the formal
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
    `Graph/Regularity.lean`, `Graph/Bridge.lean`); and specifically the
    `Regularity/Chunk` construction (per-part equitabilisation of a witness
    atomisation, with its `m`/`m + 1` cell-size and part-count arithmetic) as the
    architecture adapted — to an arbitrary host, an arbitrary directed relation, and
    the ladder's own per-parent chunk count — in `Graph/EquitableChunk.lean`, together
    with its per-atom-remainder argument for the uncovered part of a witness side
    (`card_nonuniformWitness_sdiff_biUnion_star`), adapted in
    `Graph/EquitableChunkApprox.lean`; the density and energy estimates there are this
    repository's own, stated in an `ε`-free multiplication form with the loss explicit;
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
  - `Mathlib.Combinatorics.SetFamily.Shatter` (Y. Dillies) — the shattering predicate,
    shatterer, VC dimension, Pajor inequality, and Sauer–Shelah theorem consumed by
    `Finite/VCTrace.lean`. This repository adds the finite relation-fiber/trace interface,
    proves that image/intersection restriction cannot increase Mathlib's VC dimension, and
    derives support-sensitive trace and bounded-subset cardinality bounds using Mathlib's
    Pajor inequality, binomial estimates, and `powersetCard` enumeration; it does not define
    a second VC dimension.
- **Graphons in Lean 4** (C. Freer, Apache-2.0,
  <https://github.com/cameronfreer/graphon>) — the finite Frieze–Kannan iteration in
  `Graph/FriezeKannan.lean` ports the architecture of
  `Graphon/Regularity.lean` (`energy_increment_quantitative`: witness rectangle,
  double split, conditional variance + Cauchy–Schwarz) from measurable partitions to
  finite ones.
- **Szemerédi's Regularity Lemma**, Isabelle Archive of Formal Proofs (C. Edmonds,
  A. Koutsoukou-Argyraki, L. C. Paulson) — an independent machine-checked antecedent
  of the energy-boost argument (`Graph/Increment.lean`).

### The balanced-slicing stack

The fourteen files of the `Partition/` sampling stack (hypergeometric tails by exact binomial
moments, equal-block permutation encoding, simultaneous prefix-block sampling, geometric
conversion, threshold lemmas, `SliceCert`, balanced slicing, leftover/chunk absorption, and the
homogeneity perturbation lemmas) were transplanted, with renames and convention adaptation, from
the author's private `stable-hypergraph-regularity` repository (Apache-2.0, sole-author), where
they were developed as stability-neutral infrastructure. No third-party source text is involved.

## Publications

- N. Littlestone, M. K. Warmuth, *The weighted majority algorithm*, Inf. Comput. 108
  (1994) 212–261; Y. Freund, R. E. Schapire, *A decision-theoretic generalization of
  on-line learning and an application to boosting*, J. Comput. Syst. Sci. 55 (1997)
  119–139 — the multiplicative-weights (Hedge) forecaster and its regret bound
  (`Finite/Hedge.lean`). The formalization is this repository's own: an arbitrary finite
  expert type as the primitive, raw weights with the distribution derived rather than
  bundled, an explicit empty-expert endpoint, and the regret proof telescoping the relaxed
  logarithmic increment so that the learning rate carries no upper bound.

- E. Szemerédi, *Regular partitions of graphs*, Colloq. Internat. CNRS 260, 1978.
- A. Frieze, R. Kannan, *Quick approximation to matrices and applications*,
  Combinatorica 19 (1999).

  **The rectangular weighted-kernel development** (`Finite/RectKernel.lean`,
  `Partition/RectKernel.lean`, `Partition/RectKernelEnergy.lean`,
  `Partition/RectKernelCut.lean`, `Partition/RectKernelFriezeKannan.lean`; design freeze in
  `docs/design/rectangular-kernels.md`) divides credit three ways.

  **Classical source.** The weak-regularity architecture is theirs: weak approximation in cut
  discrepancy via a greedy energy increment, with the `ε²`-per-round gain and the resulting
  single-exponential round count. What is formalized here is a **step-partition summit**; the
  separate cut-matrix decomposition interface is not implemented.

  **This repository's formulation.** Raw carrier weights on **two heterogeneous carriers**
  rather than one normalized vertex set; **independent** left and right partitions whose part
  counts are exposed separately (`2^t` per coordinate, with `4^t` appearing only where the
  same-carrier adapter multiplies them); guard-free `x / 0 = 0` conventions throughout, so
  zero-mass cells and zero-mass carriers need no side conditions; the contraction of a stepped
  prediction at constant **1** rather than 2; and the common-refinement adapter converting the
  two-coordinate statement into a same-carrier one. The supporting inequalities
  (`abs_sum_bilinear_le`, `sq_sum_mul_le_sum_mul_sum_sq_mul` in `Finite/Inequalities.lean`)
  are proved here independently.

  **Internal antecedent.** The Boolean development in `Graph/FriezeKannan.lean`, which is
  **unchanged and not superseded**: it remains the sharper direct same-carrier summit. The
  rectangular route recovers its *discrepancy* conclusion through the adapter, at a weaker
  complexity bound, because it calls at `ε/2`.

  Cut-norm and step-kernel background for `Partition/RectKernelCut.lean` is Lovász's, cited
  below; the constant-1 contraction proved there is this repository's finite weighted
  formulation, not a restatement of a lemma from that source.
- T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006) —
  the strong-regularity energy-gap iteration (`Graph/Strong.lean`).
- Y. Zhao, *Graph Theory and Additive Combinatorics* (MIT notes / CUP 2023) — the
  energy-increment presentation followed throughout the graph ladder.
- A. Schrijver, *Szemerédi's regularity lemma*, CWI notes — the mass-weighted local
  quantity behind `blockEnergy`.
- N. Alon, A. Shapira, *Testing subgraphs in directed graphs*, JCSS 69 (2004) —
  directed regularity.
- D. Conlon, J. Fox, *Graph removal lemmas*, Surveys in Combinatorics 2013 (also
  arXiv:1211.3487), especially §§3.1–3.2 — the induced-removal proof architecture, with
  N. Alon, E. Fischer, M. Krivelevich, M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), as the original argument the survey presents. The scope of the
  borrowing has four parts, and they are at different stages.

  **Adapted and proved.** The equal-size piece supplier — the weaker
  Szemerédi-plus-independent-set route the survey mentions, NOT their improved cylinder-lemma
  bound, so no tower-type bound is claimed: `Finite/IndependentSet.lean` (greedy extraction
  under a degree cap), `Graph/PieceExtraction.lean` (equal-size weighted-to-unweighted
  conversion and trimming), `Graph/PieceSchedule.lean` (acyclic parameter schedule and
  supplier summit), over this repository's own equitable finite-family regularity engine
  rather than a cylinder lemma. Also the density bucketing and Ramsey extraction
  (`Finite/DensityBuckets.lean`, `Finite/MulticolorRamsey.lean`), the union density estimates
  (`Graph/UnionCenter.lean`, `Graph/UniformSlicing.lean`, `Graph/UniformUnion.lean` — whose
  union theorem is valid in itself, independently of the directed application G-U5 refutes),
  and the Lemma 3.2 general weighted representative-selection and candidate-mass
  architecture.

  **Refuted for directed relations.** The survey's Lemma 3.6 composition concludes that the
  union of pairwise-regular pieces with close densities is SELF-regular. That step is false
  for arbitrary directed relations, and gate **G-U5** (`Graph/UniformUnion.lean`) is the
  machine-checked refutation. The self-regular-subset route is closed here; it is not merely
  unformalized.

  **Redesigned.** In its place the current design pursues transversal counting with
  separately charged diagonal cells, over a proxy partition obtained by grouping the cells of
  an already-regular equipartition rather than splitting them. That design is this
  repository's, not the survey's; it carries its own permanent gates, and it has not yet
  composed into a theorem.

  **Not formalized.** Induced removal itself. Also not formalized: their strong cylinder
  regularity lemma (Lemma 3.5), the quantitative bounds of Lemmas 3.6–3.9, Lemma 3.7's
  partition into self-regular sets, arbitrary-size induced counting, their Theorem 3.1 for
  arbitrary `H`, and the infinite removal lemma.
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
  `Hypergraph/PolyadWitness.lean`, `Hypergraph/PolyadIncrement.lean`,
  `Hypergraph/TriadIncrement.lean`, `Hypergraph/TriadCleanup.lean`).
- F. R. K. Chung, R. L. Graham, *Quasi-random hypergraphs*, Random Structures
  Algorithms 1 (1990) — the discrepancy (DISC) quasirandomness tradition behind
  disc regularity (`Hypergraph/PolyadRegularity.lean`).
- L. Lovász, *Large Networks and Graph Limits*, AMS 2012 — cut-norm background.
- N. Alon, R. Livni, M. Malliaris, S. Moran, *Private PAC learning implies finite
  Littlestone dimension*.
  [arXiv:1806.00949](https://arxiv.org/abs/1806.00949) — **Lemma 16** is the source of the
  additive two-colour subtree theorem `binaryTreeRamsey_two` of
  `Finite/BinaryTreeRamsey.lean`. Their statement uses positive integers `p, q` and host height
  `p + q - 1`; substituting `p = a + 1` and `q = b + 1` gives the `a + b + 1` used here.

  Their recursive subtree notion is likewise the antecedent for the embedding semantics of
  `Finite/BinaryTreeEmbedding.lean`: a copy's root may sit at an arbitrary node of the host, a
  descendant may be more than one level deeper than its parent's image, and left/right branch
  direction is preserved.

  What is formalized is a **precise upper theorem, with no optimality claim**: the statement
  gives the explicit height `a + b + 1`, and no matching lower-bound colouring is formalized
  here, so nothing asserts that this height is least.

  `binaryTreeRamsey_two` formalizes the two-colour subtree theorem recorded from
  Alon–Livni–Malliaris–Moran, Lemma 16. It is also the two-colour specialization of
  G. Conant and C. Terry, *Encoding orders and trees in real-valued functions*
  ([arXiv:2607.21761](https://arxiv.org/abs/2607.21761)), **Lemma 2.6**, the tree-Ramsey
  ingredient used in their proof of Theorem 1.11. Their Lemma 2.6 is the multicolour
  generalization; what is formalized here is its two-colour case, and Theorem 1.11 is a
  downstream application rather than a Ramsey statement.

  What is this repository's own is the formulation: the word-indexed node types and branch
  relation of `Finite/FullBinaryTree.lean`, the single-law `InternalEmbedding` with
  injectivity and ancestry preservation derived from that law rather than assumed, the
  proper-embedding and leaf-extension formulation of
  `Finite/BinaryTreeProperEmbedding.lean` — which places a leaf image by entering the correct
  branch below the parent's image, so that no spare-height hypothesis is needed — the
  host-height-indexed recursion that keeps the height arithmetic out of the types, and the Lean
  proof engineering.

  Mathlib's `BinaryTree` was audited for this purpose and is **not** used: it is a storage
  type carrying data at nodes, with no notion of a node's address, and so supports neither the
  ancestry nor the branch-direction relations these embeddings are defined by.
- G. Conant and C. Terry, *Quantitative analytic stable regularity*.
  [arXiv:2607.21762](https://arxiv.org/abs/2607.21762). The almost-constancy vocabulary and the
  separation lemma of `Finite/AlmostConstant.lean` follow their Definitions 1.6/2.1 and
  Proposition 2.2.

  What is formalized is **not a verbatim transcription**. The predicates here are a
  **real-valued, empty-totalized extension**: `φ : α → ℝ` carries no range or sign constraint,
  and the empty set is almost constant by convention, matching this library's guard-free
  homogeneity treatment. On nonempty sets they **agree with the paper under its `[0,1]` range
  and positive-parameter assumptions**. Correspondingly,
  `exists_separation_of_not_isAlmostConstantOn` is a **real-valued generalization** of
  Proposition 2.2, with `exists_separation_mem_Icc_of_not_isAlmostConstantOn` as the exact
  **range-aware companion** recovering the paper's `[0,1]` setting.

  Its Appendix A supplies `Finite/AnalyticHomogeneous.lean`: **Definition A.1** (the
  `(δ, ε)`-homogeneous rectangle, due to Chavarria–Conant–Pillay, cited below) as
  `RectKernel.IsHomogeneousPair`, and **Proposition A.5** in both directions
  (`RectKernel.isHomogeneousPair_of_isAlmostConstantPair`,
  `RectKernel.isAlmostConstantPair_of_isHomogeneousPair`). All three are **reformulated
  variants**, not exact formalizations: the constants are preserved, but the statements
  extend the domains (real-valued kernels, arbitrary real parameters, and (b) with no
  hypothesis at all), localize the range assumption to the rectangle in (a) only, and
  totalize empty rectangles. The paper's "main observation" in the proof of A.5 — a
  `δ`-constant function is within `δ / 2` of a common center — is
  `isDeltaConstantOn_iff_exists_center` in `Finite/AlmostConstant.lean`, in the same
  reformulated sense, with `IsDeltaConstantOn.exists_center_mem_Icc` as its range-aware
  companion; `isAlmostConstantPair_op_iff` is library-original.

  The average-slicing and common-block theorems (`Partition/AverageSlicing.lean`,
  `Partition/CommonBlocks.lean`) are shaped by their Lemmas 4.3 and 4.6: an equipartition
  into exact-size blocks on which a finite `[0,1]`-valued family keeps its averages, and its
  per-piece version at one common block size. The route is this library's own — the
  level-set staircase reduces average control to `Partition/BalancedSlicing.lean` (with the
  rectangle-counting bridges of `Finite/RectangleCounting.lean` pricing exceptional-set
  trace functions), and the ratio hypotheses are discharged by the geometric races of
  `Partition/SlicingThreshold.lean` against `polyGeometricThreshold` — rather than the
  paper's Hoeffding-with-permutation-encoding argument; the control is two-sided where the
  paper's is one-sided. The stable-regularity theorems themselves are upstream
  (stability-flavored) material, not part of this library.
- N. Chavarria, G. Conant, and A. Pillay, *Continuous stable regularity*, J. Lond. Math. Soc.
  (2) 109 (2024), no. 1, Paper No. e12822. The origin of the `(δ, ε)`-homogeneous pair
  (Conant–Terry's Definition A.1, their [11]); consumed here only through Conant–Terry's
  restatement with strict inequalities.
