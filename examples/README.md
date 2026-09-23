# Examples

Compiled files that use the library through its advertised entry points. They are built by the
default `lake build` and by the gate (`bash scripts/check.sh`) as the `RegularityLemmataExamples`
library; nothing in the library imports them, and they are not part of the library's public API
(they do define named theorems, under the `RegularityLemmataExamples` namespace). Each file states
which import it needs; every import used here is a facade or a directly importable module.

```bash
lake build RegularityLemmataExamples        # all examples
lake env lean examples/OrdinaryMatrix.lean  # one file
```

## Theorem specializations

A library theorem restated on a concrete kind of object, with the library's conventions
translated (unit weights, matrix entries, a graph's edge indicator).

| File | Import | What it shows |
| --- | --- | --- |
| [`OrdinaryMatrix.lean`](OrdinaryMatrix.lean) | `RegularityLemmata.Kernel` | The cut-matrix decomposition of a real matrix with entries in `[-1, 1]` at unit weights: at most `⌈1/ε²⌉₊` weighted submatrix indicators, coefficients at most `1/ε`, and every submatrix sum of the residual at most `ε·m·n`, stated as finite sums. |
| [`WeightedBipartiteGraph.lean`](WeightedBipartiteGraph.lean) | `RegularityLemmata.Kernel` | The decomposition of a bipartite graph's edge indicator under nonnegative vertex weights, and its unit-weight form with the classical `ε·|A|·|B|` bound. |
| [`SignedResidual.lean`](SignedResidual.lean) | `RegularityLemmata.Kernel` | Rescaling a signed residual: the centered residual `f − rectAverage f A B` of a unit-bounded kernel takes values in `[-2, 2]`; rescaling by `1/2` and decomposing gives coefficients at most `2/ε` and a residual cut norm at most `2ε · mass`, for every such kernel. |
| [`ReadmeSnippet.lean`](ReadmeSnippet.lean) | `RegularityLemmata.Kernel` | The README's compiled use, verbatim: the cut-matrix decomposition of a `[-1, 1]`-matrix at unit weights, stated with the library's own cut norm. |

## Composition certificates

Two theorems chained with proved results only, certifying that their hypotheses and error
units fit together. The two certificates below certify different things and are kept apart.

| File | Import | What it shows |
| --- | --- | --- |
| [`CompositionCertificates.lean`](CompositionCertificates.lean) | `RegularityLemmata.Relational.BinaryStrong`, `RegularityLemmata.Relational.DiagonalGate` | `compatibility`: from the strong-witness existence theorem to the three-vertex counting theorem with the trivial cell ceiling `m = |s|`, an uninformative diagonal charge, type compatibility only. `prescribed_error`: the same chain seeded by an equipartition so that, under the host-size condition `24/ε₀ ≤ |s|`, the induced count of any three-vertex pattern is within `ε₀·|s|³` of the coarse estimate, with the parameter order written out; the witness's part-count bound is not retained. |

## Global approximation of a relational model (v0.13.0)

Consumers of the global-approximation stack through the `RelationalApproximation` facade.

| File | Import | What it shows |
| --- | --- | --- |
| [`TernaryMajorityRounding.lean`](TernaryMajorityRounding.lean) | `RegularityLemmata.Relational.MajorityAssembly` | The majority-rounding cost at a ternary symbol, `3·|s|³·(2θ + γ/2 + λ/2)`, with the box-level minority identity, the nullary copy, and one model that is indivisible for the partition and within the bound. |
| [`SharedEquitableModel.lean`](SharedEquitableModel.lean) | `RegularityLemmata.RelationalApproximation` | One equitable partition and one model from the composition, bounding a binary and a ternary symbol with the same pair, displacement term `(#P.parts − 1)·⌊|s|/t⌋`. |
| [`DirectedJoinRounding.lean`](DirectedJoinRounding.lean) | `RegularityLemmata.RelationalApproximation` | A directed binary relation rounded at the join of a row and a column partition: edit at most the row defects at the first plus the column defects at the second; part count at most the product. |
| [`SymmetricRounding.lean`](SymmetricRounding.lean) | `RegularityLemmata.RelationalApproximation` | A symmetric relation rounded at one partition: edit at most twice the row defects, and the rounded relation is symmetric. |
| [`GlobalApproximationCounting.lean`](GlobalApproximationCounting.lean) | `RegularityLemmata.RelationalApproximation`, `RegularityLemmata.Relational.UniformPatternCounts`, the gates-only `Relational.DiagonalLoopRegression` | The recipe: a uniform edit rate from the composition, homomorphism-count transfer (injective, and all homomorphisms with the collision term) at binary and ternary instances with constants displayed, the induced corollary only under an explicit diagonal-agreement premise, the reused loop regression, and the six-vertex counterexample pinned to the rounding operation. |

## Not here

The external consumer fixture, a separate Lake package depending on this repository by Git at a
full commit, lives under [`consumer/`](../consumer/README.md); it is not built by the gate.
