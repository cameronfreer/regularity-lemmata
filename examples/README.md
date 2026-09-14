# Examples

Compiled files that use the library through its advertised entry points. They are built by the
default `lake build` and by the gate (`bash scripts/check.sh`) as the `RegularityLemmataExamples`
library; nothing in the library imports them, and they define no reusable declarations. Each file
states which import it needs; every import used here is a facade or a directly importable module.

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

## Concrete computations

A signed, non-indicator kernel handled by rescaling, with the bookkeeping made explicit.

| File | Import | What it shows |
| --- | --- | --- |
| [`SignedResidual.lean`](SignedResidual.lean) | `RegularityLemmata.Kernel` | The centred residual `f − rectAverage f A B` of a unit-bounded kernel takes values in `[-2, 2]`; rescaling by `1/2` and decomposing gives coefficients at most `2/ε` and a residual cut norm at most `2ε · mass`. |

## Composition certificates

Two theorems chained with proved results only, certifying that their hypotheses and error
units fit together. The two certificates below certify different things and are kept apart.

| File | Import | What it shows |
| --- | --- | --- |
| [`CompositionCertificates.lean`](CompositionCertificates.lean) | `RegularityLemmata.Relational.BinaryStrong`, `RegularityLemmata.Relational.DiagonalGate` | `compatibility`: from the strong-witness existence theorem to the three-vertex counting theorem with the trivial cell ceiling `m = |s|`, an uninformative diagonal charge, type compatibility only. `prescribed_error`: the same chain seeded by an equipartition so that, under the host-size condition `24/ε₀ ≤ |s|`, the induced count of any three-vertex pattern is within `ε₀·|s|³` of the coarse estimate, with the parameter order written out; the witness's part-count bound is not retained. |

## Not here

The external consumer fixture, a separate Lake package depending on this repository by Git at a
full commit, lives under [`consumer/`](../consumer/README.md); it is not built by the gate.
