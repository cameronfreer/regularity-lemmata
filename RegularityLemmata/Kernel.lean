/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Weight
import RegularityLemmata.Finite.RectKernel
import RegularityLemmata.Finite.RelationKernel
import RegularityLemmata.Partition.RectKernel
import RegularityLemmata.Partition.RectKernelEnergy
import RegularityLemmata.Partition.RectKernelCut

/-!
# Facade: the rectangular weighted-kernel stack

One import for the analytic kernel layer — the substrate an analytic (Frieze–Kannan-style)
regularity development consumes. A **facade** imports a curated stack and defines nothing;
each listed module remains directly importable.

* `Finite.Weight` — raw finite weights and masses. Nonnegativity and normalization are
  hypotheses, never fields, so zero-mass cells and conditioning stay honest.
* `Finite.RectKernel` — heterogeneous rectangular kernels `X → Y → ℝ` with carrier weights on
  both sides: weighted rectangle sums and averages (`rectSum`, `rectAverage`), transpose,
  pullback, restriction, and the boundedness predicates.
* `Finite.RelationKernel` — relation indicators as kernels: the bridge between the kernel core
  and the pair-density core.
* `Partition.RectKernel` — decomposition along independent partitions of the two carriers, and
  the stepped prediction (`steppedRectSum`).
* `Partition.RectKernelEnergy` — kernel energy against a partition pair and the exact
  parallel-axis identity: a refinement's energy gain is the mass-weighted variance of the
  stepped values.
* `Partition.RectKernelCut` — rectangle error, cut discrepancy (`rectCutDiscrepancy`),
  residuals, and the contraction of the constant-`1` kernel.

The design freeze for this stack is `docs/design/rectangular-kernels.md`.
-/
