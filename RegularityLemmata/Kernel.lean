/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Weight
import RegularityLemmata.Finite.Average
import RegularityLemmata.Finite.AlmostConstant
import RegularityLemmata.Finite.RectKernel
import RegularityLemmata.Finite.RelationKernel
import RegularityLemmata.Partition.RectKernel
import RegularityLemmata.Partition.RectKernelEnergy
import RegularityLemmata.Partition.RectKernelCut
import RegularityLemmata.Partition.RectKernelFriezeKannan

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
* `Finite.Average` — one-variable averages (`averageOn`), guard-free at `∅`, with `densityOn`
  as their indicator shadow and both rectangle-fiber factorizations of `rectAverageCount`. One
  averaging vocabulary shared by kernel averages, fiber averages, and densities.
* `Finite.AlmostConstant` — the analytic analogue of `ε`-homogeneity: `δ`-constant and
  `ε`-almost `δ`-constant sets and rectangles, the separation theorem, and the level-set
  staircase reducing `[0,1]`-valued average control to set-density control. Stability-free —
  no ladders, trees, or ranks.
* `Partition.RectKernel` — decomposition along independent partitions of the two carriers, and
  the stepped prediction (`steppedRectSum`).
* `Partition.RectKernelEnergy` — kernel energy against a partition pair and the exact
  parallel-axis identity: a refinement's energy gain is the mass-weighted variance of the
  stepped values.
* `Partition.RectKernelCut` — rectangle error, cut discrepancy (`rectCutDiscrepancy`),
  residuals, and the cut-norm contraction of stepping with constant `1`.
* `Partition.RectKernelFriezeKannan` — the weak-regularity summit: the paired energy-increment
  iteration, with **separate** left and right part-count bounds (`2^t` per coordinate), and
  the same-carrier adapter that multiplies them. The Boolean summit in `Graph/FriezeKannan.lean`
  remains the sharper direct result for one carrier.

The design freeze for this stack is `docs/design/rectangular-kernels.md`.
-/
