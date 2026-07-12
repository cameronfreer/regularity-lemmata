/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.TransversalCounting

/-!
# Strong transversal induced counting

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), witness layer: comparing the actual
number of induced three-vertex pattern embeddings whose images lie in distinct coarse cells
(`transversalInducedCount`) against the coarse step estimate (`coarseInducedEstimate`) for a
`BinaryPaletteStrongWitness`, with a `10·τ + 3·η + 3·δ/η²` error bound.

This module builds the witness-specific pieces on top of the partition-refinement substrate
in `Relational/TransversalCounting.lean`: the nested selected-pair lifting (charging
nonuniform and density-deviant fine pairs), the common-index expansions aligning the actual
and coarse sums over one fine index, and the final approximation assembled through two named
intermediate error bounds.
-/

namespace RegularityLemmata

end RegularityLemmata
