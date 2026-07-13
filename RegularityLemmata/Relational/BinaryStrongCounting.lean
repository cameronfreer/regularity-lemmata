/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.StrongCountingLifting

/-!
# Strong transversal induced counting

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), the summit: comparing the actual number
of induced three-vertex pattern embeddings whose images lie in distinct coarse cells
(`transversalInducedCount`) against the coarse step estimate (`coarseInducedEstimate`) for a
`BinaryPaletteStrongWitness`, with a `10·τ + 3·η + 3·δ/η²` error bound.

Assembled on the nested selected-pair lifting in `Relational/StrongCountingLifting.lean`: the
common-index expansions align the actual and coarse sums over one fine index, and the final
approximation is proved through two named intermediate error bounds — a regularity charge
(`10·τ`, via the exact three-vertex count on uniform fine triples and `IsBadPair` lifting on
nonuniform ones) and a density-shift charge (`3·η + 3·δ/η²`, via three-factor perturbation and
the witness's deviant-mass bound).
-/

namespace RegularityLemmata

end RegularityLemmata
