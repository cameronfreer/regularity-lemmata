import RegularityLemmata.Finite.Tuple
import RegularityLemmata.Finite.Injective
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Edit
import RegularityLemmata.Finite.Inequalities
import RegularityLemmata.Finite.PairDensity
import RegularityLemmata.Partition.Basic
import RegularityLemmata.Partition.Equitable
import RegularityLemmata.Partition.BlockEnergy
import RegularityLemmata.Partition.Energy
import RegularityLemmata.Partition.AlmostRefines
import RegularityLemmata.Graph.Uniformity
import RegularityLemmata.Graph.Variance
import RegularityLemmata.Graph.Increment
import RegularityLemmata.Graph.BadMass
import RegularityLemmata.Graph.Atomise

/-!
# RegularityLemmata

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on mathlib.

The first release concerns finite combinatorial regularity: a finite tuple and counting
substrate, a density and edit calculus, and partition and weighted-energy machinery.
See `README.md` for scope and `ARCHITECTURE.md` for the library's conventions.
-/

namespace RegularityLemmata

/-- Library version marker. Also guarantees the axiom audit always has at least one
declaration to check. -/
def version : String := "0.1.0"

end RegularityLemmata
