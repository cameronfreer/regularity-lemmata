/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Tuple
import RegularityLemmata.Finite.Injective
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Edit
import RegularityLemmata.Finite.WeightedChoice
import RegularityLemmata.Finite.MulticolorRamsey
import RegularityLemmata.Finite.DensityBuckets
import RegularityLemmata.Finite.Inequalities
import RegularityLemmata.Finite.PairDensity
import RegularityLemmata.Partition.Basic
import RegularityLemmata.Partition.Equitable
import RegularityLemmata.Partition.BlockEnergy
import RegularityLemmata.Partition.Energy
import RegularityLemmata.Partition.AlmostRefines
import RegularityLemmata.Partition.Fiber
import RegularityLemmata.Graph.Uniformity
import RegularityLemmata.Graph.UniformSlicing
import RegularityLemmata.Graph.UniformUnion
import RegularityLemmata.Graph.Variance
import RegularityLemmata.Graph.Increment
import RegularityLemmata.Graph.BadMass
import RegularityLemmata.Graph.BadMassDiag
import RegularityLemmata.Graph.Atomise
import RegularityLemmata.Graph.Regularity
import RegularityLemmata.Graph.RegularityDiag
import RegularityLemmata.Graph.Bridge
import RegularityLemmata.Graph.RemovalBridge
import RegularityLemmata.Graph.CutNorm
import RegularityLemmata.Graph.FriezeKannan
import RegularityLemmata.Graph.Strong
import RegularityLemmata.Graph.RegularDegree
import RegularityLemmata.Graph.RepeatedCellCounting
import RegularityLemmata.Graph.PathCounting
import RegularityLemmata.Graph.TriangleCounting
import RegularityLemmata.Hypergraph.Uniform
import RegularityLemmata.Hypergraph.Colored
import RegularityLemmata.Hypergraph.Copies
import RegularityLemmata.Hypergraph.Polyad
import RegularityLemmata.Hypergraph.PolyadRegularity
import RegularityLemmata.Hypergraph.Triad
import RegularityLemmata.Hypergraph.PolyadEnergy
import RegularityLemmata.Hypergraph.PolyadWitness
import RegularityLemmata.Hypergraph.TriadIncrement
import RegularityLemmata.Hypergraph.TriadCleanup
import RegularityLemmata.Relational.Language
import RegularityLemmata.Relational.Model
import RegularityLemmata.Relational.Transport
import RegularityLemmata.Relational.Counts
import RegularityLemmata.Relational.Edit
import RegularityLemmata.Relational.PatternCounts
import RegularityLemmata.Relational.GraphAdapter
import RegularityLemmata.Relational.HypergraphAdapters
import RegularityLemmata.Relational.BinaryPalette
import RegularityLemmata.Relational.BinaryProfile
import RegularityLemmata.Relational.BinaryEnergy
import RegularityLemmata.Relational.BinaryIncrement
import RegularityLemmata.Relational.BinaryRegularity
import RegularityLemmata.Relational.BinaryStrong
import RegularityLemmata.Relational.BinaryBridges
import RegularityLemmata.Relational.BinaryPattern
import RegularityLemmata.Relational.TwoVertexCounting
import RegularityLemmata.Relational.ThreeVertexCounting
import RegularityLemmata.Relational.TransversalCounting
import RegularityLemmata.Relational.StrongCountingLifting
import RegularityLemmata.Relational.BinaryStrongRegularityCharge
import RegularityLemmata.Relational.BinaryStrongCounting
import RegularityLemmata.Relational.DiagonalGate
import RegularityLemmata.Relational.GraphCounting
import RegularityLemmata.Relational.InducedRemovalGates
import RegularityLemmata.Relational.BinaryDiagRegularity
import RegularityLemmata.Relational.BinaryDiagStrong
import RegularityLemmata.Relational.RepresentativeSelection
import RegularityLemmata.Relational.PlacementStrata

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
