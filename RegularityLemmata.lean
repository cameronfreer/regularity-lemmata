/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Tuple
import RegularityLemmata.Finite.Injective
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Average
import RegularityLemmata.Finite.RectangleCounting
import RegularityLemmata.Finite.AlmostConstant
import RegularityLemmata.Finite.Edit
import RegularityLemmata.Finite.WeightedChoice
import RegularityLemmata.Finite.WeightedChoiceBudget
import RegularityLemmata.Finite.MulticolorRamsey
import RegularityLemmata.Finite.DensityBuckets
import RegularityLemmata.Finite.IndependentSet
import RegularityLemmata.Finite.Inequalities
import RegularityLemmata.Finite.Weight
import RegularityLemmata.Finite.CoordinateSplit
import RegularityLemmata.Finite.ProductBox
import RegularityLemmata.Finite.RelationFiber
import RegularityLemmata.Finite.VCTrace
import RegularityLemmata.Finite.RectKernel
import RegularityLemmata.Finite.PairDensity
import RegularityLemmata.Finite.RelationKernel
import RegularityLemmata.Finite.HomogeneousPair
import RegularityLemmata.Finite.HomogeneousCell
import RegularityLemmata.Partition.Basic
import RegularityLemmata.Partition.Equitable
import RegularityLemmata.Partition.Grouping
import RegularityLemmata.Partition.BlockEnergy
import RegularityLemmata.Partition.HomogeneousPartitions
import RegularityLemmata.Partition.RectKernel
import RegularityLemmata.Partition.RectKernelEnergy
import RegularityLemmata.Partition.RectKernelCut
import RegularityLemmata.Partition.RectKernelFriezeKannan
import RegularityLemmata.Partition.Energy
import RegularityLemmata.Partition.AlmostRefines
import RegularityLemmata.Partition.Fiber
import RegularityLemmata.Partition.FiniteProbabilisticMethod
import RegularityLemmata.Partition.HypergeometricTail
import RegularityLemmata.Partition.PolyGeometricThreshold
import RegularityLemmata.Partition.TraceComplementClosure
import RegularityLemmata.Partition.ParentSubtypeRekey
import RegularityLemmata.Partition.ExplicitPolyGeometricThreshold
import RegularityLemmata.Partition.EqualBlockEncoding
import RegularityLemmata.Partition.SimultaneousSampling
import RegularityLemmata.Partition.ProportionalTraceForm
import RegularityLemmata.Partition.HypergeometricGeometric
import RegularityLemmata.Partition.ActiveTraceSchedule
import RegularityLemmata.Partition.ParentSample
import RegularityLemmata.Partition.PrefixBlockSampling
import RegularityLemmata.Partition.BalancedSlicing
import RegularityLemmata.Partition.SlicingThreshold
import RegularityLemmata.Partition.AverageSlicing
import RegularityLemmata.Partition.CommonBlocks
import RegularityLemmata.Partition.AbsorbLeftover
import RegularityLemmata.Graph.Uniformity
import RegularityLemmata.Graph.UniformSlicing
import RegularityLemmata.Graph.UnionCenter
import RegularityLemmata.Graph.UniformUnion
import RegularityLemmata.Graph.PieceSupplier
import RegularityLemmata.Graph.PieceExtraction
import RegularityLemmata.Graph.PieceSchedule
import RegularityLemmata.Graph.Variance
import RegularityLemmata.Graph.Increment
import RegularityLemmata.Graph.BadMass
import RegularityLemmata.Graph.BadMassDiag
import RegularityLemmata.Graph.FamilyRegularity
import RegularityLemmata.Graph.FamilyRefinement
import RegularityLemmata.Graph.Atomise
import RegularityLemmata.Graph.EquitableChunk
import RegularityLemmata.Graph.EquitableChunkApprox
import RegularityLemmata.Graph.EquitableStep
import RegularityLemmata.Graph.EquitableFamilyRegularity
import RegularityLemmata.Graph.TripleSeed
import RegularityLemmata.Graph.Regularity
import RegularityLemmata.Graph.RegularityDiag
import RegularityLemmata.Graph.Bridge
import RegularityLemmata.Graph.RemovalBridge
import RegularityLemmata.Graph.CutNorm
import RegularityLemmata.Graph.FriezeKannan
import RegularityLemmata.Graph.Strong
import RegularityLemmata.Graph.FamilyStrong
import RegularityLemmata.Graph.StrongTypicality
import RegularityLemmata.Graph.RegularDegree
import RegularityLemmata.Graph.RepeatedCellCounting
import RegularityLemmata.Graph.PathCounting
import RegularityLemmata.Graph.TriangleCounting
import RegularityLemmata.Hypergraph.Uniform
import RegularityLemmata.Hypergraph.Colored
import RegularityLemmata.Hypergraph.Copies
import RegularityLemmata.Hypergraph.Polyad
import RegularityLemmata.Hypergraph.PolyadRegularity
import RegularityLemmata.Hypergraph.PolyadEnergy
import RegularityLemmata.Hypergraph.PolyadWitness
import RegularityLemmata.Hypergraph.PolyadIncrement
import RegularityLemmata.Hypergraph.Triad
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
import RegularityLemmata.Relational.Indivisible
import RegularityLemmata.Relational.CellwiseEdit
import RegularityLemmata.Relational.TwoVertexCounting
import RegularityLemmata.Relational.ThreeVertexCounting
import RegularityLemmata.Relational.TransversalCounting
import RegularityLemmata.Relational.StrongCountingLifting
import RegularityLemmata.Relational.BinaryStrongRegularityCharge
import RegularityLemmata.Relational.BinaryStrongCounting
import RegularityLemmata.Relational.DiagonalGate
import RegularityLemmata.Relational.GraphCounting
import RegularityLemmata.Relational.BinaryDiagRegularity
import RegularityLemmata.Relational.BinaryDiagStrong
import RegularityLemmata.Kernel
import RegularityLemmata.FiniteSetSystems
import RegularityLemmata.RelationalApproximation

/-!
# RegularityLemmata

A Lean 4 library of reusable finite regularity, counting, approximation, and removal
infrastructure, built on mathlib.

This root imports the library's public surface. Three curated facades bundle stacks a consumer
often wants whole: `RegularityLemmata.Kernel` (rectangular weighted kernels),
`RegularityLemmata.FiniteSetSystems` (relation fibers, traces, and VC bounds), and
`RegularityLemmata.RelationalApproximation` (homogeneous cells, indivisibility, and cellwise
edit bounds). The probe and obstruction-gate modules of in-progress campaigns live under the
separate umbrella `RegularityLemmataGates` — same namespace, proof gates, and CI, but not part
of this import; each stays directly importable by its module name.
See `README.md` for scope and `ARCHITECTURE.md` for the library's conventions.
-/

namespace RegularityLemmata

/-- Library version marker. Also guarantees the axiom audit always has at least one
declaration to check. -/
def version : String := "0.4.0"

end RegularityLemmata
