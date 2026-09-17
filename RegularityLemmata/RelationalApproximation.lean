/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.HomogeneousPair
import RegularityLemmata.Finite.HomogeneousCell
import RegularityLemmata.Partition.HomogeneousPartitions
import RegularityLemmata.Relational.Language
import RegularityLemmata.Relational.Model
import RegularityLemmata.Relational.Transport
import RegularityLemmata.Relational.Indivisible
import RegularityLemmata.Relational.Edit
import RegularityLemmata.Relational.CellwiseEdit
import RegularityLemmata.Relational.MajorityAssembly
import RegularityLemmata.Relational.DisplacedTransport
import RegularityLemmata.Relational.AggregationBridge

/-!
# Facade: the relational approximation stack

One import for approximating a finite relational model over a partition — the substrate a
stable (or otherwise structured) regularity development concludes into. A **facade** imports a
curated stack and defines nothing; each listed module remains directly importable.

* `Finite.HomogeneousPair`, `Finite.HomogeneousCell` — `ε`-homogeneous rectangles and `n`-index
  cell boxes, with the exact subcell laws, the `n`-box perturbation bound, the trivial `1/2`
  and exact singleton endpoints, and the relative-growth transfer at `cX + cY + 2·cX·cY`.
* `Partition.HomogeneousPartitions` — `AreHomogeneousPartitions`, the cellwise lift to a pair
  of independent partitions, with a **single** output tolerance, its monotonicity, transpose
  and complement equivalences, and the exact `⊥` and indiscrete endpoints.
* `Relational.Language`, `Relational.Model`, `Relational.Transport` — finite relational
  languages with a stored arity bound, computable finite models, and their pullback,
  restriction, and relabeling API. In particular, the facade exposes the complete
  `FiniteRelModel.binaryRel` adapter and its transport laws.
* `Relational.Indivisible` — cellwise-constant (indivisible) relations and models over a
  partition, the quotient reading and the packaged quotient model `FiniteRelModel.quotient`
  with its all-or-nothing count, and `NullaryCompatible` for the exact arity-0 layer.
* `Relational.Edit` — the per-symbol and aggregate edit calculus (ordered, diagonal-inclusive
  per-symbol edit sets as the primitive; the frozen cross-arity aggregate) and the
  **count-transfer surface**: `abs_inducedEmbeddingCountOn_sub_le_editMass`, which moves an
  induced pattern count across an edit at cost `Σ_R k^(arity R)` times the `s`-box edit mass
  times `|s|^(k−1)` under nullary agreement, and its full-carrier form.
* `Relational.CellwiseEdit` — `CellwiseEditBound` (positive-arity cellwise `ε`-closeness, a
  packaged interface over the pinned edit machinery), the computable
  `FiniteRelModel.majorityRound`, the exact box-level identity
  `editDistance_majorityRound_eq_min`, the rounding theorem
  `exists_isIndivisibleFor_of_isHomogeneousCell`, its exact converse, and the exact
  cellwise-to-aggregate conversion `CellwiseEditBound.editDistance_const_le`.
* `Relational.MajorityAssembly` (with its substrate `Finite.SectionDefect` and
  `Finite.ProductHybrid`) — the **majority-rounding cost from summed coordinate defects**: the
  box-level identity `editDistance_majorityRound_eq_minorityCount`, the ambient
  part-resampling defect `partResampleDefect` and its reassembly across cell boxes, the global
  bound `editDistance_majorityRound_le_sum_partResampleDefect`, the inclusive-decency form
  `editDistance_majorityRound_le` at `(n+1)·|s|^(n+1)·(2θ + γ/2 + λ/2)`, the labelled-fibre
  adapter `labelPartition` (unused labels allowed) with its reassembly over label tuples, and
  the exact nullary copy.
* `Partition.RepresentativeMap`, `Relational.DisplacedTransport` — the **owner/displacement
  contract** `RepresentativeMap P Q` (a representative map constant on the new parts, a
  displaced set `D`, old label = owner (new label) outside `D`), kept distinct from the
  almost-refinement charge with one-way bridges in each direction (`ofExceptional`,
  `exceptionalMass_le_mul_card_displaced`) and the crossing regression; the equitable
  construction `exists_equitable_representativeMap` (`t` parts, `|D| ≤ #P.parts·⌊|s|/t⌋`,
  crossing parts owned by a designated old part); transport `FiniteRelModel.transportAlong`
  (the pullback along the representative map, indivisible for the new partition, exact on
  nullary symbols) with the displaced-coordinate edit bound `(n+1)·|D|·|s|^n`; and the
  composition `exists_equitable_isIndivisibleFor` giving one shared equitable partition and one
  model for all symbols.

* `Relational.AggregationBridge` — the **approximation-to-counting bridge**: the raw,
  denominator-free aggregation `abs_inducedEmbeddingCountOn_sub_sum_est_le` (a supplied
  single-tuple local estimate in, a global induced count out, with the positional lift and the
  diagonal charge computed), its normalized corollary over the restricted falling factorial
  `(|s|)_k`, the arity-2 (exact) and arity-3 (`δ = 7·ε`) wrappers, and the **composite**
  approximation-to-counting theorem chaining edit transfer with quotient counting
  (`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass`, its cellwise-edit-bound
  and majority-rounding forms, and the normalized composite).

The triple a consumer typically concludes with is `N.IsIndivisibleFor P`,
`NullaryCompatible M N`, and `CellwiseEditBound M N P ε`.
-/
