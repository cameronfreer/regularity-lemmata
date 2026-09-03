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
  `exists_isIndivisibleFor_of_isHomogeneousCell`, and its exact converse.

The triple a consumer typically concludes with is `N.IsIndivisibleFor P`,
`NullaryCompatible M N`, and `CellwiseEditBound M N P ε`.
-/
