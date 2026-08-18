/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.HomogeneousPair
import RegularityLemmata.Finite.HomogeneousCell
import RegularityLemmata.Relational.Language
import RegularityLemmata.Relational.Model
import RegularityLemmata.Relational.Indivisible
import RegularityLemmata.Relational.CellwiseEdit

/-!
# Facade: the relational approximation stack

One import for approximating a finite relational model over a partition — the substrate a
stable (or otherwise structured) regularity development concludes into. A **facade** imports a
curated stack and defines nothing; each listed module remains directly importable.

* `Finite.HomogeneousPair`, `Finite.HomogeneousCell` — `ε`-homogeneous rectangles and `n`-index
  cell boxes, with the exact subcell laws and the `n`-box perturbation bound.
* `Relational.Language`, `Relational.Model` — finite relational languages with a stored arity
  bound, and computable finite models.
* `Relational.Indivisible` — cellwise-constant (indivisible) relations and models over a
  partition, the quotient reading, and `NullaryCompatible` for the exact arity-0 layer.
* `Relational.CellwiseEdit` — `CellwiseEditBound` (positive-arity cellwise `ε`-closeness, a
  packaged interface over the pinned edit machinery), the computable
  `FiniteRelModel.majorityRound`, the exact box-level identity
  `editDistance_majorityRound_eq_min`, the rounding theorem
  `exists_isIndivisibleFor_of_isHomogeneousCell`, and its exact converse.

The triple a consumer typically concludes with is `N.IsIndivisibleFor P`,
`NullaryCompatible M N`, and `CellwiseEditBound M N P ε`.
-/
