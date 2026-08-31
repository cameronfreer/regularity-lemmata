/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Weight
import RegularityLemmata.Finite.CoordinateSplit
import RegularityLemmata.Finite.ProductBox
import RegularityLemmata.Finite.BoxUnion
import RegularityLemmata.Finite.BoxCoordinateSplit
import RegularityLemmata.Partition.BoxPartition

/-!
# Weighted product spaces

The heterogeneous weighted-box stack behind one import: raw weights, boxes and their masses,
predicate mass and density, independent coordinate partitions, finite unions with a
symmetric-difference error, and the coordinate-split adapter.

## What is here

* `Finite/Weight.lean` — raw weights `w : X → ℝ` and `finsetMass`, with nonnegativity always a
  hypothesis and never a field, plus the generic estimates the box layer rests on:
  subadditivity, the union bound over a finite family, and a mass difference bounded by a
  symmetric difference.
* `Finite/CoordinateSplit.lean` — splitting tuple coordinates into two groups, with the tuple
  factorization `splitEquiv` and the index equivalences that keep every statement cast-free.
* `Finite/ProductBox.lean` — `FiniteBox`, its tuples, `boxMass` as the weighted sum over them
  with the product factorization as a theorem, and `boxPredMass` / `boxDensity` as restrictions
  of that same sum.
* `Finite/BoxUnion.lean` — semantic finite unions of boxes and `boxUnionError`, the weighted mass
  of the tuples covered by exactly one of two families.
* `Finite/BoxCoordinateSplit.lean` — boxes across a split: restriction, gluing, and the mass
  factorization.
* `Partition/BoxPartition.lean` — independent coordinate partitions, their product cells, and the
  exact decompositions of box mass and predicate mass over those cells.

## Why `Finite/CoordinateSplit` is imported explicitly

It arrives transitively through the adapter, but a facade is a **curated contract**, not a
transitive closure. A consumer of this facade needs `CoordinateSplit` to build the arguments the
adapter takes, so the facade promises it directly rather than depending on an import graph that
may change.

## One notion of mass

Every quantity here is the same weighted sum, read over a different set: `finsetMass` over an
arbitrary finset, `boxMass` over the tuples of a box, `boxPredMass` over the tuples satisfying a
predicate, and the union error over a symmetric difference. `boxMass_eq_prod_finsetMass` and
`boxMass_eq_finsetMass_tupleWeight` are the bridges, and there is deliberately no second mass
primitive anywhere in the stack.

## Where the instance profiles differ

`Finite/ProductBox.lean` is deliberately instance-light — `[Fintype ι]` and `[DecidableEq ι]`
only, with **no** decidable equality on the carriers. The two modules that genuinely need
fiberwise `[∀ i, DecidableEq (V i)]` — `Partition/BoxPartition.lean`, where `Finpartition` needs
the lattice on `Finset (V i)`, and `Finite/BoxUnion.lean`, where `biUnion` and symmetric
difference need `DecidableEq (∀ i, V i)` — are separate modules for exactly that reason, so the
cost does not leak backwards onto consumers that never partition or take unions.

## Where nonnegativity enters

Identities are hypothesis-free and hold for **signed** weights: the product factorization, the
complement mass identity, additivity over disjoint families, the cell decompositions, and the
split factorization. Nonnegativity is required only by claims that compare masses of different
sets — monotonicity, subadditivity, union bounds, the triangle inequality — and positivity of a
mass only by statements that divide, namely the density identities for `True` and for
complements. Guard-free `x / 0 = 0` keeps the `[0, 1]` density bound free of any side condition.
-/
