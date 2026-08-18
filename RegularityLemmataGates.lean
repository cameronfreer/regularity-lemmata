/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.InducedRemovalGates
import RegularityLemmata.Relational.Transversalization
import RegularityLemmata.Relational.OrientationProbe
import RegularityLemmata.Relational.CloneProxyProbe
import RegularityLemmata.Relational.ProxyMove
import RegularityLemmata.Relational.ProxyGroupingGate
import RegularityLemmata.Relational.RepresentativeSelection
import RegularityLemmata.Relational.PlacementStrata
import RegularityLemmata.Relational.ProxyEventIndex
import RegularityLemmata.Relational.ProxyAggregateMass
import RegularityLemmata.Relational.ProxySelectionSetup
import RegularityLemmata.Relational.ProxyCostBudget
import RegularityLemmata.Relational.ProxySelectionConstants
import RegularityLemmata.Relational.ProxyHierarchyBridge
import RegularityLemmata.Relational.ProxyNormalizedCostGate
import RegularityLemmata.Relational.ForbiddenForkGate
import RegularityLemmata.Relational.WeakenedCountingGate
import RegularityLemmata.Relational.GenericTripleEstimate
import RegularityLemmata.Relational.PositivityGate

/-!
# RegularityLemmataGates

The umbrella for the library's **probe, obstruction-gate, and feasibility modules** — the
machine-checked record of the in-progress induced-removal campaign (the Phase 11 feasibility
units and the route (b) ladder of `ARCHITECTURE.md`), kept out of the main
`RegularityLemmata` import so that the public surface imports only settled API.

These modules are full library members: same namespace, same proof and axiom gates, same CI
(this umbrella is a build target alongside the main root, and the axiom audit walks both).
Each remains directly importable by its own module name. What distinguishes them is *role*,
not rigor: they pin normalization decisions, refute tempting simplifications, and test
feasibility questions for work that is not yet a theorem — so their statements are shaped by
the questions they answer, not by consumer needs, and nothing here is a stable public API.

`Relational/DiagonalGate.lean` stays on the main surface despite its name: it is a
load-bearing Phase 10 counting bridge, imported by `Relational/GraphCounting.lean`.
-/
