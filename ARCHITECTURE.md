# Architecture and conventions

These conventions are frozen. Changes require an explicit owner decision recorded here.

## Type policy

- **Raw counts live in `ℕ`.** Cardinalities, edit distances, and tuple counts are natural
  numbers.
- **Normalized densities and errors live in `ℝ`.** There is no pervasive `ℚ → ℝ` cast
  layer. Where mathlib's API is `ℚ`-valued (e.g. `SimpleGraph.edgeDensity`,
  `Finpartition.energy`), a bridge states exactly one `Rat.cast` equation at the boundary.

## Denominator policy

- Densities are **zero on an empty denominator**, via real division's `x / 0 = 0`.
  Definitions carry no `if`-guards for emptiness.
- Denominator positivity or support nonemptiness is required as an **explicit
  hypothesis exactly where it is genuinely necessary** — in particular for complement
  and cancellation statements (`d(p) + d(¬p) = 1` is false on the empty support). It is
  NOT added categorically: conversion inequalities such as
  `c ≤ densityOn S p → c·|S| ≤ #filter` hold unconditionally under the convention
  (`c · 0 ≤ 0`), and are stated guard-free.

## Injectivity policy

- All copy-counting intended for removal arguments uses **injective source tuples**.
  Diagonal-sensitive variants must be separate, clearly named, and require exact diagonal
  control. Collision (non-injective) mass is bounded explicitly and loses one ambient
  power of the host size.

## Partition conventions

- Partitions are mathlib `Finpartition`s; the library never introduces a private
  partition type.
- **`P ≤ Q` means `P` is finer than `Q`** (mathlib's order).
- **Energy is mass-weighted.** The partition energy is
  `Σ_{A,B} (|A||B| / |s|²) · d(A,B)²`, **including diagonal blocks**. This is the
  refinement-monotone quantity; the uniform block-mean of `d²` is *not*
  refinement-monotone and is never used as the primary notion. Mathlib's
  `Finpartition.energy` (uniform, `ℚ`-valued, off-diagonal) is bridged only where both
  sides speak `SimpleGraph`.

## Statement discipline

- **No `sorry`, `admit`, or custom `axiom` on committed branches.** All declarations use
  only the standard axioms `propext`, `Classical.choice`, `Quot.sound`
  (enforced by `scripts/check.sh`, which audits every declaration in the library
  namespace).
- **No contentless `Prop` placeholders.** An unproved major result is never represented
  by defining a large `Prop` and treating it as available.
- Major statements pass, in order: a mathematical statement review; small finite
  counterexample tests; a dependency audit; and only then an API freeze.
- Search mathlib before introducing every foundational definition; wrap rather than
  reprove.

## Code organization

- Files stay focused, generally below 600 lines.
- Each file ends with a `/-! ### Tests and adversarial examples -/` section exercising
  its API on small finite types (kernel `decide` preferred; `native_decide` only in
  anonymous `example`s).
- Every green semantic unit becomes a commit and is pushed immediately. Pushed history
  is never rewritten.

## Deferred summit statements

Intended results whose proofs are not yet complete are recorded here as prose — never as
Lean `Prop` placeholders.

- **Self-regular almost-refining equipartition**: the proved
  `exists_regular_refinement_and_almostRefining_equipartition` produces a regular exact
  refinement `Q ≤ P₀` plus an equipartition `E` almost-refining both. The stronger
  version in which `E` is *itself* regular requires running equitabilisation
  inside the energy-increment loop (transporting the energy across the exceptional
  mass) and is deferred.
- **Strong-witness counting**: a counting theorem that genuinely consumes a
  `StrongWitness` (edge, triangle, path, and induced three-vertex pattern counts with
  explicit error scales), followed by induced graph counting and finite-family induced
  removal. This is the remaining Phase 4d sub-stage; its statements will be frozen only
  after their falsification gates.
- **Triadic regular approximation** and **colored arity-three counting/removal**:
  planned for later releases; statements will be frozen only after their falsification
  gates. The triadic design choices are frozen below.

## Phase 7 design freeze (triadic regular approximation)

Target: a **weak pair-coloring regularization theorem** using the Rödl–Schacht index
and polyad test surfaces — a *precursor to, not a formalization of*, the full
regular-partition theorem of V. Rödl, M. Schacht, *Regular partitions of
hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007) (their result
concerns families of compatible hypergraph partitions with equitable vertex
partitions, which are deliberately deferred here). Test surfaces are the local
parent-relative predicates `IsDiscRegularAt`/`IsPolyadRegularAt`
(`Hypergraph/PolyadRegularity.lean`), with the canonical own-density form
`IsLocalDiscRegular`. The following choices are frozen in prose first; the summit
statements stay prose until their falsification gates pass.

- **Unordered triads, ordered counting.** The objects are unordered
  `UniformHypergraph 3 V`; every counting and testing surface is ordered injective
  triples, mediated by the realization identity `orderedCount = 3! · #edges`
  (`orderedCount_eq`). Observables on triples are set-level
  (`triadObs H v = tupleRange v ∈ H.edges`), hence permutation-invariant by
  construction. Ordered face/triad structures, if ever wanted, are exposed
  separately, never as this API.
- **Input and edited hypergraphs** are both `UniformHypergraph 3 V`; the edit
  primitive is the unordered symmetric difference of edge sets
  (`UniformHypergraph.symmDiff`).
- **Edit normalization and the factor 6.** The primitive edit count is unordered
  (`editCount H G = #(H ∆ G)`); the ordered edit mass over injective triples equals
  `6 · editCount` — proved (the realization identity applied to `symmDiff`), never
  assumed. Relative quantities divide by `|V|³` under the guard-free `x / 0 = 0`
  convention, not by the injective-tuple count; the injective/total gap is controlled
  by the Phase 1 collision bounds where needed.
- **Regularity thresholds are parent-relative** — a `δ` fraction of the parent polyad
  block, never an absolute count. No absolute thresholds appear in Phase 7
  statements (`IsBlockUnionRegular` is not used by Phase 7).
- **Exceptional triad mass** is ordered and diagonal-free: for a set `E` of keys, the
  mass is `Σ_{key ∈ E} |polyadBlock κ key| / |V|³`. A pair coloring is `δ`-good for
  `H` when the keys on which the required block control fails carry mass at most `δ`.
- **Partition data.** The first release quantifies over pair colorings
  `κ : RSet 2 V → Fin K` only. Compatibility with an equitable vertex partition (and
  equitability of pair cells over vertex-cell triples) is required for the full
  Rödl–Schacht statement but not for the weak (energy-increment) approximation; it is
  a deferred strengthening, to be built on `Partition/Equitable.lean`.
- **Quantifier order (error schedule and bounds).** `∀ δ > 0, ∃ K₀ = bound(δ)`
  host-independent; `∀ H` on a finite `V`, `∃ K ≤ K₀` and a pair coloring `κ` with
  `K` cells satisfying the goodness conclusion. Iteration schedules follow the graph
  ladder's `ErrorSchedule` pattern (`Graph/Strong.lean`). **No quantitative bound is
  frozen yet**: a failing local disc test yields roughly a `δ³` energy gain on its
  block and hence roughly `δ⁴` globally when bad keys carry mass `> δ`, but
  simultaneously resolving witnesses across up to `K³` keys can multiply the pair
  colors by roughly `2^{O(K³)}` per round (a recurrence like `K ↦ K · 2^{3K³}`, not
  a single exponential). The bound is frozen only after Unit 4 derives the actual
  increment and cardinality recurrence.
- **Two summit statements, in order.** First the weak regularization **without
  editing**: `∃ κ` with boundedly many pair colors such that
  `badTriadMass H κ δ ≤ δ` (bad keys are `IsBadTriad`, failures of the own-density
  local predicate; the mass is the frozen ordered normalization). Then the **edited
  regular approximation** as a corollary: `∃ κ G` with
  `6 · editCount H G ≤ δ · |V|³` (the frozen ordered edit inequality) and every
  realized key locally disc-regular for `G` — with `G` constructed by deleting or
  otherwise homogenizing the exceptional blocks, which requires the permutation
  closure of bad keys (`isBadTriad_comp_perm_iff`) so that all six ordered
  presentations of an unordered triple receive the same edit decision.

Planned units, in order: (1) realized triads and mass identities ✓; (2) block
density/edit calculus ✓; (3) refinement energy for pair colorings (mass-weighted,
diagonal included, refinement-monotone, with the exact variance identity
`polyadEnergyNum_comp_variance`) ✓; (4) one-step repair — bad-key mass and
permutation closure ✓, witness selection for failed local regularity ✓
(`DiscWitness`, `exists_discWitness`), simultaneous witness atomisation with its
color-count recurrence ✓ (`cutRefine`, `cutBound j K = K·2^{K^{j+1}(j+1)}` proved by
construction), witness atoms as unions of refined blocks ✓
(`discAtom_eq_biUnion_cutRefine` over `resolvingKeys`, with cardinality corollaries);
remaining: a local increment theorem (`δ³·|block| < local refinement variance` at a
bad key, strict via `DiscWitness.deviates`) AND a simultaneous global increment from
excessive bad mass (`δ⁴ < polyadEnergy refined − polyadEnergy coarse` when
`δ < badTriadMass`; a one-key increment is insufficient: a single bad block may have
arbitrarily small mass); (5) bounded iteration — fuel `≈ ⌈1/δ⁴⌉`, color bound by
iterating `cutBound 2` from `1`, stopping theorem, then freeze that exact
recurrence; (6) summits as above, with deletion defined by an existential ordering of
each unordered edge (permutation closure keeps it well-defined and computable).
