# Design: relational induced removal (three vertices)

Work in progress. Nothing here is a theorem; theorems live in the library and their
conventions in [`ARCHITECTURE.md`](../../ARCHITECTURE.md). This document records the target,
what is fixed, what is proved, what is currently being built, what has been ruled out, and
what is still owed.

Each rejected route appears once, described by the mathematical obstruction that killed it.
Git history and issues preserve the order in which things were discovered; that order is not
reproduced here.

## 1. Goal

Induced removal for three-vertex binary-palette patterns, in two forms produced by **one**
construction: a fixed pattern `P : FiniteRelModel L (Fin 3)`, and an arbitrary `ι`-indexed
family `F : ι → FiniteRelModel L (Fin 3)` with **no** finiteness or decidability assumption
on `ι`.

One cleaned model `N` is constructed independently of the family. A **pattern-uniform
certificate** — any three-vertex pattern occurring in `N` had strictly more than `δ·|V|³`
induced copies in `M`, on large hosts — yields the family summit pointwise and the
fixed-pattern theorem via a singleton index. If the family corollary ever becomes
substantial, pattern dependence has leaked into the construction: stop and re-examine.

The removal modulus depends on `L` and the edit budget `ε` only — never on the carrier, the
index type, the family size, or the particular patterns.

The provisional shape, recorded for orientation and **not** frozen:

```lean
∀ ε > 0, ∃ δ > 0, ∀ {ι V} [Fintype V] [DecidableEq V]
  (F : ι → FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V),
  (∀ i, (inducedEmbeddingCount (F i) M : ℝ) ≤ δ * (Fintype.card V : ℝ) ^ 3) →
  ∃ N, relativeAggregateEdit M N ≤ ε ∧ ∀ i, inducedEmbeddingCount (F i) N = 0
```

## 2. Fixed normalizations

- **Edit measure**: the frozen `relativeAggregateEdit`, over all arities, with the
  cross-arity weighting of the relational substrate. A binary-only measure is **false**: in a
  unary-only language a rare-profile pattern has order `n²` copies removable only by unary
  edits.
- **Guard-free endpoint**: the smallness hypothesis uses `≤` and the certificate is strict,
  so the empty-host, nonempty-family instance is a meaningful theorem rather than vacuous at
  the zero-denominator endpoint. A small-host branch handles the rest by making the modulus
  small against `(N₀+1)⁻³`, forcing the `ℕ`-valued count to zero.
- **Statement-side minimalism**: `AtMostBinary L` is a hypothesis of every summit; `N` is an
  arbitrary `FiniteRelModel L V`; the host is the full carrier. Swap-consistency, profile
  preservation and the like are proof artifacts of the cleaning, never statement-side
  constraints.
- **Three-layer cleaning.** (1) Nullary relations are preserved exactly. (2) Exceptional
  vertex-profile cleaning covers unary values **and** binary loops, by absorbing small or
  exceptional-profile coarse cells into a maximal proxy cell; pairs involving absorbed
  vertices are classified by their **post-absorption** proxy labels. (3) Off-diagonal
  pair-palette cleaning respects the reversal law and is **representative-driven** in both
  the threshold and the replacement palette: keep a pair whose existing palette has
  representative density `≥ θ`, otherwise recolor to the representative-majority palette.
  For a diagonal coarse pair the recolor target is a palette **orbit** `{c, swap c}`,
  oriented by a local non-instance ordering of distinct host vertices, since a constant
  palette on `(C,C)` must be symmetric while the dense object may be an asymmetric orbit.

  The replacement must not be the **coarse**-majority palette: on a deviant pair that palette
  can have zero representative density, destroying the freeness certificate even though its
  edit cost is duly charged.

## 3. Proved inputs

Available from the library, with constants visible in their statements:

- Equitable regularity for a finite family of relations, with a part count divisible by
  three (`exists_familyRegular_equipartition_triple`), and the piece supplier producing large
  equal-size regular pieces (`exists_pieceFamily`).
- Simultaneous palette regularity with a host-independent bound, and the strong palette
  witness, which takes its requested deviation parameter as an input.
- Three-vertex induced counting against a strong palette witness, with explicit regularity,
  density-shift, and diagonal-cell error terms.
- Grouping of an already-regular equipartition into owners
  (`exists_triple_grouping`), and the proxy event index over ordered distinct proxy pairs.
- Abstract weighted selection with a forbidden-event channel, a cost channel, and a
  cost-only form whose conclusion carries no conditioning factor.
- Aggregate mass reindexings over proxy pairs — nonuniform and deviant — each charged once,
  with no event-count multiplier.
- The **indexed-box triple estimate**: cells of a partition index the triples and carry the
  disjointness and the mass accounting, while the box counted at a cell `C` is any `g C ⊆ C`.
  With a bad-pair set `D` of **cell** pairs covering every failure of the three required
  palette-uniformity conditions **on the boxes**, asked only of distinct cells, and carrying
  cell-weighted pair mass at most `β·|s|²`, the representative count differs from its density
  estimate by at most `(7ε + 3β)·|s|³`. No covering hypothesis is needed: a box may be a
  small fraction of its cell. The partition estimate is the case `g C = C`.

## 4. Current construction

Proxies are obtained by **grouping** the cells of an already-regular equipartition in threes,
not by splitting its cells: a sibling pair is then a pair of distinct cells and so an
ordinary off-diagonal event.

Selection assigns each proxy one representative fine cell, by weighted choice over candidate
cells whose size is comparable to their proxy's. Both charges are weighted by the proxy
pair's own normalized mass, and the cancellation is done coordinatewise against the two
candidate weights rather than against a common size floor, which keeps the proxy count out of
both budgets:

| Charge | Budget |
| --- | --- |
| Simultaneous palette nonuniformity | `4·K·ε` |
| Density deviation | `4·K·δ/η²` |

With uniformity charged rather than forbidden, the forbidden-event type is empty, the
conditioning factor is `1`, and the combined target is `4·K·ε + 4·K·δ/η²` — undoubled. Here
`K` is the palette count and enters as a union-bound multiplicity over colours, not as any
count of events or cells.

## 5. Permanent obstruction gates

Each is retained in the library as a machine-checked example, counterexample, or limitation
— several share a module, one is positive, and one records what it does not prove. They are
what stops a closed question from being reopened.

| Gate | Obstruction |
| --- | --- |
| **G-S1** | Weighted bad mass is not an unweighted bad-pair count. Equal cell sizes are what convert one into the other; without them the supplier's Markov step is unavailable. |
| **G-S2** | The piece supplier is false at a zero target: `0 < t` is required, and the zero-target instance is refuted. |
| **G-U3** | Directed pair densities are not reversal-invariant, so no argument may silently symmetrize a palette. |
| **G-U5** | For arbitrary directed relations, the union of pairwise-regular pieces with close densities is **not** self-regular. This refutes the directed reading of the Conlon–Fox Lemma 3.6 composition, and closes the self-regular-subset route here. Diagonal-inclusive regularity cannot repair it: for a strict order, `(W,W)` fails `1/4`-uniformity whenever `|W| ≥ 2`, so a diagonal-inclusive regular partition below that tolerance is almost all singletons. |
| **G4** | A planted within-cell copy is invisible to transversal counting. An edit charge on a diagonal cell does not by itself retire repeated-cell counting: the triple still induces *some* pattern. |
| **G10** | Role consistency is obtained by one representative shared by every role, not by self-regularity of a representative set. |
| **G-P1** | Splitting a cell of a regular partition does not inherit sibling-pair regularity: off-diagonal regularity of the original says nothing about two subsets of one cell. This is why proxies group rather than split. |
| **G-P2** | Two distinct cells of a partition are exactly the configuration off-diagonal regularity speaks about — the positive counterpart of G-P1. |
| **G-H1** | The `P`-dependent deviation requirement admits no positive parameter that works uniformly over all proxy counts. Stated for arbitrary positive counts, not for counts realized by a partition; it therefore constrains what the construction must supply, and does not by itself exhibit a produced counterexample. |
| **G-H2a** | A partition refining another can have strictly more parts, so seeding a witness at a bounded equipartition transports neither its count bound nor its equitability. |
| **G-H2b** | The only coarse-count bound the witness producer offers is antitone in the deviation parameter, so deriving that parameter from a target bound and then demanding the produced count respect it moves both sides the same way. |
| **G-Q1** | A conditional limitation on the positivity margin `(2q)³·(7ε + 3β) < ρ³α³`. If the `q` in use satisfies `c/ε ≤ q`, the left side is at least `56c³/ε²` and shrinking `ε` makes the margin worse — the shape of G-H2b, now on `q`. It does **not** show the construction must use such a `q`: the candidate API asks only `#F.parts ≤ q`, an upper bound, and a trivial relation stays regular at constant part count. It applies to any `q` known to satisfy an inverse-linear lower bound; no such bound is proved here for the iteration's a priori majorant. |
| **Branch A** | An exact equipartition refining the profile partition collapses as soon as one vertex has a unique profile: its class is a singleton, so every part has size at most two and the part count is linear in the host, forcing a fine tolerance of order `|s|⁻²`. A unique profile is generic — one vertex distinguished by its loop data suffices — so the combination of exact equipartition, profile refinement, and host-independent complexity is unavailable. |

## 6. Open certificates

- **Transversalization.** A pattern-uniform certificate that a positive global induced count
  forces a positive transversal one. G4 is why this is needed and why a diagonal edit charge
  does not substitute for it.
- **Surviving-triple count.** Under the charged rather than forbidden treatment of
  nonuniformity, the conclusion available to the summit is that the bad proxy pairs carry
  small normalized mass, not that there are none. Whether the three-vertex count stays
  positive under that weakening is the decisive open question.
- **Transversal rounding certificate**, and **profile homogenization**, which is a rounding
  obligation rather than a selection one.
- **A producer** delivering one witness coarse partition with both a usable count bound and
  the size facts the local budgets consume — or a formulation that needs neither.
- **A way to meet the margin.** Known routes: use the REALIZED fine part count rather than
  the a priori majorant, or a candidate-size guarantee sharper than `|C| ≤ 2q·|g C|`; a
  representative-density floor `ρ` or proxy-size floor `α` improving with `q` fast enough to
  absorb `q³`; a lower bound on the count not routed through the density estimate; or an
  error term not proportional to `|s|³`. G-Q1 constrains only a `q` with a known inverse-linear
  lower bound, so this is an open obligation rather than a closed obstruction. Supplying such
  a bound for the a priori majorant — under whatever conditions it needs, a nonempty partition
  and `0 < ε ≤ 1` among them — would sharpen the gate; it is not proved here.

## 7. Explicit non-goals

- Patterns on carriers other than `Fin 3`, including two-vertex removal.
- Languages varying after `ε`, or moduli depending on the family: the language is fixed
  before `ε`, and the family is quantified after it and may be arbitrary.
- Property-testing formulations.
- Arity `> 2`, and hypergraph removal.
- Quantitative optimality of the modulus.
- Equitable strong regularity — this route avoids it.
- Deletion-only edits, box-relative removal, and computable cleaning.
