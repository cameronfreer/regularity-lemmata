# Pattern-sensitive extension counts

`Finite/PatternExtensions.lean` proves the all-touched-coordinate bound. For
`x : Fin n -> Fin k`, put `d = |image x|`. The number of functions through `s`
whose composition with `x` belongs to `E` is at most

`|E| * |s|^(k-d)`.

The compatible-coefficient version replaces `E` by its subset satisfying
`x i = x j -> y i = y j`. The assignment-union theorem retains the separate
coefficient and exponent for every assignment. For an injective assignment,
`d = n`. Empty assignments and repeated coordinates are included; the old
one-coordinate theorem is unchanged.

The four declarations compile using the warm v4.34 checkout and the pinned
substrate imports; their axiom sets contain only the standard three. Regressions
cover two distinct pinned coordinates, repeated coordinates, and an empty
assignment. CI remains the integration gate.

## Boundary of a uniform counting corollary

The extension improvement alone does not absorb diagonal atomic edits into
the existing quotient collision charge. Induced counting tests negative atoms
too: a pattern having no loops does not mean that loop tests are omitted.

Here is a mathematical counterexample to such an absorption without further
diagonal control (not asserted as a Lean-certified counterexample here).
Let the host have 10,000 vertices and let `M` be the complete irreflexive binary
relation. Set `N` to the full binary relation. Partition into 100 parts of size
100. The edit set consists of the 10,000 loops. Each diagonal cell changes 100
of its 10,000 pairs, and off-diagonal cells are unchanged. Thus the cellwise
error is at most `epsilon = 1/100`; `N` is indivisible for the partition.

For the two-vertex irreflexive complete pattern, the induced count in `M` is
`10,000 * 9,999 = 99,990,000`. Its count in `N`, and its quotient count, are zero:
the required negative loop atoms fail. A proposed bound

`k^2 * epsilon * |s|^k + choose(k,2) * m * |s|^(k-1)`

with `k=2`, `m=100` is only `5,000,000`. The affected embeddings can use different
parts, so the same-part collision charge does not account for them.

A subsequent transfer theorem must retain the contraction-specific error
terms, or impose agreement on repeated-coordinate tuples (for example, suitable
simplicity assumptions on both models). The general tuple-counting theorem and
the existing counting-transfer recipe remain valid. No host-uniform normalized
counting corollary is claimed by this increment.
