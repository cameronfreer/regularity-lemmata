# Uniform pattern-count transfers

The module `Relational/UniformPatternCounts.lean` supplies the two corollaries
tracked in #197. The old general estimate and counting recipe are unchanged.
Write `C(L,k) = sum_R k^(arity R) = patternAtomCoefficient L k`.
This coefficient includes nullary symbols, harmlessly: their edit contribution
is zero by the explicit compatibility premise.

## Induced counts

`abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement` bounds the count
difference by `C(L,k) * epsilon * |s|^k`. Its premises are nonnegative epsilon,
nullary compatibility, agreement on every repeated-entry tuple through `s`,
and per-symbol box edit mass at most `epsilon * |s|^arity` for positive arity.

The result actually permits arbitrary patterns: diagonal agreement handles
both positive and negative repeated-coordinate atoms. The cellwise wrapper is
`abs_inducedEmbeddingCountOn_sub_le_of_cellwise_diagonalAgreement`.
It retains diagonal agreement as an independent hypothesis. Majority rounding
does not discharge it.

## Homomorphisms

`SimplePattern` says that each true atom uses distinct pattern vertices.
`abs_injectiveHomCountOn_sub_le_of_simple` gives the same uniform bound for
injective preservation-only homomorphisms, with nullary compatibility and no
diagonal-agreement premise.

`abs_homCountOn_sub_le_of_simple` adds exactly
`choose(k,2) * |s|^(k-1)` for all homomorphisms.
The cellwise wrapper is `abs_homCountOn_sub_le_of_cellwise_simple`.
No host-size assumption absorbs the collision term implicitly. The proof bounds
the difference of the two non-injective contributions by their common upper
bound, avoiding an unnecessary factor two.

`homCountOn_univ` and `injectiveHomCountOn_univ` identify the new set-restricted
wrappers with the existing full-carrier counts.

## Verification and conventions

The endpoints and regression clients compile in the warm 4.34 environment.
Only the two new source modules were compiled into that cache; no full dependency
build or release-pin change was performed. All endpoint axiom queries are subsets
of `propext`, `Classical.choice`, and `Quot.sound`. Root classification and its
self-test are local checks; CI remains the merge gate.

The named diagonal-loop regression now also checks that the edge pattern is
simple, that its two hosts fail diagonal agreement, and that the restricted
homomorphism count agrees with the original count of nine. The original
6-to-0, 6-to-6, and 6-to-9 tests remain intact.

These are raw-count inequalities, including empty hosts and zero-vertex
patterns. Dividing by `|s|^k` gives the normalized reading when that denominator
is positive; no convention for division by zero is silently used.

The general induced theorem with contraction-specific error masses remains a
separate later task. The next planned comparison concerns tree embeddings; no
release or publication is authorized by this mathematical increment.
