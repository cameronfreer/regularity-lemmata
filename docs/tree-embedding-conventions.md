# Tree-embedding conventions

`exists_properEmbedding_of_child_branches` in
`RegularityLemmata/Finite/BinaryTreeProperEmbedding.lean` converts the
immediate-child convention into `ProperEmbedding`.

The input is a word map on nodes of depth at most `s`, taking internal nodes
to depth strictly less than `t`, with

```
f (x ++ [b]) = f x ++ [b] ++ w
```

for some suffix `w` at each internal node and each Boolean `b`.
The output is a proper embedding of height `s` into height `t`, with the
same internal-node map. There is no depth shift. Its leaves are extended
to full host depth `t`, so the original leaf images are not asserted to
be preserved. Internal-node monochromaticity transfers without any loss.

A synchronized-level regular embedding supplies these hypotheses: its
strictly increasing level map makes internal nodes internal, and its
child law is exactly the displayed equality. Synchronization is stronger
than the assumptions used by this bridge. `ProperEmbedding` does not
require equal-depth nodes to land at equal depths, so the bridge is not
an equivalence of conventions.

Consequently `binaryTreeRamsey_proper_const` supplies a proper embedding
at source height `t + 1` and host height `m * t + 1`; it does not, merely
by this bridge, supply a synchronized-level regular embedding. A Ramsey
theorem supplying regular embeddings can be read as a proper-embedding
theorem at its own height bound. No comparison of those height bounds,
converse conversion, or new Ramsey theorem is claimed here.

Validation: the bridge elaborates against Lean 4.34.0-rc1, with exactly
`propext`, `Classical.choice`, and `Quot.sound` in its axiom print.
