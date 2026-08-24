/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.MulticolorRamsey
import RegularityLemmata.Finite.FullBinaryTree
import RegularityLemmata.Finite.BinaryTreeEmbedding
import RegularityLemmata.Finite.BinaryTreeProperEmbedding
import RegularityLemmata.Finite.BinaryTreeRamsey

/-!
# Finite Ramsey theory

The library's finite Ramsey results behind one import.

## What is here

* `Finite/MulticolorRamsey.lean` — multicolour Ramsey for a colouring of **ordered pairs**, by
  greedy pigeonhole, with an explicit single-exponential bound. No symmetry is assumed.
* `Finite/FullBinaryTree.lean` — the full binary tree of height `h` as the words of length at
  most `h`, with ancestry and branch direction as relations on words.
* `Finite/BinaryTreeEmbedding.lean` — subtree embeddings on internal nodes: arbitrary root,
  branch direction preserved, depth unconstrained.
* `Finite/BinaryTreeProperEmbedding.lean` — the same with the leaf level covered, and the
  extension of an arbitrary internal embedding through it.
* `Finite/BinaryTreeRamsey.lean` — the additive two-colour subtree theorem: a colouring of the
  internal nodes of a height-`a + b + 1` tree admits a colour-`0` subtree of height `a + 1` or a
  colour-`1` subtree of height `b + 1`.

## What they share, and what they do not

Both halves are colour-avoidance statements about a finite structure with an explicit witness,
and neither depends on the other: the pair colouring lives on an unstructured vertex set, the
tree colouring on the interior of a binary tree. They are bundled because a consumer reaching
for one commonly wants the other in view, not because either is built from the other.

Neither half carries any stability, VC, ladder, or rank vocabulary. The tree theorem's antecedent
comes from that literature (see `PROVENANCE.md`), but what is formalized here is finite
combinatorics with no such notion in its statement.
-/
