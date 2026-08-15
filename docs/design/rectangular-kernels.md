# Design: rectangular weighted finite kernels and cut discrepancy

Work in progress. Nothing here is a theorem; theorems live in the library and their
conventions in [`ARCHITECTURE.md`](../../ARCHITECTURE.md). This document records the target,
what is fixed, what has been checked, and where the quantitative seams are.

This is the design freeze for issue #71. Its purpose is to fix the definitions **before**
implementation, because the canonical Frieze–Kannan object is a rectangular weighted kernel
(cf. Frieze–Kannan, *Quick Approximation to Matrices and Applications*), while the library's
current theorem is Boolean, same-carrier, and uses one partition on both coordinates.

## 1. Goal

A cut-discrepancy and Frieze–Kannan theory for

- two carriers `A : Finset α`, `B : Finset β`, with **their own nonnegative weight
  functions** `wA : α → ℝ`, `wB : β → ℝ`;
- a signed kernel `W : α → β → ℝ`, bounded **on `A ×ˢ B` only**;
- **independent** partitions `P : Finpartition A` and `Q : Finpartition B`.

Downstream coverage: bipartite graphs without a disjoint-union encoding, signed matrices and
residuals, weighted graphs, differences of two graphs, adjacency between distinct vertex
classes, and graphon discretizations.

## 2. The three contracts

The most important thing this document fixes is that these are **three separate contracts**,
not one theorem stated three ways. Conflating them loses a quantitative seam.

### 2.1 The rectangular summit

Separate left and right partitions, and **separate left and right part-count bounds**. The
conclusion is a uniform bound on the rectangle discrepancy over all `S ⊆ A`, `T ⊆ B`.

The two bounds are exposed individually. Their product is derivable but is **not** the
primitive form, because the product is exactly where sharpness is lost (§2.2).

### 2.2 The common-refinement adapter

Given the rectangular summit, a same-carrier statement follows by taking a common refinement
`S` of `P` and `Q`. The mechanism is proved, not assumed — see §4 — and decomposes as:

| step | constant |
| --- | --- |
| cut-norm contraction of weighted conditional expectation | **1** |
| triangle inequality `\|D − E[D\|S×S]\| ≤ \|D\| + \|E[D\|S×S]\|` | **2** |

so the adapter calls the rectangular summit at **`ε/2`**.

The part count is the **product** `#P · #Q` of the two sides' bounds, each evaluated at
`ε/2`.

### 2.3 The existing Boolean same-carrier summit

`frieze_kannan` (`Graph/FriezeKannan.lean`) is **kept as the sharper direct summit** and is
quantitatively independent of this track. It is not superseded, not deprecated, and not
re-derived.

## 3. The quantitative seam (read this before claiming a specialization)

The adapter of §2.2 recovers the **discrepancy conclusion** of the existing Boolean theorem.
It does **not** recover its complexity bound.

- **Accurate:** single-exponential dependence on `1/ε²` is preserved.
- **Not accurate:** "the same `4^t` bound". The existing theorem's bound is
  `4^(⌈1/ε²⌉ + 1)`. The adapter evaluates its rectangular bounds at `ε/2`, so `t` is computed
  at `ε/2` rather than `ε`, and the two sides' bounds are then multiplied under common
  refinement. Both effects degrade the constant.

Therefore the relationship between the rectangular track and the existing theorem is
**API compatibility, with an explicitly weaker bound** — not a quantitative specialization.
Any acceptance criterion phrased as "the current theorem is a short specialization" must
exclude the complexity bound, or it is false.

A **synchronized same-carrier weighted-kernel theorem** — one partition on both coordinates
at full weighted generality, recovering a sharp constant — is deliberately out of scope. It
is a separate future issue, to be opened only if a consumer needs that generality. Keeping
§2.3 is the cheaper answer to the sharpness question.

## 4. What has been checked

The same-carrier gate was the real hard stop of the RFC, and it cleared. Writing
`D = W − E[W | P×Q]`, and using that `S×S` refines `P×Q`, the tower property gives
`E[W|S×S] − E[W|P×Q] = E[D|S×S]`, hence

```
W − E[W|S×S] = D − E[D|S×S]
```

so everything reduces to contraction plus one triangle inequality.

**Contraction holds with constant 1.** Stripped of partition bookkeeping it is a bilinear
statement: if every **0/1** (cell-union) rectangle sum of the cell-pair matrix `xᵢⱼ` is
within `ε`, then so is every `[0,1]`-weighted combination `∑ᵢⱼ cᵢ dⱼ xᵢⱼ`. A stepped
rectangle sum is exactly such a combination, with `cᵢ, dⱼ` the relative masses of the test
rectangle inside each cell.

Two facts worth recording because they shape the implementation:

- **No extreme-point machinery is needed.** The pointwise bound `cᵢ·yᵢ ≤ max yᵢ 0` suffices,
  and the maximizing 0/1 choice is the filter `0 ≤ yᵢ`, which is a genuine cell-union
  rectangle. Two applications, one per coordinate.
- **The relative-mass weights land in `[0,1]` guard-free.** On a zero-mass cell the quotient
  is `0/0 = 0`. No positivity hypothesis is needed, and this is consistent with — indeed a
  check on — the zero-block-mass convention of §5.

## 5. Frozen conventions

1. **The raw weighted rectangle sum is primitive.** Average and normalized discrepancy are
   derived from it. Rationale: the raw form is the one that adds across cells, and every
   identity in the substrate is cleanest there.
2. **Kernel boundedness is required only on `A ×ˢ B`.** The bound is a hypothesis about the
   carriers in play, not a global property of `W`. A consumer restricting to subcarriers
   should not have to re-establish a global bound.
3. **Restriction preserves raw weights.** Restricting to `A' ⊆ A`, `B' ⊆ B` carries the
   weight functions across unchanged; it does **not** silently renormalize. Renormalization,
   where wanted, is an explicit separate step.
4. **Zero-total-mass and zero-block-mass averages are `0`.** The library's guard-free
   convention, extended to both carriers. No nonemptiness or positive-mass hypotheses appear
   in the substrate's statements. (§4 confirms this is compatible with the gate.)
5. **Separate left and right part-count bounds.** Never only their product. §3 is the reason.
6. **Positive rescaling of either carrier weight** scales the raw discrepancy by the same
   factor and leaves the normalized energy unchanged. This is the sanity check that the
   normalization is doing what it should.
7. **`op` is involutive and exchanges every left/right construction.** `W.op y x = W x y`,
   with `rectSum`, cut discrepancy, and stepification all transported across it, so that left
   and right statements are never duplicated by hand.
8. **Left and right stepification commute.** They are independent operations; refinement on
   one coordinate must not disturb the other coordinate's statements.
9. **Prefer a stepped predicted-sum definition** over a total pointwise kernel, unless a total
   kernel comes with a clean outside-support convention. A pointwise stepped kernel forces a
   decision about values outside `A ×ˢ B` that the predicted-sum form simply does not have to
   make.

### Style constraint

Raw nonnegative weight functions and total masses, with probability normalization
**derived**. No new probability-measure structure. This matches the existing mass-weighted
`energy`, `pairDensity`, and the relational weight machinery; a measure layer would fork the
library. The same convention is used by the heterogeneous weighted-box work (#83), so the two
substrates compose without an adapter.

## 6. Implementation order

1. **Rectangular kernel substrate and variance identities** — carriers, weights, restriction,
   `op`, `rectSum`, stepification, and the parallel-axis / refinement-variance identities in
   the rectangular weighted setting.
2. **The rectangular weighted FK step theorem** — one step partition pair with uniform cut
   discrepancy, with separate left/right part-count bounds. **More urgent than item 3**,
   because downstream stable regularity consumes the step, not the decomposition.
3. **The cut-matrix decomposition** — a bounded kernel as a sum of `O(ε⁻²)` weighted rectangle
   indicators plus a residual of cut norm at most `ε`, recorded during the greedy residual
   iteration rather than forced through the partition theorem.

Tensor/box FK stays gated until item 2 lands.

## 7. Acceptance tests

Each of these pins a decision above, so that a later refactor that quietly loses it fails to
compile rather than silently weakening a constant.

- Contraction at constant **1**, not 2.
- The `[0,1]` weights admissible **guard-free**, with no positive-mass hypothesis.
- The triangle constant **2**, and hence the `ε/2` call.
- Separate left and right part-count bounds exposed; the same-carrier product bound
  **derived** from them, never primitive.
- `op` involutive.
- Left and right stepification commuting.
- Rescaling a carrier weight: raw discrepancy scales, normalized energy fixed.
- Empty carrier, empty part, and zero-mass block, all guard-free.

## 8. Explicit non-goals

- Superseding, deprecating, or re-deriving the existing Boolean same-carrier summit (§2.3).
- A synchronized same-carrier weighted-kernel theorem (§3).
- Tensor/box FK, until the step theorem lands.
- Any probability-measure layer (§5).
