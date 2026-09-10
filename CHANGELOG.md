# Changelog

Release notes aggregated from the GitHub Releases, newest first. Each tag is annotated and the
GitHub Release names the full commit SHA it was cut from; pin a tag when depending on the library.

## v0.10.0 (2026-09-06)

Release commit: `f4377e2d30db1906b9cf2e11f2ca858b755a601f`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from v0.9.0.

Axiom audit: standard axioms only, over `4004` audited declarations (an audit count, including private and compiler-generated declarations; not a public-API measure). The public surface change in this release is **1 declaration added and one public version marker changed**.

### Highlights

**Closeness from equal predecessor-ceiling buckets (#163, #165).** In `Finite/DensityBuckets.lean`, beside the floor-based half-open `densityBucket`:

```
le_add_of_ceil_div_pred_eq {x y c : ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (h : ⌈x / c⌉₊ - 1 = ⌈y / c⌉₊ - 1) : x ≤ y + c
```

The predecessor-ceiling bucket `⌈x / c⌉₊ - 1` cuts `[0, 1]` into exactly `⌈1/c⌉₊` buckets, one fewer than the `⌊1/c⌋₊ + 1` half-open buckets whenever `1/c` is an integer, so it is not a substitute for `densityBucket`. The conclusion is **one-sided**: the truncated subtraction merges ceilings `0` and `1` into one bucket, so `x = −100`, `y = 0`, `c = 1` satisfies the hypothesis while `y ≤ x + c` fails. It is **not strict**: `x = c`, `y = 0` gives equality. Both are pinned by tests, together with the merged zero bucket `x = 0`, `y = c/2`.

Mathlib's pin has `Nat.ceil_eq_iff` and `Int.abs_sub_lt_one_of_floor_eq_floor` but no predecessor-ceiling variant; this is a new theorem, kept over `ℝ`.

### Also merged since v0.9.0 (documentation)

The design document for the cut-matrix decomposition, `docs/design/cut-matrix-decomposition.md` (#162, #71 tranche 9): the audit, the frozen interface `kernel_frieze_kannan_cutDecomposition` with budget `⌈1/ε²⌉₊` and coefficient bound `1/ε`, the explicit strict iteration invariant, the signed-weight decrement identities, placement, tranches, and tests. No implementation is in this release.

### Public API added in v0.10.0

### `Finite/DensityBuckets.lean` (1 declaration)

`le_add_of_ceil_div_pred_eq`.

No new public instances are added in this release.

### Changed

`RegularityLemmata.version` now evaluates to `"0.10.0"` rather than `"0.9.0"`. It is a public declaration, so this is a public API change and not merely a packaging one; the package, citation, and installation markers identify v0.10.0 to match.

### Not in this release

#71 tranche 9 (the cut-matrix decomposition): designed (#162), not implemented; its release number is deliberately undecided.


## v0.9.0 (2026-09-05)

Release commit: `dc33c29f764cae0c0c94859383c3124ee4881c2b`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from v0.8.0.

Axiom audit: standard axioms only, over `3995` audited declarations (an audit count, including private and compiler-generated declarations; not a public-API measure). The public surface change in this release is **3 declarations added and one public version marker changed**, inventoried below.

### Highlights

**Multicolour tree Ramsey — companion Lemma 2.6 in colouring form (#159, #160).** The `m`-colour generalization of the additive two-colour subtree theorem, in the same conventions (arbitrary root, branch direction preserved, depth unconstrained; heights in successor form):

- `binaryTreeRamsey (m) (t : Fin m → ℕ) (colour : InternalNode ((∑ i, t i) + 1) → Fin m)`: for some colour `i`, a colour-`i` subtree (an `InternalEmbedding`) of height `t i + 1`. The host height is the successor of the sum — the parenthesization is load-bearing, and at `m = 2`, `t = ![a, b]` it is `a + b + 1`.
- `binaryTreeRamsey_proper`: the whole-tree form, leaves placed (`ProperEmbedding`).
- `binaryTreeRamsey_proper_const (m t) (colour : InternalNode (m * t + 1) → Fin m)`: equal heights, every subtree of height `t + 1`, host `m * t + 1`.

The two-colour theorems `binaryTreeRamsey_two` and `binaryTreeRamsey_two_proper` are **unchanged**, and both are recovered through the public multicolour API as tests (with the colouring restricted along the host-height identity on the way in and the embedding rebuilt on the way out).

### The induction

The recursion is indexed by the host height, as before. At a root of colour `c`: if `t c = 0` the root alone answers; otherwise `t c` is shrunk by one with `Function.update` and both branches are recursed into — a branch answering with a colour other than `c` already answers at that colour's full height, and two branches answering with `c` are joined under the root by `fork`. The returned height is carried as an equation `k = t i + 1` next to the embedding, so the arithmetic of `Function.update` is reconciled by rewriting the equation and never by casting an embedding. The equal-height form enters the recursion at `n = m * t` with `∑ i : Fin m, t = m * t` as its hypothesis, so no colouring is transported.

Edge cases, all tested: `m = 0` is vacuous (the host root exists, so no colouring into `Fin 0`); `m = 1` gives existence at equal heights, with the identity embedding exhibited separately as a witness; `t = 0` in the constant form is the root alone; three colours at host height `3 · 1 + 1 = 4` force a monochromatic proper subtree of height `2`, including on a concrete non-constant colouring.

### Provenance

A **reformulated variant** of G. Conant and C. Terry, *Encoding orders and trees in real-valued functions* ([arXiv:2607.21761](https://arxiv.org/abs/2607.21761)), companion **Lemma 2.6**: the colouring form of their cover statement, with heights in successor form (subtrees `t i + 1`, host `(∑ i, t i) + 1`, their `t = t₁ + … + t_m − m + 1`), generalizing the Alon–Livni–Malliaris–Moran Lemma 16 two-colour case recorded in v0.5.0. The cover equivalence is not formalized, so the label is not "exact". Recorded in the module docstring and `PROVENANCE.md`.

### Public API added in v0.9.0

### `Finite/BinaryTreeRamsey.lean` (3 declarations)

`binaryTreeRamsey`, `binaryTreeRamsey_proper`, `binaryTreeRamsey_proper_const`.

No new public instances are added in this release.

### Changed

`RegularityLemmata.version` now evaluates to `"0.9.0"` rather than `"0.8.0"`. It is a public declaration, so this is a public API change and not merely a packaging one; the package, citation, and installation markers identify v0.9.0 to match.

### Not in this release

#71 tranche 9 (the cut-matrix decomposition) remains a separate campaign for a later release boundary.


## v0.8.0 (2026-09-05)

Release commit: `acd454899e80f1287dae12b306f59449759539dc`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from v0.7.0.

Axiom audit: standard axioms only, over `3982` audited declarations (an audit count, including private and compiler-generated declarations; not a public-API measure). The public surface change in this release is **35 declarations added and one public version marker changed**, inventoried below.

### Highlights

**The finite multiplicative-weights (Hedge) forecaster and its regret bound (#125, #157).** Self-contained real analysis over `Finset` sums in the library's raw-weight idiom — no measure theory, no probability library — over an **arbitrary finite expert type** `ι`, with `Fin m` as a specialization:

- `hedgeWeight η ℓ t i = exp (−η ∑_{s<t} ℓ s i)` as an honest definition (closed form by `rfl`, the multiplicative update `hedgeWeight_succ` as a theorem), the potential, and `hedgeProb` as a **raw function** with nonnegativity and `≤ 1` guard-free and sum-one under `[Nonempty ι]`; no bundled probability type.
- The **empty-expert endpoint** stated explicitly: potential `0`, probabilities summing to `0`, expected loss `0`.
- **Causal congruence** (round `t` reads only rounds `< t`) and **relabeling** by an equivalence of expert types.
- The bound: for losses in `[0, 1]` over the horizon and **any** `η > 0`,

  `∑_{t<T} ⟨p_t, ℓ_t⟩ ≤ ∑_{t<T} ℓ t i₀ + log |ι| / η + η T / 2`,

  with constants `1` and `1/2`, no upper hypothesis on `η`, the loss hypothesis only for `t < T`, and no inhabitedness instance (the expert `i₀` witnesses it). `Fin m` reads `log m`.

### The telescoping correction

The per-round estimate is `Φ (t+1) ≤ Φ t · (1 − η⟨p_t, ℓ_t⟩ + η²/2)`. Dividing an `(η − η²/2)`-form through would force `η < 2` onto the public statement. Instead the factor — positive for every `η ≥ 0`, being at least `(1 − η)²/2 + 1/2` since `⟨p, ℓ⟩ ≤ 1` — has its logarithm relaxed to the increment `−η⟨p_t, ℓ_t⟩ + η²/2` via `log (1 + y) ≤ y`, and *that* increment telescopes. This is why `η` is unconstrained; a pin instantiates the bound at `η = 5`.

### One analytic ingredient, separated

The update and potential identities are algebraic (`hedgeWeight_succ`, `hedgePotential_succ`). The single analytic step (`hedgePotential_succ_le`) uses `exp (−x) ≤ 1 − x + x²/2` for `x ≥ 0`, which Mathlib's pin does not have (it has only the forward series bound `Real.quadratic_le_exp_of_nonneg`). It is added as `exp_neg_le_one_sub_add_sq_half` in `Finite/Inequalities.lean`, derived via `(1 − x + x²/2)(1 + x + x²/2) = 1 + x⁴/4 ≥ 1`, and recorded on #54 as plausibly Mathlib-shaped.

### Concrete symbolic pins

`Real.exp` is noncomputable, so the tests are kernel-checked closed forms rather than executable ones (recorded on #125): on a two-expert sequence where expert `0` loses once, the weights, potential, and played distribution after round `0` in closed form; the forecaster strictly favouring the better expert for every `η > 0`; stationarity afterwards; uniformity under zero loss; the bound at `η = 1` and `η = 5`; the finite-horizon boundary (an out-of-range later loss does not disturb the bound); the `Fin 0` endpoint; a swap relabeling; causal congruence.

### Public API added in v0.8.0

### `Finite/Inequalities.lean` (1 declaration)

`exp_neg_le_one_sub_add_sq_half`.

### `Finite/Hedge.lean` (34 declarations)

Definitions: `hedgeWeight`, `hedgePotential`, `hedgeProb`, `hedgeExpectedLoss`.

Weights and potential: `hedgeWeight_eq_exp`, `hedgeWeight_zero`, `hedgeWeight_succ`, `hedgeWeight_pos`, `hedgePotential_nonneg`, `hedgePotential_pos`, `hedgePotential_zero`, `hedgeWeight_le_hedgePotential`.

The distribution: `hedgeProb_nonneg`, `hedgeProb_sum_one`, `hedgeProb_le_one`, `hedgeProb_zero`.

Empty-expert endpoint: `hedgePotential_of_isEmpty`, `sum_hedgeProb_of_isEmpty`, `hedgeExpectedLoss_of_isEmpty`.

Causal congruence and relabeling: `hedgeWeight_congr`, `hedgePotential_congr`, `hedgeProb_congr`, `hedgeWeight_comp_equiv`, `hedgePotential_comp_equiv`, `hedgeProb_comp_equiv`, `hedgeExpectedLoss_comp_equiv`.

Potential estimate and regret: `hedgePotential_succ`, `hedgePotential_succ_le`, `log_hedgePotential_succ_le`, `log_hedgePotential_le`, `hedge_regret`.

`Fin m` specializations: `sum_hedgeWeight_pos`, `hedgeProb_sum_one_fin`, `hedge_regret_fin`.

No new public instances are added in this release.

### Exposure and provenance

`Finite.Hedge` is imported by the root and belongs to no facade (see the facade audit above). `PROVENANCE.md` gains the antecedents: N. Littlestone and M. K. Warmuth, *The weighted majority algorithm* (1994); Y. Freund and R. E. Schapire, *A decision-theoretic generalization of on-line learning and an application to boosting* (1997).

### Changed

`RegularityLemmata.version` now evaluates to `"0.8.0"` rather than `"0.7.0"`. It is a public declaration, so this is a public API change and not merely a packaging one; the package, citation, and installation markers identify v0.8.0 to match.

### Not in this release

#71 tranche 9 (the cut-matrix decomposition) is a substantial independent campaign and is held for the following release boundary.


## v0.7.0 (2026-09-04)

Release commit: `f1780033e200c0c107efc05bb7b96805e7746297`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from
v0.6.0.

Axiom audit: standard axioms only, over `3918` audited declarations. That figure is the
**axiom-audit** count and includes private and compiler-generated declarations; it is not a
public-API measure. The public surface change in this release is **89 named declarations and one
instance added, one declaration moved, and one public version marker changed**, inventoried below.

### Highlights

**Approximation-to-counting, complete (#84, #148).** The interface frozen in the design audit
(#147, `docs/design/approximation-to-counting.md`) is fully implemented across six tranches:

- **The arity-generic diagonal gate** (#149). Collision characterization
  (`not_injective_iff_exists_lt_eq`), nontransversal cell tuples, `cellTupleVolume`, and the
  generic bound on their weight; the arity-3 statements are retained as instances.
- **Positional lift and the normalization conversion** (#150). `badCellTuples` lift a single
  aggregated bad-pair mass bound to `k`-tuples with coefficient `k.choose 2`, guard-free; the
  `s`-restricted injective-tuple layer (`injectiveTuplesOn`, card `(|s|)_k`, the
  `(k.choose 2)|s|^(k-1)` collision bound) yields the additive conversion between `n^k` and
  `(n)_k` normalizations.
- **The packaged quotient model and the quotient counting theorem** (#151).
  `FiniteRelModel.quotient` interprets each symbol by `quotientRel`; under indivisibility the
  induced count on a transversal cell tuple is all-or-nothing, and `quotientInducedCount` sums
  box volumes over matching transversal cell tuples, with the counting theorem bounding the
  gap by `(k.choose 2) * m * |s|^(k-1)`.
- **Count across an edit** (#152). `abs_inducedEmbeddingCountOn_sub_le_editMass` bounds the
  difference of the `s`-restricted induced counts of two nullary-compatible models by the
  edit mass times `|s|^(k-1)`.
- **The aggregation bridge** (#153). `abs_inducedEmbeddingCountOn_sub_sum_est_le` (raw), its
  normalized corollary, and the arity-2/3 wrappers (`pairInducedEstimate`, the coarse
  estimate), with `MatchesProfiles` and its `DecidablePred` instance.
- **The cellwise-to-aggregate edit conversion and the composite theorem** (#155).
  `editDistance_const_eq_sum_cellBoxes`, `CellwiseEditBound.editDistance_const_le`, and the
  composite approximation-to-counting bounds through edit mass, cellwise edit bounds, and
  majority rounding, in raw and normalized forms.

**Analytic homogeneity** (#154). Conant–Terry's `(δ, ε)`-homogeneous rectangle (analytic
Definition A.1, after Chavarria–Conant–Pillay) as `RectKernel.IsHomogeneousPair`, built from
`IsAlmostNearOn` ("for `ε`-almost all `v`, `φ v ≈_δ r`") and `RectKernel.IsRowConcentrated`
(totalized on both empty sides), with monotonicity, totalization, and an exact transpose law;
and Proposition A.5 in both directions — `ε²`-almost `2δ`-constant implies
`(δ, ε)`-homogeneous (a row-wise Markov count, range hypothesis local to the rectangle), and
`(δ, ε)`-homogeneous implies `2ε`-almost `2δ`-constant (hypothesis-free, all real `ε`). All
three are reformulated variants: constants preserved, domains extended, empty rectangles
totalized. `Finite/AlmostConstant.lean` gains the centered characterization of
`δ`-constancy (`isDeltaConstantOn_iff_exists_center`, radius `δ / 2`, center `0` on the empty
set), its range-aware companion, and the transpose law `isAlmostConstantPair_op_iff`.

### Public API added in v0.7.0

### `Finite/AlmostConstant.lean` (3 declarations)

`isDeltaConstantOn_iff_exists_center`, `IsDeltaConstantOn.exists_center_mem_Icc`,
`isAlmostConstantPair_op_iff`.

### `Finite/AnalyticHomogeneous.lean` — new module (17 declarations)

`IsAlmostNearOn`, `IsAlmostNearOn.mono_delta`, `IsAlmostNearOn.mono_eps`, `isAlmostNearOn_empty`,
`RectKernel.IsRowConcentrated`, `RectKernel.IsRowConcentrated.mono_delta`,
`RectKernel.IsRowConcentrated.mono_eps`, `rectKernel_isRowConcentrated_empty_left`,
`rectKernel_isRowConcentrated_empty_right`, `RectKernel.IsHomogeneousPair`,
`RectKernel.IsHomogeneousPair.mono_delta`, `RectKernel.IsHomogeneousPair.mono_eps`,
`RectKernel.isHomogeneousPair_op_iff`, `rectKernel_isHomogeneousPair_empty_left`,
`rectKernel_isHomogeneousPair_empty_right`, `RectKernel.isHomogeneousPair_of_isAlmostConstantPair`,
`RectKernel.isAlmostConstantPair_of_isHomogeneousPair`.

### `Finite/Injective.lean` (13 declarations)

`not_injective_iff_exists_lt_eq`, `injectiveTuplesOn`, `nonInjectiveTuplesOn`,
`mem_injectiveTuplesOn`, `mem_nonInjectiveTuplesOn`, `card_injectiveTuplesOn`,
`card_injectiveTuplesOn_add_card_nonInjectiveTuplesOn`, `card_injectiveTuplesOn_pos_iff`,
`card_nonInjectiveTuplesOn_le`, `pow_le_descFactorial_add_choose_mul`,
`div_pow_le_div_descFactorial`, `div_descFactorial_sub_div_pow_le`, `card_filter_comp_mem_le`.

### `Relational/DiagonalGate.lean` (25 declarations)

`nontransversalCellTuples`, `mem_nontransversalCellTuples`,
`nontransversalCellTriples_eq_nontransversalCellTuples`, `cellTupleVolume`,
`cellTupleVolume_nonneg`, `cellTripleVolume_eq_cellTupleVolume`,
`sum_nontransversalCellTuples_weight_le`, `badCellTuples`, `mem_badCellTuples`,
`sum_badCellTuples_weight_le_mass`, `sum_badCellTuples_weight_le`,
`piFinset_const_eq_biUnion_cellTuples`, `piFinset_pairwiseDisjoint_cellTuples`,
`inducedEmbeddingCountOn_eq_sum_cellTuples`, `transversalCellTuples`,
`mem_transversalCellTuples`, `transversalCellTriples_eq_transversalCellTuples`,
`inducedEmbeddingCountOn_eq_transversal_add_nontransversal`,
`inducedEmbeddingCountOn_le_cellTupleVolume`, `sum_transversalCellTuples_eq_quotientInducedCount`,
`FiniteRelModel.IsIndivisibleFor.quotientInducedCount_le`,
`FiniteRelModel.IsIndivisibleFor.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le`,
`FiniteRelModel.IsIndivisibleFor.abs_inducedEmbeddingCount_sub_quotientInducedCount_le`,
`sum_cellTupleVolume_eq`, `sum_transversalCellTuples_cellTupleVolume_le`.

### `Relational/Indivisible.lean` (9 declarations)

`FiniteRelModel.quotient`, `FiniteRelModel.quotient_holds_iff`,
`FiniteRelModel.IsIndivisibleFor.quotient_holds_iff`,
`FiniteRelModel.IsIndivisibleFor.quotient_holds_part`, `FiniteRelModel.quotient_holds_zero`,
`FiniteRelModel.nullaryCompatible_quotient`,
`FiniteRelModel.IsIndivisibleFor.inducedEmbeddingCountOn_cells`, `quotientInducedCount`,
`quotientInducedCount_eq_sum_ite`.

### `Relational/BinaryPattern.lean` (3 declarations and one instance)

`inducedEmbeddingCountOn_le_descFactorial`, `inducedEmbeddingCountOn_univ` (moved here from
`Relational/DiagonalGate`, same name and statement), `MatchesProfiles` and its `DecidablePred`
instance.

### `Relational/Edit.lean` (3 declarations)

`abs_inducedEmbeddingCountOn_sub_le_editMass`, `abs_inducedEmbeddingCount_sub_le_editMass`,
`editDistance_const_eq_zero_of_nullaryCompatible`.

### `Relational/CellwiseEdit.lean` (2 declarations)

`editDistance_const_eq_sum_cellBoxes`, `CellwiseEditBound.editDistance_const_le`.

### `Relational/TransversalCounting.lean` (2 declarations)

`matchesThreeProfiles_iff_matchesProfiles`, `inducedEmbeddingCountOn_eq_zero_of_not_matchesProfiles`.

### `Relational/AggregationBridge.lean` — new module (12 declarations)

`abs_sum_transversalCellTuples_sub_le`, `abs_inducedEmbeddingCountOn_sub_sum_est_le`,
`abs_inducedEmbeddingCountOn_div_sub_sum_est_div_le`, `pairInducedEstimate`,
`abs_inducedEmbeddingCountOn_sub_pairInducedEstimate_le`,
`abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le`,
`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass`,
`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_of_cellwiseEditBound`,
`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_majorityRound_le`,
`abs_inducedEmbeddingCountOn_sub_sum_est_le_of_editMass`,
`abs_inducedEmbeddingCountOn_div_sub_quotientInducedCount_div_le`,
`abs_inducedEmbeddingCountOn_div_sub_sum_est_div_le_of_editMass`.

### Facades

`RegularityLemmata.Kernel` gains `Finite.AnalyticHomogeneous`;
`RegularityLemmata.RelationalApproximation` gains `Relational.Edit` and
`Relational.AggregationBridge`, each with a doc bullet. The root module imports both new modules
through the facades. Every declaration remains reachable from the root import and each module
remains directly importable by name.

### Changed

`RegularityLemmata.version` now evaluates to `"0.7.0"` rather than `"0.6.0"`. It is a public
declaration, so this is a public API change and not merely a packaging one; the package, citation,
and installation markers identify v0.7.0 to match.

`inducedEmbeddingCountOn_univ` moved from `Relational/DiagonalGate` to `Relational/BinaryPattern`
(#152), same name and statement. Existing statements whose proofs were rebuilt on the new generic
layer keep their statements unchanged (`not_injective_fin_three`, `sum_nontransversal_weight_le`,
`piFinset_const_eq_biUnion_cellTriples`, `piFinset_pairwiseDisjoint_cellTriples`,
`globalInducedCount_eq_inducedEmbeddingCountOn`, `globalInducedCount_eq_inducedEmbeddingCount`).
Import edges added: `Relational/DiagonalGate`, `Relational/Edit` (on `Relational/BinaryPattern`),
`Relational/CellwiseEdit` (on `Partition/BoxPartition`), `Relational/AggregationBridge` (on
`Relational/Edit` and `Relational/CellwiseEdit`).

### Deprecated/removed

None public. Four private arity-specific collision lemmas were replaced by one private generic
lemma in #149.

### Documentation

`docs/design/approximation-to-counting.md` (#147): the audit and interface freeze for the
campaign. `ARCHITECTURE.md`: the derived constant of the diagonal gate. `PROVENANCE.md`: the
Conant–Terry Appendix A paragraph (Definition A.1, Proposition A.5, the centered lemmas) and the
Chavarria–Conant–Pillay entry. `README.md`: facade summaries.



## v0.6.0 (2026-08-31)

Release commit: `ad3e5b75fba25736035d9f7d6c070bf6e8d92ea4`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from
v0.5.0.

Axiom audit: standard axioms only, over `3762` audited declarations. That figure is the
**axiom-audit** count and includes private and compiler-generated declarations; it is not a
public-API measure. The public surface change in this release is **86 declarations added and one
public version marker changed**, inventoried below.

### Highlights

**The heterogeneous weighted-box stack, complete (#83).** v0.5.0 shipped only the box substrate;
this release adds everything built on it and closes the issue.

- **Predicate mass and density** (#140). `boxPredMass` restricts the *same* tuple sum to a
  decidable predicate, and `boxDensity` divides by the total mass under the guard-free
  `x / 0 = 0` convention.
- **Independent coordinate partitions** (#141). Product cells from `Fintype.piFinset`, with
  disjointness, coverage, the cell count `∏ i, (P i).parts.card`, and exact decompositions of
  both box mass and predicate mass.
- **Finite unions and a symmetric-difference error** (#142). Semantic unions with no Boolean
  syntax tree, and `boxUnionError` as the weighted mass of the tuples covered by exactly one of
  two families.
- **The coordinate-split adapter** (#143). Restriction, gluing, tuple-membership compatibility
  with `splitEquiv`, and the mass factorization across a split.
- **A fifth curated facade** (#144), `RegularityLemmata.ProductSpaces`, collecting the stack.

### The hypothesis boundary

The single design decision running through this release is *where* sign and mass hypotheses are
required. Every result is placed deliberately:

**No hypothesis — identities, valid for signed weights.** The complement mass identity
`boxPredMass w A p + boxPredMass w A ¬p = boxMass w A`; additivity over disjoint sets and disjoint
families; the cell decompositions; the split factorization; symmetry and self-vanishing of the
union error.

**Nonnegativity — every claim comparing masses of *different* sets**, which is exactly when a
signed weight can make a larger set lighter: monotonicity in the box and in the predicate,
subadditivity, the union bounds, the triangle inequality, and the `[0, 1]` density bound.

**Positive mass — only where something is divided**: `boxDensity_true_of_pos` and the
complement-density identities. At zero mass they would read `0 = 1`.

The `[0, 1]` density bound needs **no** positivity, because the guard-free convention puts the
zero-mass endpoint at `0`, inside the interval. `abs_sub_finsetMass_le` needs nonnegativity only
on the symmetric difference, since the shared intersection cancels between the two masses.

### One notion of mass

There is no second mass primitive anywhere in the stack. `finsetMass` over a finset, `boxMass`
over a box's tuples, `boxPredMass` over the tuples satisfying a predicate, and the union error
over a symmetric difference are all the same weighted sum read over a different set, bridged by
`boxMass_eq_prod_finsetMass` and `boxMass_eq_finsetMass_tupleWeight`. A `tupleSetMass` introduced
during development was removed before merge as an exact duplicate of `finsetMass (tupleWeight w)`.

### Instance discipline

`Finite/ProductBox.lean` remains instance-light: `[Fintype ι]` and `[DecidableEq ι]` only, with no
decidable equality on the carriers. The two modules that genuinely need fiberwise
`[∀ i, DecidableEq (V i)]` are separate for that reason — `Partition/BoxPartition.lean`, where
`Finpartition` needs the lattice on `Finset (V i)`, and `Finite/BoxUnion.lean`, where `biUnion`
and symmetric difference need `DecidableEq (∀ i, V i)` — so the cost does not reach consumers
that never partition or take unions.

### Public API added in v0.6.0

### `Finite/ProductBox.lean` — predicate mass and density (24 declarations)

`boxPredMass`, `boxPredMass_apply`, `boxPredMass_true`, `boxPredMass_false`,
`boxPredMass_add_compl`, `tupleWeight_nonneg`, `boxPredMass_nonneg`, `boxPredMass_mono`,
`boxPredMass_le_boxMass`, `boxPredMass_of_eq_empty`, `boxDensity`, `boxDensity_apply`,
`boxDensity_of_boxMass_eq_zero`, `boxDensity_false`, `boxDensity_true_of_pos`,
`boxDensity_nonneg`, `boxDensity_le_one`, `boxDensity_add_compl_of_pos`,
`boxDensity_compl_of_pos`, `boxDensity_of_eq_empty`, `sum_tuples_reindex`, `tupleWeight_reindex`,
`boxPredMass_reindex`, `boxDensity_reindex`.

### `Finite/Weight.lean` — generic estimates (3 declarations)

`finsetMass_union_le`, `finsetMass_biUnion_le`, `abs_sub_finsetMass_le`.

`finsetMass_biUnion_le` is proved by induction: the pinned Mathlib has cardinality and density
versions of the union bound but no weighted one.

### `Partition/BoxPartition.lean` — coordinate partitions (20 declarations)

`BoxPartition`, `boxCells`, `mem_boxCells`, `card_boxCells`, `boxCells_subset`,
`tuples_subset_of_mem_boxCells`, `cellOf`, `cellOf_apply`, `cellOf_mem_boxCells`,
`mem_tuples_cellOf`, `eq_cellOf_of_mem_tuples`, `boxCells_pairwiseDisjoint`,
`biUnion_boxCells_tuples`, `boxMass_eq_sum_boxCells`, `boxPredMass_eq_sum_boxCells`,
`BoxPartition.reindex`, `BoxPartition.reindex_apply`, `boxCells_reindex`,
`card_boxCells_reindex`, `existsUnique_parent_boxCell`.

Refinement follows the repository convention that `Q ≤ P` means `Q` is finer.

### `Finite/BoxUnion.lean` — unions and the error (16 declarations)

`unionTuples`, `mem_unionTuples`, `unionTuples_empty`, `unionTuples_singleton`,
`unionTuples_subset`, `boxMass_eq_finsetMass_tupleWeight`,
`finsetMass_unionTuples_of_pairwiseDisjoint`, `finsetMass_unionTuples_le`, `boxUnionError`,
`boxUnionError_apply`, `boxUnionError_comm`, `boxUnionError_self`,
`boxUnionError_of_unionTuples_eq`, `boxUnionError_nonneg`, `boxUnionError_triangle`,
`abs_sub_finsetMass_unionTuples_le`.

`boxUnionError_of_unionTuples_eq` is one-directional by design: zero error does not imply equal
tuple sets, because a nonempty symmetric difference of zero-weight tuples also has zero error.

### `Finite/BoxCoordinateSplit.lean` — the split adapter (23 declarations)

In the `CoordinateSplit` namespace: `boxLeft`, `boxRight`, `boxLeft_apply`, `boxRight_apply`,
`boxGlue`, `boxGlue_apply_left`, `boxGlue_apply_right`, `boxLeft_boxGlue`, `boxRight_boxGlue`,
`boxGlue_boxLeft_boxRight`, `mem_tuples_iff_split`, `mem_tuples_iff_splitEquiv`, `boxMass_split`,
`boxMass_glue`, `boxLeft_swap`, `boxRight_swap`, `boxMass_split_swap`, `boxLeft_reindex`,
`boxRight_reindex`, `boxMass_boxLeft_of_left_eq_empty`, `boxMass_of_left_eq_empty`,
`boxMass_boxRight_of_left_eq_univ`, `boxMass_of_left_eq_univ`.

Cast-free throughout. No transport was needed, so no `FiniteBox.reindexEquiv` was introduced.

### Facade

`RegularityLemmata.ProductSpaces`, collecting `Finite.Weight`, `Finite.CoordinateSplit`,
`Finite.ProductBox`, `Finite.BoxUnion`, `Finite.BoxCoordinateSplit`, and
`Partition.BoxPartition`. It declares nothing of its own. `Finite.CoordinateSplit` is imported
explicitly rather than transitively, because a facade is a curated contract and a consumer needs
it to construct the adapter's arguments.

No new public instances are added in this release.

### Changed

`RegularityLemmata.version` now evaluates to `"0.6.0"` rather than `"0.5.0"`. It is a public
declaration, so this is a public API change and not merely a packaging one; the package, citation,
and installation markers identify v0.6.0 to match.

The root module imports `RegularityLemmata.ProductSpaces` in place of `Finite.Weight`,
`Finite.CoordinateSplit`, `Finite.ProductBox`, `Finite.BoxUnion`, `Finite.BoxCoordinateSplit`, and
`Partition.BoxPartition`. Every declaration remains reachable from the root import and each module
remains directly importable by name, so no consumer of the root import is affected.

### Deprecated/removed

None.

### Documentation

`PROVENANCE.md` and `Finite/BinaryTreeRamsey.lean` record that `binaryTreeRamsey_two` formalizes
the two-colour subtree theorem taken from Alon–Livni–Malliaris–Moran, Lemma 16, and that it is
also the two-colour specialization of G. Conant and C. Terry, *Encoding orders and trees in
real-valued functions* ([arXiv:2607.21761](https://arxiv.org/abs/2607.21761)), **Lemma 2.6**, the
tree-Ramsey ingredient used in their proof of Theorem 1.11. Their Lemma 2.6 is the multicolour
generalization; what is formalized here is its two-colour case, and Theorem 1.11 is a downstream
application rather than a Ramsey statement. That paper is distinct from the arXiv:2607.21762
*Quantitative analytic stable regularity* already cited for `Finite/AlmostConstant.lean`.

### Known gap from v0.5.0, now closed

v0.5.0's notes recorded that `Finite.ProductBox` was exposed through the root and directly
importable but belonged to no curated facade. `RegularityLemmata.ProductSpaces` closes that gap.


## v0.5.0 (2026-08-25)

Release commit: `fbc62c984302304aa0712b00e4508b803611a2a7`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from
v0.4.0.

Axiom audit: standard axioms only, over `3367 → 3628` audited declarations. That figure is the
**axiom-audit** count and includes private and compiler-generated declarations; it is not a
public-API measure. The public surface change in this release is **131 declarations added and
one public version marker changed**, inventoried below.

### Highlights

- **A finite binary-tree Ramsey layer** (#130, delivered by #134, #137, #138). Full binary trees
  as words; subtree embeddings with arbitrary root and preserved branch direction; proper
  embeddings covering the leaf level; and the additive two-colour subtree theorem — a colouring
  of the internal nodes of a height-`a + b + 1` tree admits a colour-`0` subtree of height
  `a + 1` or a colour-`1` subtree of height `b + 1`. A **precise upper theorem with no optimality
  claim**: no matching lower-bound colouring is formalized.
- **Heterogeneous weighted product boxes** (#131, first tranche of #83). `boxMass` is the
  weighted sum over a box's tuples, with the product factorization as a theorem, so that a mass
  restricted to a subfamily of tuples restricts the same construction.
- **The coordinate-split swap algebra closed** (#129): `restrictLeft_swap`, `restrictRight_swap`,
  and `splitRel_swap`.
- **A fourth curated facade**, `RegularityLemmata.FiniteRamsey`, collecting the library's
  independent finite Ramsey APIs. The root module imports the Ramsey modules through it rather
  than individually.

### Public API added in v0.5.0

### Added: finite full binary trees — `Finite/FullBinaryTree.lean` (34 declarations, 8 instances)

`TreeNode`, `InternalNode`, `LeafNode`, `internalToTree`, `leafToTree`, `internalToTree_val`,
`leafToTree_val`, `IsStrictPrefix`, `BranchBelow`, `branchBelow_def`,
`BranchBelow.isStrictPrefix`, `BranchBelow.length_lt`, `exists_branchBelow_of_isStrictPrefix`,
`eq_of_prefix_of_prefix_of_length_eq`, `not_branchBelow_of_branchBelow`, `prefix_trichotomy`,
`root`, `root_val`, `child`, `leftChild`, `rightChild`, `child_val`, `branchBelow_child`,
`parent`, `parent_val`, `consInternal`, `consInternal_val`, `branchBelow_root_cons`,
`consInternal_injective`, `internalNode_cases`, `wordsLE`, `mem_wordsLE`, `leafNode_zero_eq`,
`card_leafNode`.

Instances: `treeNodeFintype`, `internalNodeFintype`, `leafNodeFintype`, and the unnamed
`Decidable (BranchBelow ..)`, `Decidable (IsStrictPrefix ..)`, `IsEmpty (InternalNode 0)`,
`Unique (LeafNode 0)`, `Nonempty (InternalNode (h + 1))`.

The `Fintype` instances go through an explicit recursive enumeration rather than
`Fintype.ofInjective`, which is noncomputable and would have made every `decide` test in this
layer impossible.

### Added: subtree embeddings — `Finite/BinaryTreeEmbedding.lean` (24 declarations, 1 instance)

`InternalEmbedding` with fields `toFun` and `branch`; `coe_mk`, `ext`, `branch_preserved`, `id`,
`id_apply`, `comp`, `comp_apply`, `comp_id`, `id_comp`, `comp_assoc`, `isStrictPrefix_preserved`,
`apply_ne_apply_of_branchBelow`, `injective`, `singleton`, `singleton_apply`, `branchLift`,
`branchLift_apply`, `left`, `right`, `branchBelow_root_branchLift`, `fork`, `fork_root`,
`fork_cons`; plus the unnamed `CoeFun` instance.

The structure has **one law** — the first turn is preserved. Nothing requires the source root to
map to the host root, the depths to agree, or an edge to map to an edge; all three would make the
Ramsey construction impossible, and each is refuted by a test. Injectivity and ancestry
preservation are theorems derived from the branch law, not structure fields.

### Added: proper embeddings — `Finite/BinaryTreeProperEmbedding.lean` (42 declarations)

`padWordToLength`, `padWordToLength_length`, `prefix_padWordToLength`, `padWordToLength_nil`;
`ProperEmbedding` with fields `internal`, `leaf`, `branch_internal`, `branch_leaf`, and
`toInternal`, `toInternal_apply`, `ext`, `length_leaf`, `length_internal`, `id`, `id_internal`,
`id_leaf`, `toInternal_id`, `comp`, `comp_internal`, `comp_leaf`, `comp_id`, `id_comp`,
`toInternal_comp`, `internal_injective`, `branch_leaf_preserved`, `leaf_injective`,
`internal_ne_leaf`, `vertex`, `vertex_val`, `vertex_of_internal`, `vertex_of_leaf`,
`vertex_injective`; and `InternalEmbedding.leafParent`, `leafParent_val`,
`leafParent_append_getLast`, `leafPrefix`, `leafPrefix_of_ne_nil`, `leafPrefix_of_nil`,
`leafPrefix_length_le`, `extendProper`, `extendProper_toInternal`, `extendProper_internal`,
`extendProper_leaf_val`, `extendProper_leaf_zero`, `ofHeightZero`.

`extendProper` requires **no common-level or spare-height hypothesis**, because the leaf image
enters the correct branch below the parent's image before padding. Height zero is an explicit
branch of the definition: `InternalNode 0` is empty while `LeafNode 0` holds the empty word.

### Added: the additive two-colour subtree theorem — `Finite/BinaryTreeRamsey.lean` (3 declarations)

`BinaryTreeTwoColouring`, `binaryTreeRamsey_two`, `binaryTreeRamsey_two_proper`.

### Added: heterogeneous weighted product boxes — `Finite/ProductBox.lean` (16 declarations)

`FiniteBox`, `FiniteBox.tuples`, `FiniteBox.mem_tuples`, `FiniteBox.reindex`,
`FiniteBox.reindex_apply`, `tupleWeight`, `tupleWeight_apply`, `boxMass`, `boxMass_apply`,
`boxMass_eq_prod_finsetMass`, `boxMass_one`, `boxMass_nonneg`, `boxMass_mono`,
`boxMass_of_eq_empty`, `boxMass_of_isEmpty`, `boxMass_reindex`.

### Added: coordinate-split symmetry — `Finite/CoordinateSplit.lean` (3 declarations)

`restrictLeft_swap`, `restrictRight_swap`, `splitRel_swap`.

### Added: facade

`RegularityLemmata.FiniteRamsey`, re-exporting `Finite.MulticolorRamsey`,
`Finite.FullBinaryTree`, `Finite.BinaryTreeEmbedding`, `Finite.BinaryTreeProperEmbedding`, and
`Finite.BinaryTreeRamsey`. It declares nothing of its own.

### Changed

`RegularityLemmata.version` now evaluates to `"0.5.0"` rather than `"0.4.0"`. It is a public
declaration, so this is a public API change, not merely a packaging one; the package, citation,
and installation markers identify v0.5.0 to match.

The root module `RegularityLemmata` no longer imports `Finite.MulticolorRamsey`,
`Finite.FullBinaryTree`, `Finite.BinaryTreeEmbedding`, or `Finite.BinaryTreeProperEmbedding`
directly; they arrive through `RegularityLemmata.FiniteRamsey`. Every declaration remains
reachable from the root import and each module remains directly importable by name, so no
consumer of the root import is affected.

`scripts/check_public_api_impact.py` accepts emphasised labels (`**Added:**`, `**Changed**:`,
`**None**`) alongside the plain forms (#132). An entry with no content after the label still
fails.

### Deprecated/removed

None.

### Documentation

- `Finite/VCTrace.lean`, `FiniteSetSystems.lean`, and `Relational/Model.lean` describe the
  set-system and binary-adapter modules intrinsically rather than by campaign phase (#128).
- `Finite/ProductBox.lean` states its design as an enduring API contract rather than as
  development narration (#133).
- `PROVENANCE.md` records Alon–Livni–Malliaris–Moran, *Private PAC learning implies finite
  Littlestone dimension* ([arXiv:1806.00949](https://arxiv.org/abs/1806.00949)), **Lemma 16** as
  the source of the subtree theorem — their `p + q - 1` with `p = a + 1`, `q = b + 1` is the
  `a + b + 1` used here — and as the antecedent for the embedding semantics. It also records
  that Mathlib's `BinaryTree` was audited and is not used: it carries data at nodes with no
  notion of a node's address, so it supports neither the ancestry nor the branch-direction
  relations these embeddings are defined by.

### Known gaps

`Finite.ProductBox` is exposed through the root and remains directly importable, but is not yet
grouped into a curated facade. The remaining #83 work will introduce `ProductSpaces`, collecting
it together with predicate mass and density, independent coordinate partitions, box unions with
weighted symmetric difference, and a `CoordinateSplit` adapter.


## v0.4.0 (2026-08-23)

Release commit: `ebe94d8359e21de3388c6e13b372ce731ebfdaea`

Lean `v4.34.0-rc1` and Mathlib `77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d` are unchanged from v0.3.0.

### Highlights

- Complete heterogeneous homogeneity API: singleton and trivial-regime bridges, quantitative restriction under relative growth, and homogeneous pairs of independent partitions (#115).
- Complete binary finite-model adapter: construction, decidability, pullback, relabeling, and restriction, all exposed through the relational-approximation facade (#116, #120).
- Neutral finite set-system facade: heterogeneous relation fibers, trace families over Mathlib's `Finset.vcDim`, support-sensitive Sauer–Shelah bounds, polynomial binomial-sum bounds, and bounded-subset counting (#124, #127).
- Required `Public API impact` section for every PR, checked by CI (#121).

### Public API impact

### Added: homogeneity (14 declarations)

- `IsAlmostConstantOn.isAlmostConstantPair_singleton_left`
- `IsAlmostConstantOn.isAlmostConstantPair_singleton_right`
- `isAlmostConstantPair_singleton`
- `isHomogeneousPair_of_half_le`
- `isHomogeneousPair_singleton`
- `abs_pairDensity_sub_le_of_relative_grow`
- `AreHomogeneousPartitions`
- `AreHomogeneousPartitions.mono`
- `areHomogeneousPartitions_swapRel_iff`
- `areHomogeneousPartitions_not_iff`
- `areHomogeneousPartitions_of_half_le`
- `areHomogeneousPartitions_bot`
- `areHomogeneousPartitions_bot_of_nonneg`
- `areHomogeneousPartitions_indiscrete_iff`

### Added: binary finite-model adapter (7 declarations)

- `FiniteRelModel.binaryRel`
- `FiniteRelModel.binaryRel_apply`
- the `DecidableRel (M.binaryRel R)` instance
- `FiniteRelModel.binaryRel_pullback`
- `FiniteRelModel.binaryRel_pullback_eq`
- `FiniteRelModel.binaryRel_relabel`
- `FiniteRelModel.binaryRel_restrict`

### Added: finite relation fibers and VC traces (32 declarations)

- `fiber`, `mem_fiber`, `fiber_subset`, `fiber_mono`, `fiber_empty`, `fiber_inter`
- `fiberFamily`, `mem_fiberFamily`, `mem_fiberFamily_subset`, `fiberFamily_empty_left`, `fiberFamily_empty_right`, `fiberFamily_mono_left`
- `traceFamily`, `traceFamily_empty_left`, `traceFamily_empty_right`, `mem_traceFamily`, `mem_traceFamily_subset`, `traceFamily_mono_left`, `traceFamily_eq_self_of_subset`, `traceFamily_traceFamily`, `traceFamily_eq_powerset_iff`
- `vcDim_traceFamily_le`, `vcDim_image_inter_le`
- `card_powerset_filter_card_le_sum_choose`
- `card_setFamily_le_sum_choose_of_subset`, `card_traceFamily_le_sum_choose`, `card_image_inter_le_sum_choose`
- `sum_choose_le_pow`, `sum_choose_le_two_pow`
- `card_traceFamily_le_pow`, `card_fiberFamily_le_sum_choose`, `card_fiberFamily_le_pow`

The new `RegularityLemmata.FiniteSetSystems` facade exports the neutral fiber/trace stack. `RegularityLemmata.RelationalApproximation` now exports relational transport as well as model construction, so the binary adapter and all of its transport laws are available from the facade alone.

### Changed

- `RegularityLemmata.version` is now `0.4.0`.
- README dependency guidance now recommends the `v0.4.0` tag.
- Pull requests must include a nonempty `Public API impact` section (`Added`, `Changed`, `Deprecated/removed`, or explicit `None`).

### Deprecated or removed

None.

### Verification

- full `lake build` passed;
- no `sorry`, `admit`, or custom source `axiom` tokens;
- no declaration-uses-sorry warnings;
- `axiom_audit` audited 3,367 declarations with standard axioms only.

Included PRs: #115, #116, #120, #121, #124, #126, and #127.


## v0.3.0 (2026-08-23)

Five commits since v0.2.0 (#108, #110, #112–#114). Toolchain and dependency pins are unchanged from v0.2.0: Lean v4.34.0-rc1 and mathlib `77cbcbc`.

### New public capability

- **Rectangular Frieze–Kannan summit** (`RegularityLemmata.Kernel`): the paired weighted-kernel iteration starts from independent left and right seed partitions, keeps the two `2^t` part bounds separate, and produces a uniform rectangular cut-discrepancy bound. The same-carrier adapter takes the common refinement and exposes the resulting product bound. The Boolean theorem remains available as the sharper direct specialization. (#108)
- **Finite averages and analytic almost-constancy**: guard-free `averageOn` and its density and rectangular-fiber bridges; real-valued, empty-totalized almost-constancy predicates; separation outside almost-constant sets; and the level-set staircase reducing bounded average control to set-density control. (#110, #112)
- **Slicing substrate**: threshold schedules and races, average slicing, and common-block slicing for later finite approximation arguments. (#113)

### Public surface

`RegularityLemmata.Kernel` now exposes weights, rectangular kernels and indicators, one-variable averages, almost-constancy, stepping, energy, cut discrepancy, the rectangular Frieze–Kannan summit, and the slicing substrate. The Conant–Terry provenance entry states precisely which predicates and separation results generalize the paper's `[0,1]` setting. (#112)

### Compatibility

No public declaration was removed or deprecated in this release. Existing direct module imports remain valid. The README dependency example and all version markers now recommend `v0.3.0`. (#114)

Release gate on the tagged tree: 3300 declarations audited, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).


## v0.2.0 (2026-08-18)

62 commits since v0.1.0 (#30–#107). Toolchain: Lean v4.34.0-rc1; mathlib pinned at
`77cbcbc` (29 commits past the v4.34.0-rc1 tag), migrated from v0.1.0's toolchain in #92 and
advanced in #106.

### New capability since v0.1.0

- **Rectangular weighted-kernel stack** (`RegularityLemmata.Kernel` facade): raw weights;
  heterogeneous kernels with carrier weights on both sides; relation indicators; decomposition
  and stepping over independent partitions; energy with the exact parallel-axis
  (refinement-variance) identity; residuals; cut discrepancy and the cut-norm contraction of
  stepping with constant 1; the tower identity. (#85, #88, #90, #94, #96, #104)
- **Sampling and balanced slicing**: hypergeometric tails by exact binomial moments, the
  polynomial-geometric threshold with joint monotonicity, equal-block permutation encoding,
  and `exists_balanced_slicing` — exact equal-size blocks simultaneously typical for a
  supplied trace family — plus leftover and chunk absorption into genuine equipartitions with
  density-transfer lemmas. (#87/#97, #98, #99, #100, #101)
- **Heterogeneous homogeneity and coordinate substrate**: instance-free heterogeneous pair
  density and `IsHomogeneousPair`; dependent coordinate splits; index-generic tuple counting;
  `IsHomogeneousCell` with the exact subcell law and the n-box perturbation bound at
  `c(n) = n`. (#86, #89, #95, #103)
- **Relational approximation stack** (`RegularityLemmata.RelationalApproximation` facade):
  indivisibility of a finite relational model over a partition with the quotient reading and
  exact nullary compatibility; `CellwiseEditBound`; the computable
  `FiniteRelModel.majorityRound` with the exact box-level identity
  `editDistance_majorityRound_eq_min`; the rounding theorem
  `exists_isIndivisibleFor_of_isHomogeneousCell` and its exact converse. (#102, #105)
- **Graph-side regularity**: equitable finite-family regularity with a multiple-of-three seed,
  exact-refining family regularity, strong (energy-gap) regularity for finite families, the
  seeded Frieze–Kannan export, and the piece supplier/schedule. (#30–#33, #46, #74, #76, #79,
  #81)
- **Hypergraph increments**: arity-generic one-atom polyad regularization; pair colorings
  preserved through triadic regularization. (#75, #77)

### Import surfaces (#107)

`import RegularityLemmata` is now the settled public surface, with two curated facades
(`RegularityLemmata.Kernel`, `RegularityLemmata.RelationalApproximation`). The probe,
obstruction-gate, and feasibility modules of the in-progress induced-removal campaign live
under the separate `RegularityLemmataGates` umbrella — same namespace, gates, and CI, each
still directly importable. The axiom audit walks both roots (3139 declarations, standard
axioms only). All deprecation warnings cleared.

### Compatibility notes

- No declaration was renamed or restated in the surface pass; consumers of individual modules
  are unaffected. Consumers of the bare `import RegularityLemmata` who used a probe/gate
  module must now import it directly or via `RegularityLemmataGates`.
- v0.1.0 consumers must migrate toolchains (v0.1.0 predates the v4.34.0-rc1 migration).


## v0.1.0 (2026-07-14)

First public release.

**Toolchain:** `leanprover/lean4:v4.32.0` with mathlib `v4.32.0`. Pin this tag (or a revision) when requiring the library; your project's toolchain should match.

**Scope** (see the README and `ARCHITECTURE.md` for the frozen conventions):
1. finite tuple/counting substrate; 2. density and edit calculus; 3. partitions and mass-weighted energy; 4. the directed graph regularity ladder (weak, Frieze–Kannan, strong, with mathlib Szemerédi bridges); 5. hypergraph vocabulary with the weak and edited triadic regularization summits; 6. finite relational structures over mathlib's `FirstOrder.Language` with graph/hypergraph adapters; 7. finite-palette binary relational regularity with a strong palette witness; 8. binary-palette counting through three vertices — exact palette counts, directed path/triangle counting under regularity, induced three-vertex counts, a global strong-counting theorem with explicit error terms, and simple-graph bridges.

**Soundness:** 1446 declarations, zero sorries, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), enforced in CI by `scripts/check.sh` including a full per-declaration axiom audit.

**Stability:** pre-1.0 — statements pass a review-and-falsification gate before freezing, but names and signatures may change between releases.

**Explicit non-goals of this release:** no relational removal theorem of any kind is included (fixed-pattern and finite-family induced removal are deferred to a later phase with their own statement freeze), and the relational layers assert nothing about relation symbols of arity greater than two.

