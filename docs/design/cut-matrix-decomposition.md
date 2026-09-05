# Cut-matrix decomposition: audit and interface proposal (#71, tranche 9)

**Status: draft for review. No theorem signature is frozen until this document is approved.**

The last open item of #71. `Partition/RectKernelFriezeKannan.lean` delivered the
**step-partition summit** (`rect_frieze_kannan_cutDiscrepancy`, design freeze
`docs/design/rectangular-kernels.md`); `PROVENANCE.md` records that "the separate cut-matrix
decomposition interface is not implemented". This document audits what exists against that
interface, proposes `kernel_frieze_kannan_cutDecomposition`, isolates the missing reusable
lemmas, and lays out implementation tranches and tests.

## 1. What the decomposition is, and why it is not the partition theorem

Frieze–Kannan's second statement: a bounded kernel `f` on `A ×ˢ B` is a sum of **few weighted
rectangle indicators** plus a residual of small **cut norm**,

> `f = ∑_{k<n} cₖ · 𝟙_{Sₖ} ⊗ 𝟙_{Tₖ} + R`, with `n ≤ ⌈1/ε²⌉₊`, `|cₖ| ≤ 1/ε`, and
> `|rectSum R wX wY S T| ≤ ε · M` for every `S ⊆ A`, `T ⊆ B`, where `M = mass wX A · mass wY B`.

It is produced by a **greedy residual iteration**: while some rectangle `S ×ˢ T` has
`|rectSum R S T| > ε·M`, subtract the rectangle term with coefficient
`c = rectSum R S T / (mass S · mass T)` (the residual's own average on the witness). The
mass-weighted square of the residual drops by `c² · mass S · mass T ≥ ε² · M`, and it starts at
most `M`, so at most `1/ε²` rounds happen.

**Why it is a separate summit.** The partition summit's stepped prediction *is* a rectangle
combination — one term per cell pair, `#P · #Q ≤ 4^t` of them — so a decomposition could be
"forced through the partition theorem", but with a **product** term count. The greedy
residual iteration records **one term per round**, `O(ε⁻²)` in total, and never forms a
partition. This is exactly the seam the freeze anticipated ("recorded during the greedy
residual iteration rather than forced through the partition theorem"), and it is the reason
the decomposition's residual is measured by a **partition-free cut norm**, not by
`rectCutDiscrepancy` (which is the error against a stepped prediction).

Two quantitative facts to carry into the statement, both classical:

- **Term count** `n ≤ 1/ε²` in the mass-weighted `L²` sense: each round gains at least `ε²·M`
  and the initial square is at most `M` under `|f| ≤ 1`. So `⌈1/ε²⌉₊` is the honest budget;
  the partition summit's `⌈1/ε²⌉₊ + 1` off-by-one comes from the same arithmetic.
- **Coefficient bound** `|cₖ| ≤ 1/ε`: from the witness `|rectSum| > ε·M` and the decrement
  `c² · mass S · mass T ≤ M`, so `c² ≤ M/(mass S · mass T) < |c|/ε`. A consumer needs this
  bound to control the decomposed part; it is not free from the term count.

## 2. Audit table

| existing declaration | file | what it gives the decomposition | gap |
| --- | --- | --- | --- |
| `rectSum`, `rectSum_add/sub/smul/neg/const` | `Finite/RectKernel` | the raw-weight linear algebra of residual updates | none |
| `rectAverage` (guard-free `x / 0 = 0`) | `Finite/RectKernel` | the round coefficient `c = rectAverage R wX wY S T` | none — the guard-free convention makes `c = 0` on a zero-mass witness, which cannot occur (§4) |
| `abs_rectSum_le` | `Finite/RectKernel` | `\|rectSum f S T\| ≤ C · mass S · mass T` under `IsAbsBoundedOnRectangle` | none |
| `finsetMass`, `finsetMass_nonneg`, `finsetMass_mono`, `relMass` | `Finite/Weight` | masses, `mass S ≤ mass A` for `S ⊆ A` | none |
| `sq_sum_mul_le_sum_mul_sum_sq_mul` | `Finite/Inequalities` | mass-weighted Cauchy–Schwarz, the coefficient bound's engine | none |
| `rectBlockEnergy` = `rectAverage² · mass` | `Partition/RectKernelEnergy` | the per-round gain `c² · mass S · mass T` **is** `rectBlockEnergy R wX wY S T` | reuse verbatim |
| `rectEnergyNum`, `rectEnergy_le_one` | `Partition/RectKernelEnergy` | partition-indexed square; the decomposition needs the **pointwise** square `∑∑ wX wY f²` | **missing**: partition-free mass-weighted square (§5, L1) |
| `rectFkIterate`, `one_sub_rounds_mul_sq_le_rectEnergy` | `Partition/RectKernelFriezeKannan` | the round-budget arithmetic and the iteration *shape* (induction on a budget `t`, with a potential ≥ `1 − t ε²`) | shape reused; the potential is the residual's pointwise square, decreasing, rather than the stepped energy, increasing |
| `finsetMass_mul_pos_of_lt_abs_rectError` | `Partition/RectKernelFriezeKannan` | "a witness forces positive total mass" | needs the partition-free analogue for `rectSum` (§5, L4) |
| `rectCutDiscrepancy` (sup over `A.powerset ×ˢ B.powerset`) | `Partition/RectKernelCut` | the `sup'` pattern and the `_le_iff` elimination | **missing**: the partition-free cut norm `rectCutNorm` in the same pattern (§5, L2) |
| `RectKernel.op`, `rectSum_op` | `Finite/RectKernel` | transport of the decomposition across `op` (rectangles swap) | none |
| `IsAbsUnitBoundedOnRectangle` | `Finite/RectKernel` | the hypothesis on `f` | none |
| relation indicators (`relationKernel`, mentioned in the freeze) | — | **not present** in `Finite/RectKernel` | **missing**: a rectangle indicator kernel `rectIndicator S T` and its `rectSum` (§5, L3) |

Nothing in `Graph/FriezeKannan.lean` is consumed: the Boolean same-carrier summit stays the
sharper direct summit (freeze §2.3), and no decomposition form exists there either.

## 3. Proposed interface

### 3.1 Representation

A **finite indexed family of weighted rectangles**, unbundled, in the library's raw idiom:

```
/-- The kernel `∑ k, c k • 𝟙_{S k} ⊗ 𝟙_{T k}`. -/
def rectCombination {n : ℕ} (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y) :
    RectKernel X Y :=
  fun x y => ∑ k, c k * rectIndicator (S k) (T k) x y
```

with `rectIndicator S T x y := if x ∈ S ∧ y ∈ T then 1 else 0` (`IsUnitIntervalOnRectangle`,
`rectSum (rectIndicator S T) wX wY S' T' = mass (S' ∩ S) · mass (T' ∩ T)`).

Why this and not the alternatives:

- **Not a list of triples.** `Fin n` indexing exposes the term count `n` as a first-class
  natural number in the conclusion and composes with `Finset.sum` directly; a `List` would
  need `length` bookkeeping in every consumer.
- **Not a partition.** The whole point (§1) is that no partition is formed; the rectangles
  overlap freely.
- **Not a bundled structure** carrying its bounds. The freeze keeps `RectKernel` unbundled and
  bounds as hypotheses; a `structure` here would fork that.
- **The residual is a definition, not an existential.** `f - rectCombination c S T` is the
  residual; the theorem bounds its cut norm.

### 3.2 The cut norm, partition-free

```
noncomputable def rectCutNorm (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  (A.powerset ×ˢ B.powerset).sup' ⟨…⟩ fun p => |rectSum f wX wY p.1 p.2|
```

in the exact pattern of `rectCutDiscrepancy`, with `rectCutNorm_le_iff` (`≤ ε ↔ ∀ S ⊆ A, ∀ T
⊆ B, |rectSum f S T| ≤ ε`), nonnegativity, `op` transport, and rescaling. The normalized
cut norm `rectCutNorm / (mass A · mass B)` is derived and guard-free; it is not the primitive.
Relationship to the existing notion, recorded as a lemma: `rectCutDiscrepancy f P Q =
rectCutNorm (rectResidual f P Q)`… **only after** checking whether `rectResidual`'s stepped
sum matches `rectSum` of the residual on every sub-rectangle — it does not in general
(`rectError` uses the stepped prediction on `S ×ˢ T`, `rectResidual` subtracts cell averages
pointwise); the bridge is `rectSum_rectResidual_eq_rectError`, which already exists and says
they agree. So `rectCutDiscrepancy f wX wY P Q = rectCutNorm (rectResidual f wX wY P Q) wX wY A
B` is expected to be a one-line consequence and is worth stating as the link between the two
summits.

### 3.3 The theorem

```
theorem kernel_frieze_kannan_cutDecomposition [DecidableEq X] [DecidableEq Y]
    (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y),
      n ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ k, |c k| ≤ 1 / ε) ∧
      (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧
      rectCutNorm (f - rectCombination c S T) wX wY A B
        ≤ ε * (finsetMass wX A * finsetMass wY B)
```

- **Hypotheses**: exactly those of `rect_frieze_kannan_cutDiscrepancy` — nonnegative carrier
  weights on the carriers, `|f| ≤ 1` on `A ×ˢ B`, `0 < ε`. No nonemptiness, no positive
  mass, no `ε ≤ 1` (at `ε > 1` the statement is trivial with `n = 0`: `|rectSum f S T| ≤ M`).
- **Denominator-free**, in units of `M = mass A · mass B`, like the summit; a normalized
  corollary divides through (guard-free, `x / 0 = 0`).
- **Term count** `⌈1/ε²⌉₊`, without the summit's `+ 1`: the decomposition's budget argument is
  "the potential drops by ≥ `ε² M` per round from ≤ `M`", which is `t ε² ≤ 1` rounds, so
  `⌈1/ε²⌉₊` suffices. If the proof ends up wanting the `+ 1` for the same off-by-one reason
  the partition iteration did, **stop and report** rather than silently weakening: the term
  count is the headline constant of this theorem.
- **Coefficient bound** `1/ε`, from §1. Worth exposing separately because a consumer bounding
  `‖∑ cₖ 𝟙 ⊗ 𝟙‖` needs it.
- **Rectangles inside the carriers**: recorded so that a consumer can restrict without
  re-deriving.
- **Signed** throughout: nothing assumes `f ≥ 0`, and the coefficients are signed.

Corollaries to state alongside:

- `…_normalized`: divide by `M` (guard-free).
- `…_op`: the decomposition transports across `RectKernel.op` with `S`/`T` swapped (freeze
  convention 7).
- **Two-sided uniform-counting reading** at `wX = wY = 1`: `M = #A · #B` and the cut norm is
  the unweighted one; stated as an example, not a theorem.

### 3.4 What is *not* proposed

- No claim that the partition summit's stepped prediction equals a decomposition with
  `#P · #Q` terms as a public theorem. It is true and cheap, but it is the *weaker* route and
  publishing it invites the product-count reading the freeze warns about. It may appear as a
  test.
- No "cut norm" in `L¹`/normalized-only form as primitive; raw first, normalized derived.
- No same-carrier symmetric decomposition (`S = T`): a different statement with its own
  constants; out of scope, as the synchronized same-carrier theorem is (freeze §8).

## 4. Proof route, and where each existing result enters

Potential: `Φ(R) = rectSqMass R wX wY A B := ∑ x ∈ A, ∑ y ∈ B, wX x * wY y * R x y ^ 2`
(the pointwise mass-weighted square, §5 L1). Facts:

1. **Start**: `Φ(f) ≤ M` under `|f| ≤ 1` and nonnegative weights (pointwise `f² ≤ 1`).
2. **Witness forces positive mass** (L4): `ε·M < |rectSum R S T|` with `S ⊆ A`, `T ⊆ B` gives
   `0 < mass S · mass T` (else the sum is `0`), hence `0 < M`. As in the partition summit, this
   is why no positive-mass hypothesis appears.
3. **Decrement identity** (L5), pure algebra with `c := rectAverage R wX wY S T`:
   `Φ(R − c·𝟙_{S×T}) = Φ(R) − 2c·rectSum R S T + c²·mass S·mass T = Φ(R) − c²·mass S·mass T`,
   the last step because `c · mass S · mass T = rectSum R S T` under nonnegative weights with
   no positivity needed (`rectAverage_mul_mass`, exists — on zero mass both sides are `0`).
   The gain is `rectBlockEnergy R wX wY S T`.
4. **Gain is at least `ε² M`**: `c²·mass S·mass T = (rectSum)²/(mass S·mass T) ≥ (ε M)²/M`,
   using `mass S · mass T ≤ M` (`finsetMass_mono`, nonnegativity).
5. **Coefficient bound**: `c² · mass S · mass T ≤ Φ(R) ≤ M` (Cauchy–Schwarz,
   `sq_sum_mul_le_sum_mul_sum_sq_mul`, applied to the double sum flattened over `S ×ˢ T`), and
   `|c| · mass S · mass T = |rectSum| > ε M`; combining, `|c| ≤ 1/ε`. **Note** the residual
   `R` is *not* unit-bounded after the first round, so this bound must come from `Φ(R) ≤ M`
   (monotone under the iteration), never from `abs_rectSum_le`.
6. **Iteration** (L6): by induction on a budget `t` with hypothesis `Φ(R) ≤ M − t·ε²·M`
   read as `(t : ℝ) * ε ^ 2 * M ≤ M − Φ(R)`… i.e. the mirror image of
   `one_sub_rounds_mul_sq_le_rectEnergy`: at budget `t` either every rectangle is within
   `ε M` (done, with the terms recorded so far) or a witness exists and the budget `t + 1`
   step applies to the updated residual with one more term appended (`Fin.snoc`, or build the
   families as `Fin (n+1)` by `Fin.cons`). The recorded family's coefficient bounds and
   carrier containments are carried in the induction hypothesis.
7. **Summit**: instantiate at `t = ⌈1/ε²⌉₊` with `Φ(f) ≤ M`.

Everything up to 3 is algebra with no sign hypothesis; nonnegativity of the weights enters
at 1, 2, 4, 5 (masses and `Φ ≥ 0`), matching the algebra/measure boundary the FK tranche
established.

## 5. Missing reusable lemmas (each a candidate for permanent source, none decomposition-specific)

| id | lemma | home |
| --- | --- | --- |
| L1 | `rectSqMass f wX wY A B` (pointwise mass-weighted square), nonnegativity, `≤ C² · M` under `IsAbsBoundedOnRectangle`, `op` transport | `Finite/RectKernel` |
| L2 | `rectCutNorm` with `_le_iff`, `_nonneg`, `_op`, `_smul_weight_left`, and `rectCutDiscrepancy_eq_rectCutNorm_rectResidual` | `Partition/RectKernelCut` (cut norm itself is partition-free and could sit in `Finite/RectKernel`; the bridge to `rectResidual` needs partitions) |
| L3 | `rectIndicator S T`, unit-interval bounded, `rectSum (rectIndicator S T) wX wY S' T' = mass (S' ∩ S) · mass (T' ∩ T)`, and `rectCombination` with `rectSum_rectCombination` (linearity) | `Finite/RectKernel` (indicators were promised there by the freeze; `relationKernel` may come with it) |
| L4 | `finsetMass_mul_pos_of_lt_abs_rectSum` — the partition-free "witness forces positive mass" | `Finite/RectKernel` (the partition version stays; it may become a corollary) |
| L5 | `rectSqMass_sub_rectAverage_smul_rectIndicator` — the decrement identity, and `rectBlockEnergy_le_rectSqMass` (Cauchy–Schwarz on a rectangle) | `Partition/RectKernelEnergy` or `Finite/RectKernel` — wherever `rectBlockEnergy` can be reached; `rectBlockEnergy` currently lives with the partition energy although it mentions no partition, so **moving it down** to `Finite/RectKernel` is the clean option (a relocation, "Changed", same name and statement) |
| L6 | the greedy iteration `rectCutIterate` (private to the summit file) | `Partition/RectKernelFriezeKannan` or a sibling `Partition/RectKernelCutDecomposition` |

The Mathlib pin should be searched for a finset-indexed weighted Cauchy–Schwarz before L5 is
written; `Finset.sq_sum_div_le_sum_sq_div` and `inner_mul_le_norm_mul_norm` are the likely
neighbours, and the repository's `sq_sum_mul_le_sum_mul_sum_sq_mul` already wraps the former.

## 6. Implementation tranches

Each tranche is one PR, reviewed before the next.

1. **Substrate** (L1, L3, L4, and the relocation of `rectBlockEnergy` if approved): the
   pointwise square, rectangle indicators and combinations, the partition-free witness lemma.
   No cut norm, no iteration.
2. **Cut norm** (L2): `rectCutNorm` and its bridge to `rectCutDiscrepancy` via
   `rectResidual`. Establishes that the two summits measure the same thing on the residual.
3. **Decrement and coefficient bound** (L5): the two analytic lemmas of the round.
4. **Iteration and summit** (L6, §3.3), with the normalized and `op` corollaries; the
   provenance sentence "the separate cut-matrix decomposition interface is not implemented"
   is replaced; `docs/design/rectangular-kernels.md` §6 item 3 marked done; #71 closed.

Placement: a new module `Partition/RectKernelCutDecomposition.lean` for tranches 2–4 is the
natural home (the summit is a genuine interface, as `AggregationBridge` was); it is exposed
through the `Kernel` facade with a doc bullet and root-imported through it. If the
no-new-modules preference applies, tranches 2–4 go into `RectKernelFriezeKannan.lean`.

## 7. Tests to pin (per tranche, all `example`s)

- **Empty carriers**: `A = ∅` or `B = ∅` — `M = 0`, cut norm `0`, and the theorem holds with
  `n = 0` (statement-level, and computed on `Fin 0`).
- **Zero mass on a nonempty carrier**: weights identically `0` — every `rectSum` is `0`, the
  decomposition is `n = 0`; pins the guard-free convention with no positive-mass hypothesis.
- **Signed kernels**: a kernel with values `±1` whose total is `0` but whose cut norm is
  positive (the `±1` chequerboard on `2 × 2` has cut norm `1` on a single cell); pins that the
  decomposition, not the total, is what is bounded.
- **Signed weights are excluded by hypothesis, not by convention**: the decrement identity
  (L5, algebra) holds for signed weights; a test with cancelling weights pins that the
  identity's hypotheses were not strengthened, exactly as the tower tests did.
- **Normalization**: rescaling `wX` by `λ > 0` scales the raw cut norm by `λ` and leaves the
  normalized corollary's bound fixed (freeze convention 6).
- **`ε > 1`**: `n = 0` suffices (`abs_rectSum_le`).
- **Coefficient bound is attained-ish**: a single rectangle kernel `𝟙_{S×T}` at `ε` just below
  its relative mass decomposes in one round with `c = 1`; pins `|c| ≤ 1/ε` as a real bound.
- **`op`**: the decomposition of `f.op` is the decomposition of `f` with `S` and `T` swapped.
- **Term count**: the chequerboard at `ε = 1/2` needs `≤ 4` terms; the theorem's budget is
  `⌈4⌉₊ = 4`.
- **The two summits agree on the residual**: `rectCutDiscrepancy f P Q = rectCutNorm
  (rectResidual f P Q)` on a concrete `2 × 2` instance.

## 8. Hard stops

- If the term count needs `⌈1/ε²⌉₊ + 1` (§3.3), stop and report; do not weaken silently.
- If the coefficient bound `1/ε` cannot be obtained without a positive-mass or `ε ≤ 1`
  hypothesis, stop: the statement is meant to be guard-free like the summit.
- If `rectBlockEnergy`'s relocation is refused, L5 goes beside it in
  `Partition/RectKernelEnergy` and the substrate tranche imports partitions — acceptable but
  worth a note.

## 9. Release placement

Not decided here. The decomposition is the last item of #71; whether it ships alone or with
further rectangular-kernel work is the maintainer's call once the design is approved.
