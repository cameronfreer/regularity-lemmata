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
| `rectAverage` (guard-free `x / 0 = 0`) | `Finite/RectKernel` | the round coefficient `c = rectAverage R wX wY S T` | none — the guard-free convention makes `c = 0` on a zero-mass witness (§4 handles that case explicitly) |
| `rectAverage_mul_mass` | `Partition/RectKernel` | `c · mass S · mass T = rectSum R S T` under nonnegative weights (guard-free) | none for the estimates; the algebraic decrement identity (§4) is stated without it, by a split on the witness mass |
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
| `relationKernel R` (`0/1` indicator of a relation) | `Finite/RelationKernel` | the rectangle indicator is `relationKernel (fun x y => x ∈ S ∧ y ∈ T)` | **missing**: the rectangle specialization `rectIndicator S T`, its `rectSum` (`mass (S' ∩ S) · mass (T' ∩ T)`), and finite combinations (§5, L3) |

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
**The bridge to the partition summit.** `rectSum_rectResidual_eq_rectError`
(`Partition/RectKernelCut`) states precisely: for `S ⊆ A` and `T ⊆ B`, the residual's rectangle
sum equals the stepped error, `rectSum (rectResidual f wX wY P Q) wX wY S T = rectError f wX wY
P Q S T`, for **arbitrary signed weights**. Both `rectCutDiscrepancy` and `rectCutNorm` are the
same finite supremum over `A.powerset ×ˢ B.powerset` of the absolute value, so

> `rectCutDiscrepancy f wX wY P Q = rectCutNorm (rectResidual f wX wY P Q) wX wY A B`

follows by `sup'_congr`. This is the link between the two summits: the partition summit bounds
the cut norm of the *stepped* residual; the decomposition bounds the cut norm of the
*rectangle-combination* residual.

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

Potential: `Φ(R) = rectSqMass R wX wY A B := rectSum (fun x y => R x y ^ 2) wX wY A B`, the
raw rectangle sum of the pointwise square (§5 L1) — defined *through* `rectSum` so that its
algebra is `rectSum`'s. Facts:

1. **Start**: `Φ(f) ≤ M` under `|f| ≤ 1` and nonnegative weights (pointwise `f² ≤ 1`).
2. **Witness forces positive mass** (L4): `ε·M < |rectSum R S T|` with `S ⊆ A`, `T ⊆ B` gives
   `0 < mass S · mass T` (else the sum is `0`), hence `0 < M`. As in the partition summit, this
   is why no positive-mass hypothesis appears.
3. **Decrement identity** (L5), in two layers, both **hypothesis-free apart from rectangle
   containment** `S ⊆ A`, `T ⊆ B`, valid for arbitrary signed weights:
   - the quadratic expansion for an arbitrary coefficient `a`:
     `Φ(R − a·𝟙_{S×T}) = Φ(R) − 2a·rectSum R S T + a²·d`, with `d := mass S · mass T`
     (linearity of `rectSum` and `rectSum (rectIndicator S T) S T = d`);
   - its specialization at the average `c := rectAverage R S T = rectSum R S T / d`:
     `Φ(R − c·𝟙_{S×T}) = Φ(R) − c²·d`. This is **not** obtained from `rectAverage_mul_mass`
     (which needs nonnegative weights, since signed masses can cancel); it is a split on
     `d`: if `d = 0` the totalized division gives `c = 0`, so the update and the gain both
     vanish and the identity is `Φ(R) = Φ(R)`; if `d ≠ 0` then `c·d = rectSum R S T` by
     cancellation and the expansion collapses. The gain `c²·d` is `rectBlockEnergy R wX wY S T`.

   Positivity enters the *estimates* below, never these identities.
4. **Gain is at least `ε² M`**: `c²·mass S·mass T = (rectSum)²/(mass S·mass T) ≥ (ε M)²/M`,
   using `mass S · mass T ≤ M` (`finsetMass_mono`, nonnegativity).
5. **Coefficient bound**: `c² · mass S · mass T ≤ Φ(R) ≤ M` (Cauchy–Schwarz,
   `sq_sum_mul_le_sum_mul_sum_sq_mul`, applied to the double sum flattened over `S ×ˢ T`), and
   `|c| · mass S · mass T = |rectSum| > ε M`; combining, `|c| ≤ 1/ε`. **Note** the residual
   `R` is *not* unit-bounded after the first round, so this bound must come from `Φ(R) ≤ M`
   (monotone under the iteration), never from `abs_rectSum_le`.
6. **Iteration** (L6), starting at `t = 0` and carrying the accumulated state. The invariant
   after `t` rounds is: a family of `t` recorded rectangles (inside the carriers, coefficients
   bounded by `1/ε`) whose residual `Rₜ` satisfies the **strict** potential bound
   `Φ(Rₜ) ≤ Φ(f) − t·ε²·M` — strict in the sense that each *failing* round drops the potential
   by strictly more than `ε²·M` (from the strict witness inequality `|rectSum Rₜ S T| > ε·M`).
   At each round either every rectangle is within `ε·M` (stop; the recorded family is the
   decomposition) or a witness exists and the round `t + 1` state is built by appending the
   term (`Fin.snoc`). The round limit is imposed **separately**: the induction runs to a
   fixed `N`, and the summit argues that `N = ⌈1/ε²⌉₊` consecutive failures are impossible.
7. **Summit**. Split on `M`. If `M = 0` (nonnegative weights): every `rectSum` over
   sub-rectangles is `0`, so the empty decomposition (`n = 0`) satisfies the bound at once.
   If `M > 0`: `N := ⌈1/ε²⌉₊` consecutive failing rounds would give
   `Φ(R_N) < Φ(f) − N·ε²·M ≤ M − M = 0` (using `N ≥ 1/ε²`, i.e. `N·ε² ≥ 1`, and `Φ(f) ≤ M`),
   contradicting `Φ ≥ 0`; so some round `t ≤ N` stops, with `n = t ≤ N` terms. This is what
   supplies the budget `⌈1/ε²⌉₊` with **no `+ 1`**: the `+ 1` of the partition iteration came
   from instantiating a non-strict invariant at the budget itself, which is exactly what is
   avoided here.

Everything in 3 is algebra with no sign hypothesis; nonnegativity of the weights enters at 1,
2, 4, 5, and 7 (masses, `Φ ≥ 0`, and the `M = 0` case), matching the algebra/measure boundary
the FK tranche established.

## 5. Missing reusable lemmas (each a candidate for permanent source, none decomposition-specific)

| id | lemma | home |
| --- | --- | --- |
| L1 | `rectSqMass f wX wY A B := rectSum (fun x y => f x y ^ 2) wX wY A B`, nonnegativity under nonnegative weights, `≤ C² · M` under `IsAbsBoundedOnRectangle`, `op` transport | `Finite/RectKernel` |
| L2 | `rectCutNorm` with `_le_iff`, `_nonneg`, `_op`, `_smul_weight_left` | a new partition-free module `Finite/RectKernelCutNorm` (approved placement: partition-free declarations live in `Finite`); the bridge `rectCutDiscrepancy_eq_rectCutNorm_rectResidual` alone stays in `Partition/RectKernelCut` |
| L3 | `rectIndicator S T := relationKernel (fun x y => x ∈ S ∧ y ∈ T)`, unit-interval bounded, `rectSum (rectIndicator S T) wX wY S' T' = mass (S' ∩ S) · mass (T' ∩ T)`, and `rectCombination` with `rectSum_rectCombination` (linearity) | `Finite/RelationKernel` (beside `relationKernel`, which already exists there) |
| L4 | `finsetMass_mul_pos_of_lt_abs_rectSum` — the partition-free "witness forces positive mass" | `Finite/RectKernel` (the partition version stays with its name and statement; it becomes a corollary) |
| L5 | `rectSqMass_sub_smul_rectIndicator` (arbitrary-coefficient quadratic expansion) and `rectSqMass_sub_rectAverage_smul_rectIndicator` (its average specialization by the `d = 0` / `d ≠ 0` split), both hypothesis-free apart from containment; `rectBlockEnergy_le_rectSqMass` (Cauchy–Schwarz on a rectangle, nonnegative weights) | `Finite/RectKernel`, after **relocating `rectBlockEnergy`** (with `_nonneg`, `_le_mass`, `_op`) down from `Partition/RectKernelEnergy` — approved: names and statements preserved, recorded under Changed |
| L6 | the greedy iteration `rectCutIterate` (private to the summit file) | the new partition-free module `Finite/RectKernelCutDecomposition` |

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

Placement (approved direction: partition-free declarations move *down*, names and statements
preserved, relocations recorded under Changed):

- `Finite/RectKernel`: `rectSqMass` (L1), the partition-free witness lemma (L4), the relocated
  `rectBlockEnergy` and the decrement identities (L5).
- `Finite/RelationKernel`: `rectIndicator`, `rectCombination` (L3), beside `relationKernel`.
- `Finite/RectKernelCutNorm` (new): `rectCutNorm` and its laws (L2).
- `Finite/RectKernelCutDecomposition` (new): the iteration and the summit (L6, §3.3), with the
  normalized and `op` corollaries.
- `Partition/RectKernelCut`: only the bridge `rectCutDiscrepancy_eq_rectCutNorm_rectResidual`.

The two new modules join the `Kernel` facade with doc bullets and are root-imported through it;
the facade docstring, root docstring, and README are updated in the tranche that adds them.
Tranche 1 carries the relocation of `rectBlockEnergy`; tranche 2 adds `Finite/RectKernelCutNorm`;
tranche 4 adds `Finite/RectKernelCutDecomposition`.

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
- **Coefficient sanity check**: a single rectangle kernel `𝟙_{S×T}` at `ε` just below its
  relative mass decomposes in one round with `c = 1 ≤ 1/ε`. (This does not exhibit
  near-attainment of `1/ε`; it only checks the bound's direction.)
- **Round-level coefficient example**: a residual with potential bounded by `M` but pointwise
  values exceeding `1` (e.g. after subtracting a rectangle term from a `±1` kernel, a value
  `−2` appears), on which the round's `c` is still bounded by `1/ε` through the potential —
  pins that the coefficient bound is derived from `Φ ≤ M`, not from unit boundedness.
- **`op`**: the decomposition of `f.op` is the decomposition of `f` with `S` and `T` swapped.
- **A forced update**: for the counting-weight `±1` chequerboard on `2 × 2`, `M = 4` and the
  cut norm is `1` (a single cell), so at `ε = 1/2` the **empty** decomposition already satisfies
  `1 ≤ ε·M = 2`. Use `ε < 1/4` (say `ε = 1/5`, bound `4/5 < 1`) to force at least one round,
  and pin that the returned family is nonempty there.
- **Budget arithmetic**, separately: `⌈1/ε²⌉₊` at `ε = 1/5` is `25`, at `ε = 1/2` is `4`, and
  the summit's `n ≤ ⌈1/ε²⌉₊` is instantiated at both.
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
