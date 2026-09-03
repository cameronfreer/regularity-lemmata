/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.DiagonalGate
import RegularityLemmata.Relational.TwoVertexCounting
import RegularityLemmata.Relational.Edit
import RegularityLemmata.Relational.CellwiseEdit

/-!
# The aggregation bridge: from local box estimates to a global induced count

The generic **approximation-to-counting** bridge of the design freeze
(`docs/design/approximation-to-counting.md`, §6). It is *arity-parametric with an arity-specific
local hypothesis*: the library computes no local coefficient. Given, on each **good transversal**
cell tuple `T` (transversal: distinct cells; good: no coordinate-pair position in the bad pair
set `D`), a supplied box estimate `est T` within `δ · vol T` of the induced count, the bridge
aggregates:

`|inducedEmbeddingCountOn P M (fun _ ↦ s) − Σ_{T transversal} est T|`
`  ≤ (δ + (k.choose 2)·β) · |s|^k + (k.choose 2)·m · |s|^(k−1)`

under the **single aggregated** bad-pair mass bound `Σ_{(A,B) ∈ D} |A|·|B| ≤ β·|s|²` (its
`k.choose 2` is the positional lift, `sum_badCellTuples_weight_le`) and the cell-size bound
`|C| ≤ m` (its `k.choose 2` is the diagonal charge, `sum_nontransversalCellTuples_weight_le`).
The estimate is only asked to lie in `[0, vol T]` — the shape of a volume times a product of
densities — so that bad tuples are charged by volume.

Two levels, per §3a: the **raw** bridge above is denominator-free, and the **normalized**
corollary divides through by the restricted falling factorial `(|s|)_k`, guard-free under
`x / 0 = 0` (at `s = univ` this is `(|V|)_k`).

`hlocal` concerns a **single** cell tuple: any formulation quantifying over the partition would
restate the conclusion box by box. The bridge is abstract in the supplied local estimate and
does not claim one exists for every `FiniteRelModel L`; the arity-specific wrappers discharge
`hlocal` where the library has a local estimate (`bridgeTwo`, exact at arity `2` with the cell's
own pair density, `δ = 0`; `bridgeThree`, `δ = 7·ε` at arity `3` from
`abs_inducedEmbeddingCountOn_three_sub_le`). The **composite** (§9) chains the edit
transfer (`Relational/Edit.lean`) with quotient counting (`Relational/DiagonalGate.lean`):
`abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass`, its instantiation under a
`CellwiseEditBound` via the exact cellwise-to-aggregate conversion
(`CellwiseEditBound.editDistance_const_le`), the majority-rounding corollary — homogeneity in,
counting out — the chain with the raw bridge, and the normalized composite over `(|s|)_k`. The
composite introduces no coefficient of its own. The volume tiling and the generic profile
substrate live upstream (`Relational/DiagonalGate.lean`, `Relational/BinaryPattern.lean`,
`Relational/TransversalCounting.lean`).
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {Q : Finpartition s} {k : ℕ}

/-! ### The raw bridge -/

omit [FiniteRelational L] in
/-- **Aggregation over the transversal tuples.** Any two weights within `δ · vol` of each other
on the good transversal tuples, and within `vol` of each other on the bad ones, have
transversal sums within `(δ + (k.choose 2)·β) · |s|^k`: the good tuples contribute at most
`δ` times the total volume, and the bad ones at most their volume, which the positional lift
charges to the aggregated bad-pair mass. -/
theorem abs_sum_transversalCellTuples_sub_le (count est : (Fin k → Finset V) → ℝ)
    (D : Finset (Finset V × Finset V)) {δ β : ℝ} (hδ : 0 ≤ δ)
    (hlocal : ∀ T ∈ transversalCellTuples Q, T ∉ badCellTuples Q D →
      |count T - est T| ≤ δ * cellTupleVolume T)
    (hcrude : ∀ T ∈ transversalCellTuples Q, |count T - est T| ≤ cellTupleVolume T)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2) :
    |∑ T ∈ transversalCellTuples Q, count T - ∑ T ∈ transversalCellTuples Q, est T|
      ≤ (δ + (k.choose 2) * β) * (s.card : ℝ) ^ k := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (transversalCellTuples Q)
    (fun T => T ∈ badCellTuples Q D)]
  have hbad : ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∈ badCellTuples Q D),
      |count T - est T| ≤ (k.choose 2) * β * (s.card : ℝ) ^ k := by
    calc ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∈ badCellTuples Q D),
          |count T - est T|
        ≤ ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∈ badCellTuples Q D),
            cellTupleVolume T :=
          Finset.sum_le_sum fun T hT => hcrude T (Finset.mem_filter.mp hT).1
      _ ≤ ∑ T ∈ badCellTuples Q D, cellTupleVolume T :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun T hT => (Finset.mem_filter.mp hT).2) fun T _ _ => cellTupleVolume_nonneg T
      _ ≤ (k.choose 2) * β * (s.card : ℝ) ^ k :=
          sum_badCellTuples_weight_le hmass _ fun _ _ => le_rfl
  have hgood : ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∉ badCellTuples Q D),
      |count T - est T| ≤ δ * (s.card : ℝ) ^ k := by
    calc ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∉ badCellTuples Q D),
          |count T - est T|
        ≤ ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∉ badCellTuples Q D),
            δ * cellTupleVolume T :=
          Finset.sum_le_sum fun T hT =>
            hlocal T (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
      _ = δ * ∑ T ∈ (transversalCellTuples Q).filter (fun T => T ∉ badCellTuples Q D),
            cellTupleVolume T := by rw [Finset.mul_sum]
      _ ≤ δ * ∑ T ∈ transversalCellTuples Q, cellTupleVolume T :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun T _ _ => cellTupleVolume_nonneg T) hδ
      _ ≤ δ * (s.card : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (sum_transversalCellTuples_cellTupleVolume_le Q k) hδ
  calc _ ≤ (k.choose 2) * β * (s.card : ℝ) ^ k + δ * (s.card : ℝ) ^ k := add_le_add hbad hgood
    _ = (δ + (k.choose 2) * β) * (s.card : ℝ) ^ k := by ring

/-- **The raw aggregation bridge.** For a pattern on `k` vertices, a supplied estimate
`est` that lies in `[0, vol T]` on every transversal cell tuple and is within `δ · vol T` of the
induced count on every good one (`hlocal`, a statement about a single tuple), together with the
single aggregated bad-pair mass bound and the cell-size bound, gives

`|inducedEmbeddingCountOn P M (fun _ ↦ s) − Σ_{T transversal} est T|`
`  ≤ (δ + (k.choose 2)·β) · |s|^k + (k.choose 2)·m · |s|^(k−1)`.

Denominator-free and guard-free: no `2 ≤ k`, no positivity of `|s|` or of the cells, no
hypothesis on `β` or `m` beyond the two bounds. `δ` is supplied, never computed (§1 of the
design); both `k.choose 2` are computed — the positional lift and the diagonal charge. -/
theorem abs_inducedEmbeddingCountOn_sub_sum_est_le (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) (est : (Fin k → Finset V) → ℝ) (D : Finset (Finset V × Finset V))
    {δ β : ℝ} {m : ℕ} (hδ : 0 ≤ δ)
    (hlocal : ∀ T ∈ transversalCellTuples Q, T ∉ badCellTuples Q D →
      |(inducedEmbeddingCountOn P M T : ℝ) - est T| ≤ δ * cellTupleVolume T)
    (hest : ∀ T ∈ transversalCellTuples Q, 0 ≤ est T ∧ est T ≤ cellTupleVolume T)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
        - ∑ T ∈ transversalCellTuples Q, est T|
      ≤ (δ + (k.choose 2) * β) * (s.card : ℝ) ^ k
        + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
  have hcrude : ∀ T ∈ transversalCellTuples Q,
      |(inducedEmbeddingCountOn P M T : ℝ) - est T| ≤ cellTupleVolume T := by
    intro T hT
    have h0 : (0 : ℝ) ≤ inducedEmbeddingCountOn P M T := Nat.cast_nonneg _
    have hv := inducedEmbeddingCountOn_le_cellTupleVolume P M T
    obtain ⟨he0, hev⟩ := hest T hT
    rw [abs_le]
    constructor <;> linarith
  have htr := abs_sum_transversalCellTuples_sub_le
    (fun T => (inducedEmbeddingCountOn P M T : ℝ)) est D hδ hlocal hcrude hmass
  have hdiag : |∑ T ∈ nontransversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)|
      ≤ (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
    exact sum_nontransversalCellTuples_weight_le hm _
      fun T _ => inducedEmbeddingCountOn_le_cellTupleVolume P M T
  rw [inducedEmbeddingCountOn_eq_transversal_add_nontransversal P M Q]
  push_cast
  calc |(∑ T ∈ transversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)
          + ∑ T ∈ nontransversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ))
          - ∑ T ∈ transversalCellTuples Q, est T|
      = |(∑ T ∈ transversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)
          - ∑ T ∈ transversalCellTuples Q, est T)
          + ∑ T ∈ nontransversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)| := by
        ring_nf
    _ ≤ |∑ T ∈ transversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)
          - ∑ T ∈ transversalCellTuples Q, est T|
          + |∑ T ∈ nontransversalCellTuples Q, (inducedEmbeddingCountOn P M T : ℝ)| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add htr hdiag

/-! ### The normalized corollary -/

/-- **The normalized bridge.** Dividing the raw bridge through by the restricted falling
factorial `(|s|)_k` — the number of injective `k`-tuples through `s` — gives the density form.
Guard-free under `x / 0 = 0`: at `|s| < k` both sides are `0`, and no positivity hypothesis is
taken (positivity belongs to the inversion lemma `card_injectiveTuplesOn_pos_iff` alone). At
`s = univ` the denominator is `(|V|)_k`, the `injectiveRelationDensity` convention. -/
theorem abs_inducedEmbeddingCountOn_div_sub_sum_est_div_le (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) (est : (Fin k → Finset V) → ℝ) (D : Finset (Finset V × Finset V))
    {δ β : ℝ} {m : ℕ} (hδ : 0 ≤ δ)
    (hlocal : ∀ T ∈ transversalCellTuples Q, T ∉ badCellTuples Q D →
      |(inducedEmbeddingCountOn P M T : ℝ) - est T| ≤ δ * cellTupleVolume T)
    (hest : ∀ T ∈ transversalCellTuples Q, 0 ≤ est T ∧ est T ≤ cellTupleVolume T)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) / (s.card.descFactorial k : ℝ)
        - (∑ T ∈ transversalCellTuples Q, est T) / (s.card.descFactorial k : ℝ)|
      ≤ ((δ + (k.choose 2) * β) * (s.card : ℝ) ^ k
          + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1)) / (s.card.descFactorial k : ℝ) := by
  rw [← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (s.card.descFactorial k) : (0 : ℝ) ≤ _)]
  exact div_le_div_of_nonneg_right
    (abs_inducedEmbeddingCountOn_sub_sum_est_le P M est D hδ hlocal hest hmass hm)
    (Nat.cast_nonneg _)

/-! ### The arity-2 wrapper: exact at the cell level -/

section Two

/-- The two-vertex partition estimate: pair density times box volume on the matching
transversal cell pairs. -/
noncomputable def pairInducedEstimate (P : FiniteRelModel L (Fin 2)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℝ :=
  ∑ T ∈ (transversalCellTuples Q).filter (MatchesProfiles P M),
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * (T 0).card * (T 1).card

/-- **`bridgeTwo`.** At arity `2` the local estimate is exact: on a transversal cell pair the
induced count *is* the palette pair count (`inducedEmbeddingCountOn_two`), so the bridge is
instantiated with `δ = 0` and an empty bad set, and only the diagonal charge `m · |s|`
remains. (An `ε` local error at arity `2` arises only when a coarser density is substituted
for the cell's own — the `IsUniformPair` reading — and is a supplied `δ` like any other.) -/
theorem abs_inducedEmbeddingCountOn_sub_pairInducedEstimate_le [AtMostBinary L]
    {P : FiniteRelModel L (Fin 2)} {M : FiniteRelModel L V}
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 2 => s) : ℝ) - pairInducedEstimate P M Q|
      ≤ m * (s.card : ℝ) := by
  classical
  set est : (Fin 2 → Finset V) → ℝ := fun T =>
    if MatchesProfiles P M T then
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
        * (T 0).card * (T 1).card
    else 0 with hest_def
  have hsum : pairInducedEstimate P M Q = ∑ T ∈ transversalCellTuples Q, est T := by
    rw [pairInducedEstimate, Finset.sum_filter]
  have hvol : ∀ T : Fin 2 → Finset V, cellTupleVolume T = (T 0).card * (T 1).card := by
    intro T; rw [cellTupleVolume, Fin.prod_univ_two]
  have hbridge := abs_inducedEmbeddingCountOn_sub_sum_est_le (Q := Q) P M est ∅ (δ := 0)
    (β := 0) le_rfl ?_ ?_ (by simp) hm
  · rw [hsum]
    refine hbridge.trans (le_of_eq ?_)
    simp
  · intro T hT _
    rw [mem_transversalCellTuples] at hT
    obtain ⟨hmem, hinj⟩ := hT
    have hdisj : Disjoint (T 0) (T 1) :=
      Q.disjoint (Finset.mem_coe.mpr (hmem 0)) (Finset.mem_coe.mpr (hmem 1))
        (fun h => absurd (hinj h) (by decide))
    have heta : ![T 0, T 1] = T := by funext i; fin_cases i <;> rfl
    rw [zero_mul, abs_nonpos_iff, sub_eq_zero, hest_def]
    dsimp only
    by_cases hmatch : MatchesProfiles P M T
    · rw [ite_eq_left hmatch, ← heta,
        inducedEmbeddingCountOn_two hnull (hmatch 0) (hmatch 1) hdisj, pairCount_eq_pairDensity_mul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · rw [ite_eq_right hmatch,
        inducedEmbeddingCountOn_eq_zero_of_not_matchesProfiles hQ hmem hmatch, Nat.cast_zero]
  · intro T _
    rw [hvol, hest_def]
    dsimp only
    split_ifs
    · refine ⟨mul_nonneg (mul_nonneg pairDensity_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _),
        ?_⟩
      have h1 := pairDensity_le_one (R := HasBinaryPairPalette M (binaryPairPalette P 0 1))
        (A := T 0) (B := T 1)
      have h0 : (0 : ℝ) ≤ ((T 0).card : ℝ) * (T 1).card := by positivity
      nlinarith
    · exact ⟨le_rfl, by positivity⟩

end Two

/-! ### The arity-3 wrapper: `δ = 7·ε` from the three-vertex local estimate -/

section Three

/-- **`bridgeThree`.** The arity-`3` instantiation: `δ := 7·ε` from
`abs_inducedEmbeddingCountOn_three_sub_le` on the good transversal triples (those with no
coordinate pair in the non-uniform pair set `D`), the single aggregated mass bound on `D`, and
the cell bound. The conclusion is the shape of the global strong-counting corollary,
`(7ε + 3β) · |s|³ + 3·m · |s|²`, with `3 = 3.choose 2` at both places. The `7` is supplied by the
three-vertex estimate, not computed here (design §1). -/
theorem abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {D : Finset (Finset V × Finset V)} {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε → (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε → (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε → (A, B) ∈ D)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 + 3 * m * (s.card : ℝ) ^ 2 := by
  classical
  set est : (Fin 3 → Finset V) → ℝ := fun T =>
    if MatchesThreeProfiles P M T then
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
        * (T 0).card * (T 1).card * (T 2).card
    else 0 with hest_def
  have hsum : coarseInducedEstimate P M Q = ∑ T ∈ transversalCellTuples Q, est T := by
    rw [coarseInducedEstimate, Finset.sum_filter, transversalCellTriples_eq_transversalCellTuples]
  have hvol : ∀ T : Fin 3 → Finset V,
      cellTupleVolume T = (T 0).card * (T 1).card * (T 2).card := by
    intro T; rw [cellTupleVolume, Fin.prod_univ_three]
  have hbridge := abs_inducedEmbeddingCountOn_sub_sum_est_le (Q := Q) P M est D (δ := 7 * ε)
    (β := β) (by positivity) ?_ ?_ hmass hm
  · rw [hsum]
    refine hbridge.trans (le_of_eq ?_)
    rw [show Nat.choose 3 2 = 3 from rfl]
    norm_num
  · intro T hT hgood
    rw [mem_transversalCellTuples] at hT
    obtain ⟨hmem, hinj⟩ := hT
    rw [mem_badCellTuples] at hgood
    push Not at hgood
    have hne : ∀ i j : Fin 3, i ≠ j → T i ≠ T j := fun i j hij h => hij (hinj h)
    have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j) := fun i j hij =>
      Q.disjoint (Finset.mem_coe.mpr (hmem i)) (Finset.mem_coe.mpr (hmem j)) (hne i j hij)
    have hnotD : ∀ i j : Fin 3, i < j → (T i, T j) ∉ D := fun i j hij hmemD =>
      hgood hmem i j hij hmemD
    have heta : ![T 0, T 1, T 2] = T := by funext i; fin_cases i <;> rfl
    rw [hvol, hest_def]
    dsimp only
    by_cases hmatch : MatchesThreeProfiles P M T
    · rw [ite_eq_left hmatch]
      have h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1) ε :=
        by_contra fun hcon => hnotD 0 1 (by decide) (hD01 _ (hmem 0) _ (hmem 1) hcon)
      have h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2) ε :=
        by_contra fun hcon => hnotD 0 2 (by decide) (hD02 _ (hmem 0) _ (hmem 2) hcon)
      have h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) ε :=
        by_contra fun hcon => hnotD 1 2 (by decide) (hD12 _ (hmem 1) _ (hmem 2) hcon)
      have hmain := abs_inducedEmbeddingCountOn_three_sub_le (A := T 0) (B := T 1) (C := T 2)
        hnull (hmatch 0) (hmatch 1) (hmatch 2) (hdisj 0 1 (by decide)) (hdisj 0 2 (by decide))
        (hdisj 1 2 (by decide)) hε0 hε1 h01 h02 h12
      rw [heta] at hmain
      refine hmain.trans (le_of_eq ?_)
      ring
    · rw [ite_eq_right hmatch,
        inducedEmbeddingCountOn_eq_zero_of_not_matchesThreeProfiles hQ hmem hmatch, Nat.cast_zero,
        sub_zero, abs_zero]
      positivity
  · intro T _
    rw [hvol, hest_def]
    dsimp only
    split_ifs
    · have hd1 : pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) ≤ 1 :=
        mul_le_one₀ (mul_le_one₀ pairDensity_le_one pairDensity_nonneg pairDensity_le_one)
          pairDensity_nonneg pairDensity_le_one
      have hd0 : (0 : ℝ)
          ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) :=
        mul_nonneg (mul_nonneg pairDensity_nonneg pairDensity_nonneg) pairDensity_nonneg
      have hv : (0 : ℝ) ≤ ((T 0).card : ℝ) * (T 1).card * (T 2).card := by positivity
      refine ⟨by positivity, ?_⟩
      calc _ = (pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
              * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
              * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2))
            * (((T 0).card : ℝ) * (T 1).card * (T 2).card) := by ring
        _ ≤ 1 * (((T 0).card : ℝ) * (T 1).card * (T 2).card) :=
            mul_le_mul_of_nonneg_right hd1 hv
        _ = _ := one_mul _
    · exact ⟨le_rfl, by positivity⟩

end Three

/-! ### The composite: approximation to counting -/

section Composite

/-- **The composite theorem** (design §9): edit transfer moves the count from `M` to an
indivisible approximant `N`, and quotient counting evaluates `N`'s count exactly up to the
diagonal charge. Everything is in `s`-restricted units — restricted count, `s`-box edit mass,
extension factor `|s|^(k−1)` — so the two terms compose with no off-`s` remainder. No new
coefficient: the edit coefficient `Σ_R k^(arity R)` and the diagonal `k.choose 2` are the
audited ones. Hypotheses: `N` indivisible for `Q`, nullary agreement, cells of size at most
`m`. -/
theorem abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass
    (P : FiniteRelModel L (Fin k)) {M N : FiniteRelModel L V} (hN : N.IsIndivisibleFor Q)
    (hnull : NullaryCompatible M N) {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) - quotientInducedCount P N Q|
      ≤ (∑ R : RelSymbol L,
          (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
          * (s.card : ℝ) ^ (k - 1)
        + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) :=
  calc |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) - quotientInducedCount P N Q|
      ≤ |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
            - inducedEmbeddingCountOn P N (fun _ : Fin k => s)|
          + |(inducedEmbeddingCountOn P N (fun _ : Fin k => s) : ℝ)
            - quotientInducedCount P N Q| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (abs_inducedEmbeddingCountOn_sub_le_editMass P M N hnull s)
          (hN.abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le P hm)

/-- **The composite under a cellwise edit bound.** With `CellwiseEditBound M N Q ε`, the
`s`-box edit mass of each positive-arity symbol is at most `ε · |s|^(arity R)`
(`CellwiseEditBound.editDistance_const_le`, exact over the partition boxes), and nullary
agreement makes the arity-`0` edit mass exactly `0`; so the edit term is bounded by
`Σ_{R, arity R > 0} k^(arity R) · ε · |s|^(arity R)`, a sum over the positive-arity symbols only
(the nullary symbols contribute nothing, and are not charged). This is "approximation yields
counting": a cellwise approximation in, a global induced count out. -/
theorem abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_of_cellwiseEditBound
    (P : FiniteRelModel L (Fin k)) {M N : FiniteRelModel L V} (hN : N.IsIndivisibleFor Q)
    (hnull : NullaryCompatible M N) {ε : ℝ} (hce : CellwiseEditBound M N Q ε)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) - quotientInducedCount P N Q|
      ≤ (∑ R ∈ (Finset.univ : Finset (RelSymbol L)).filter (fun R => 0 < (R.1 : ℕ)),
          (k : ℝ) ^ (R.1 : ℕ) * (ε * (s.card : ℝ) ^ (R.1 : ℕ)))
          * (s.card : ℝ) ^ (k - 1)
        + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) := by
  classical
  have hsum : ∑ R : RelSymbol L,
        (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s)
      ≤ ∑ R ∈ (Finset.univ : Finset (RelSymbol L)).filter (fun R => 0 < (R.1 : ℕ)),
          (k : ℝ) ^ (R.1 : ℕ) * (ε * (s.card : ℝ) ^ (R.1 : ℕ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun R : RelSymbol L => 0 < (R.1 : ℕ))]
    have hzero : ∑ R ∈ (Finset.univ : Finset (RelSymbol L)).filter (fun R => ¬ 0 < (R.1 : ℕ)),
        (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s) = 0 := by
      refine Finset.sum_eq_zero fun R hR => ?_
      rw [Finset.mem_filter, not_lt, Nat.le_zero] at hR
      rw [editDistance_const_eq_zero_of_nullaryCompatible hnull s hR.2 R.2, Nat.cast_zero,
        mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_le_sum fun R hR => mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hce.editDistance_const_le (Finset.mem_filter.mp hR).2 R.2
  have hpow : (0 : ℝ) ≤ (s.card : ℝ) ^ (k - 1) := by positivity
  exact (abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass P hN hnull hm).trans
    (add_le_add_left (mul_le_mul_of_nonneg_right hsum hpow) _)

/-- **Homogeneity in, counting out.** Majority rounding of `M` over `Q` is indivisible,
nullary-compatible, and cellwise within `ε` under cell homogeneity
(`cellwiseEditBound_majorityRound_of_isHomogeneousCell`); the composite then reads the induced
count of `M` off the quotient of its rounding. -/
theorem abs_inducedEmbeddingCountOn_sub_quotientInducedCount_majorityRound_le
    (P : FiniteRelModel L (Fin k)) (M : FiniteRelModel L V) (Q : Finpartition s) {ε : ℝ}
    (hhom : ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → Q.parts),
      IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
        - quotientInducedCount P (M.majorityRound Q) Q|
      ≤ (∑ R ∈ (Finset.univ : Finset (RelSymbol L)).filter (fun R => 0 < (R.1 : ℕ)),
          (k : ℝ) ^ (R.1 : ℕ) * (ε * (s.card : ℝ) ^ (R.1 : ℕ)))
          * (s.card : ℝ) ^ (k - 1)
        + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1) :=
  abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_of_cellwiseEditBound P
    (majorityRound_isIndivisibleFor M Q) (nullaryCompatible_majorityRound M Q)
    (cellwiseEditBound_majorityRound_of_isHomogeneousCell M Q hhom) hm

/-- **The composite chained with the raw bridge.** When the approximant's transversal count is
further compared with a supplied estimate, the bridge's `(δ + (k.choose 2)·β) · |s|^k` is added:
edit transfer from `M` to `N`, then `abs_inducedEmbeddingCountOn_sub_sum_est_le` for `N`. -/
theorem abs_inducedEmbeddingCountOn_sub_sum_est_le_of_editMass (P : FiniteRelModel L (Fin k))
    {M N : FiniteRelModel L V} (hnull : NullaryCompatible M N)
    (est : (Fin k → Finset V) → ℝ) (D : Finset (Finset V × Finset V))
    {δ β : ℝ} {m : ℕ} (hδ : 0 ≤ δ)
    (hlocal : ∀ T ∈ transversalCellTuples Q, T ∉ badCellTuples Q D →
      |(inducedEmbeddingCountOn P N T : ℝ) - est T| ≤ δ * cellTupleVolume T)
    (hest : ∀ T ∈ transversalCellTuples Q, 0 ≤ est T ∧ est T ≤ cellTupleVolume T)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
        - ∑ T ∈ transversalCellTuples Q, est T|
      ≤ (∑ R : RelSymbol L,
          (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
          * (s.card : ℝ) ^ (k - 1)
        + ((δ + (k.choose 2) * β) * (s.card : ℝ) ^ k
          + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1)) :=
  calc |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
          - ∑ T ∈ transversalCellTuples Q, est T|
      ≤ |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
            - inducedEmbeddingCountOn P N (fun _ : Fin k => s)|
          + |(inducedEmbeddingCountOn P N (fun _ : Fin k => s) : ℝ)
            - ∑ T ∈ transversalCellTuples Q, est T| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (abs_inducedEmbeddingCountOn_sub_le_editMass P M N hnull s)
          (abs_inducedEmbeddingCountOn_sub_sum_est_le P N est D hδ hlocal hest hmass hm)

/-- **The normalized composite.** The composite divided through by `(|s|)_k`, guard-free under
`x / 0 = 0`; at `s = univ` the denominator is `(|V|)_k`. -/
theorem abs_inducedEmbeddingCountOn_div_sub_quotientInducedCount_div_le
    (P : FiniteRelModel L (Fin k)) {M N : FiniteRelModel L V} (hN : N.IsIndivisibleFor Q)
    (hnull : NullaryCompatible M N) {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) / (s.card.descFactorial k : ℝ)
        - (quotientInducedCount P N Q : ℝ) / (s.card.descFactorial k : ℝ)|
      ≤ ((∑ R : RelSymbol L,
          (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
          * (s.card : ℝ) ^ (k - 1)
        + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1)) / (s.card.descFactorial k : ℝ) := by
  rw [← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (s.card.descFactorial k) : (0 : ℝ) ≤ _)]
  exact div_le_div_of_nonneg_right
    (abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass P hN hnull hm)
    (Nat.cast_nonneg _)

/-- **The normalized whole chain.** The edit-to-estimate chain
`abs_inducedEmbeddingCountOn_sub_sum_est_le_of_editMass` divided through by `(|s|)_k`, including
the bridge's `(δ + (k.choose 2)·β) · |s|^k` term, guard-free under `x / 0 = 0`. -/
theorem abs_inducedEmbeddingCountOn_div_sub_sum_est_div_le_of_editMass
    (P : FiniteRelModel L (Fin k)) {M N : FiniteRelModel L V} (hnull : NullaryCompatible M N)
    (est : (Fin k → Finset V) → ℝ) (D : Finset (Finset V × Finset V))
    {δ β : ℝ} {m : ℕ} (hδ : 0 ≤ δ)
    (hlocal : ∀ T ∈ transversalCellTuples Q, T ∉ badCellTuples Q D →
      |(inducedEmbeddingCountOn P N T : ℝ) - est T| ≤ δ * cellTupleVolume T)
    (hest : ∀ T ∈ transversalCellTuples Q, 0 ≤ est T ∧ est T ≤ cellTupleVolume T)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ) / (s.card.descFactorial k : ℝ)
        - (∑ T ∈ transversalCellTuples Q, est T) / (s.card.descFactorial k : ℝ)|
      ≤ ((∑ R : RelSymbol L,
          (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
          * (s.card : ℝ) ^ (k - 1)
        + ((δ + (k.choose 2) * β) * (s.card : ℝ) ^ k
          + (k.choose 2) * m * (s.card : ℝ) ^ (k - 1))) / (s.card.descFactorial k : ℝ) := by
  rw [← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (s.card.descFactorial k) : (0 : ℝ) ≤ _)]
  exact div_le_div_of_nonneg_right
    (abs_inducedEmbeddingCountOn_sub_sum_est_le_of_editMass P hnull est D hδ hlocal hest hmass hm)
    (Nat.cast_nonneg _)

end Composite

/-! ### Tests and adversarial examples -/

section Tests

/-- The unique model of the empty language. -/
private def emptyModel (W : Type*) : FiniteRelModel FirstOrder.Language.empty W :=
  ⟨fun {_} R _ => R.elim⟩

-- **Volume tiling on the indiscrete partition**, statement-level: with `⊤` the single cell pair
-- carries the whole volume `4²` (`sum_cellTupleVolume_eq`, a `ProductSpaces` adapter).
example : ∑ T ∈ Fintype.piFinset fun _ : Fin 2 =>
      (⊤ : Finpartition (Finset.univ : Finset (Fin 4))).parts, cellTupleVolume T
    = ((Finset.univ : Finset (Fin 4)).card : ℝ) ^ 2 :=
  sum_cellTupleVolume_eq _ _

-- **The raw bridge with the exact estimate.** Taking `est := count` itself, `δ = 0`, and an
-- empty bad set, the bridge reduces to the diagonal gate: statement-level, any partition.
example (P : FiniteRelModel FirstOrder.Language.empty (Fin 3))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P (emptyModel (Fin 3)) (fun _ : Fin 3 => Finset.univ) : ℝ)
        - ∑ T ∈ transversalCellTuples Q, (inducedEmbeddingCountOn P (emptyModel (Fin 3)) T : ℝ)|
      ≤ (0 + (Nat.choose 3 2) * 0) * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ 3
        + (Nat.choose 3 2) * m * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ (3 - 1) :=
  abs_inducedEmbeddingCountOn_sub_sum_est_le P _ _ ∅ le_rfl
    (fun T _ _ => by simp)
    (fun T _ => ⟨Nat.cast_nonneg _, inducedEmbeddingCountOn_le_cellTupleVolume _ _ T⟩)
    (by simp) hm

-- **`k = 0` is guard-free**: the empty pattern, an empty bad set, `δ = 0`; both sides `0`.
example (Q : Finpartition (Finset.univ : Finset (Fin 3))) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn (emptyModel (Fin 0)) (emptyModel (Fin 3))
          (fun _ : Fin 0 => Finset.univ) : ℝ)
        - ∑ T ∈ transversalCellTuples Q,
            (inducedEmbeddingCountOn (emptyModel (Fin 0)) (emptyModel (Fin 3)) T : ℝ)|
      ≤ 0 := by
  simpa using abs_inducedEmbeddingCountOn_sub_sum_est_le (emptyModel (Fin 0)) (emptyModel (Fin 3))
    (fun T => (inducedEmbeddingCountOn (emptyModel (Fin 0)) (emptyModel (Fin 3)) T : ℝ)) ∅
    (δ := 0) (β := 0) le_rfl (fun T _ _ => by simp)
    (fun T _ => ⟨Nat.cast_nonneg _, inducedEmbeddingCountOn_le_cellTupleVolume _ _ T⟩)
    (by simp) hm

-- **The normalized corollary at the `|s| < k` endpoint** is `0 ≤ 0`: three vertices, pattern on
-- four, `(3)_4 = 0`.
example (Q : Finpartition (Finset.univ : Finset (Fin 3))) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn (emptyModel (Fin 4)) (emptyModel (Fin 3))
          (fun _ : Fin 4 => Finset.univ) : ℝ)
          / (((Finset.univ : Finset (Fin 3)).card.descFactorial 4 : ℕ) : ℝ)
        - (∑ T ∈ transversalCellTuples Q,
            (inducedEmbeddingCountOn (emptyModel (Fin 4)) (emptyModel (Fin 3)) T : ℝ))
          / (((Finset.univ : Finset (Fin 3)).card.descFactorial 4 : ℕ) : ℝ)|
      ≤ ((0 + (Nat.choose 4 2) * 0) * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ 4
          + (Nat.choose 4 2) * m * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ (4 - 1))
        / (((Finset.univ : Finset (Fin 3)).card.descFactorial 4 : ℕ) : ℝ) :=
  abs_inducedEmbeddingCountOn_div_sub_sum_est_div_le _ _ _ ∅ le_rfl (fun T _ _ => by simp)
    (fun T _ => ⟨Nat.cast_nonneg _, inducedEmbeddingCountOn_le_cellTupleVolume _ _ T⟩)
    (by simp) hm

example : ((Finset.univ : Finset (Fin 3)).card.descFactorial 4 : ℕ) = 0 := by decide

-- **The arity-3 wrapper recovers the global strong-counting shape**: same conclusion as
-- `BinaryPaletteStrongWitness.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le`'s
-- diagonal-charged form, from uniform-pair hypotheses instead of a strong witness.
example [AtMostBinary L] {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {D : Finset (Finset V × Finset V)} {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε → (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε → (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε → (A, B) ∈ D)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 + 3 * m * (s.card : ℝ) ^ 2 :=
  abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le hQ hnull hε0 hε1 hmass hD01 hD02 hD12 hm

-- **The arity-2 wrapper is exact up to the diagonal**, statement-level.
example [AtMostBinary L] {P : FiniteRelModel L (Fin 2)} {M : FiniteRelModel L V}
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 2 => s) : ℝ) - pairInducedEstimate P M Q|
      ≤ m * (s.card : ℝ) :=
  abs_inducedEmbeddingCountOn_sub_pairInducedEstimate_le hQ hnull hm

-- **The composite on the empty language** reduces to quotient counting: every model is
-- indivisible and nullary-compatible with every other, and the edit mass is an empty sum.
example (Q : Finpartition (Finset.univ : Finset (Fin 3))) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3))
          (fun _ : Fin 3 => Finset.univ) : ℝ)
        - quotientInducedCount (emptyModel (Fin 3)) (emptyModel (Fin 3)) Q|
      ≤ (Nat.choose 3 2) * m * ((Finset.univ : Finset (Fin 3)).card : ℝ) ^ (3 - 1) := by
  have h := abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass
    (emptyModel (Fin 3)) (M := emptyModel (Fin 3)) (N := emptyModel (Fin 3))
    (fun _ R => R.elim) (fun R => R.elim) hm
  have : IsEmpty (RelSymbol FirstOrder.Language.empty) := ⟨fun R => R.2.elim⟩
  simpa using h

-- **Homogeneity in, counting out**, statement-level: the majority-rounding corollary.
example [AtMostBinary L] (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) {ε : ℝ}
    (hhom : ∀ (n : ℕ), 0 < n → ∀ (S : L.Relations n) (C : Fin n → Q.parts),
      IsHomogeneousCell (M.Holds S) (fun i ↦ (C i : Finset V)) ε)
    {m : ℕ} (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin 3 => s) : ℝ)
        - quotientInducedCount P (M.majorityRound Q) Q|
      ≤ (∑ R ∈ (Finset.univ : Finset (RelSymbol L)).filter (fun R => 0 < (R.1 : ℕ)),
          (3 : ℝ) ^ (R.1 : ℕ) * (ε * (s.card : ℝ) ^ (R.1 : ℕ)))
          * (s.card : ℝ) ^ (3 - 1)
        + (Nat.choose 3 2) * m * (s.card : ℝ) ^ (3 - 1) :=
  abs_inducedEmbeddingCountOn_sub_quotientInducedCount_majorityRound_le P M Q hhom hm

-- **The nullary symbols are not charged**: with one nullary symbol and nothing else, the
-- positive-arity sum is empty, so the cellwise composite's edit term is `0` for any `ε`.
example : ((Finset.univ : Finset (RelSymbol (singleRelLang 0))).filter
    (fun R => 0 < (R.1 : ℕ))) = ∅ := by decide

-- **`k = 0` composite is guard-free**: both sides `0` on the empty language.
example (Q : Finpartition (Finset.univ : Finset (Fin 3))) {m : ℕ}
    (hm : ∀ C ∈ Q.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn (emptyModel (Fin 0)) (emptyModel (Fin 3))
          (fun _ : Fin 0 => Finset.univ) : ℝ)
        - quotientInducedCount (emptyModel (Fin 0)) (emptyModel (Fin 3)) Q| ≤ 0 := by
  have h := abs_inducedEmbeddingCountOn_sub_quotientInducedCount_le_editMass
    (emptyModel (Fin 0)) (M := emptyModel (Fin 3)) (N := emptyModel (Fin 3))
    (fun _ R => R.elim) (fun R => R.elim) hm
  have : IsEmpty (RelSymbol FirstOrder.Language.empty) := ⟨fun R => R.2.elim⟩
  simpa using h

-- **Profile matching agrees with the `Fin 3` predicate** definitionally.
example {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} (T : Fin 3 → Finset V) :
    MatchesThreeProfiles P M T ↔ MatchesProfiles P M T :=
  matchesThreeProfiles_iff_matchesProfiles T

end Tests

end RegularityLemmata
