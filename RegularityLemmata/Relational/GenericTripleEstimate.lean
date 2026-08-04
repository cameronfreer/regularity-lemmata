/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.WeakenedCountingGate

/-!
# Route (b) ladder step 2: the indexed-box triple estimate

`ARCHITECTURE.md` route (b) ladder step 2. The weakened-counting gate produced the two inputs
the count needs: a `7 * ε` estimate on triples all of whose coordinate pairs are uniform, and
a crude volume bound on the rest. This file combines them, **generically in a bad-pair set
`D`** — no proxy, no palette-union, no selection appears.

## Indexing cells versus counting boxes

The estimate is stated for a **box map** `g` with `g C ⊆ C`, and the two roles are kept
apart:

* cells `C ∈ Q.parts` supply the index, the disjointness, and the mass accounting;
* `g C` is the box actually counted.

`D` is a set of **cell** pairs, its mass is **cell**-weighted, and its uniformity hypothesis
is about the **boxes** `(g A, g B)` and is asked only of **distinct** cells. That is exactly
the shape a set of selected pairs has: its elements are proxy pairs — never diagonal — while
membership records a failure on their representative boxes. Distinctness at the point of use
comes from `transversalCellTriples_ne`.

Nothing here needs the boxes to cover the host. A representative box can be a `1/(2q)`
fraction of its cell, so a covering charge would be of order `#s ^ 3` and useless; instead
proxy disjointness carries the accounting and the boxes only shrink. Counts inside the boxes
are genuine copies in the original host.

**This is the estimate, not step 5.** No selection is performed and no summit is assembled.

## The statement

`abs_representativeInducedCount_sub_estimate_le` : if the pairs whose BOXES fail any of the
three required palette-uniformity conditions all lie in `D`, and `D` carries CELL pair mass
at most `β * #s ^ 2`, then

`|representativeInducedCount - representativeInducedEstimate| ≤ (7 * ε + 3 * β) * #s ^ 3`.

`abs_transversalInducedCount_sub_coarseInducedEstimate_le` is the partition case `g C = C`.

## Which hypothesis does which job

The four ingredients stay separate, and each is used exactly once:

* **`D` covers uniformity failures** (`hD01`, `hD02`, `hD12`) — one per coordinate pair, at
  that pair's own palette. This is all `D` is asked to do.
* **Profile matching** comes from the triple lying in `MatchesThreeProfiles`, which is where
  `coarseInducedEstimate` already sums; non-matching triples contribute nothing to either
  side (`transversalInducedCount_eq_sum_matching`, generic profile-elimination infrastructure
  living with the rest of the counting substrate). It is NOT read off `D`.
* **Transversality** supplies pairwise disjointness (`transversalCellTriples_disjoint`).
* **Good triples** consume `abs_inducedEmbeddingCountOn_three_sub_le` — the `7 * ε` estimate.
* **Bad triples** consume only the crude bound: both the count and the density product lie in
  `[0, volume]`, so their difference is at most the BOX volume, which is at most the CELL
  volume since `g C ⊆ C`, and `badTripleVolume_le` sums the cell volumes to
  `3 * β * #s ^ 3`. No density estimate is used on a bad triple.

## Not done here

Two things stand between this and a summit. First, `selectedPaletteNonuniformPairs` is
indexed by `ProxyIndex Q` while the box map here is a plain `Finset V → Finset V`, so the
specialization needs the adapter that reads a selection at a cell of `Q`. Second, and harder:
the positivity arithmetic. The representative-volume floor is what makes the surviving count
positive, and it must be checked for a circular dependence on the fine bound `q`, since the
candidate condition is `#C ≤ 2 * q * #(g C)`. **Step 5 stays closed** until that check is
done.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V} {Q : Finpartition s}
  {L : FirstOrder.Language} [FiniteRelational L] [AtMostBinary L]
  {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}

/-! ### The crude bound on a single triple -/

omit [AtMostBinary L] in
/-- On ANY triple both the count and the density product lie in `[0, volume]`, so their
difference is at most the volume. This is the only estimate a bad triple receives. -/
theorem abs_count_sub_densityProduct_le_volume (T : Fin 3 → Finset V) :
    |(inducedEmbeddingCountOn P M T : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
            * (T 0).card * (T 1).card * (T 2).card|
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
  have hcount0 : (0 : ℝ) ≤ (inducedEmbeddingCountOn P M T : ℝ) := by positivity
  have hcountv : (inducedEmbeddingCountOn P M T : ℝ)
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
    inducedEmbeddingCountOn_le_cellTripleVolume P M T
  have hd : pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ pairDensity_le_one pairDensity_nonneg pairDensity_le_one)
      pairDensity_nonneg pairDensity_le_one
  have hd0 : (0 : ℝ) ≤ pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) :=
    mul_nonneg (mul_nonneg pairDensity_nonneg pairDensity_nonneg) pairDensity_nonneg
  have hv : (0 : ℝ) ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith [hcount0, hcountv, hd, hd0, hv]

/-! ### Representative boxes over a proxy index -/

/-- The count over REPRESENTATIVE boxes: proxy cells index the triples and supply
disjointness and mass accounting, while the box actually counted at a cell `C` is `g C ⊆ C`.
Every copy counted is a genuine copy in the host. -/
def representativeInducedCount (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) (g : Finset V → Finset V) : ℕ :=
  ∑ T ∈ transversalCellTriples Q, inducedEmbeddingCountOn P M (fun i => g (T i))

open Classical in
/-- The matching-triple density estimate on the same boxes. -/
noncomputable def representativeInducedEstimate (P : FiniteRelModel L (Fin 3))
    (M : FiniteRelModel L V) (Q : Finpartition s) (g : Finset V → Finset V) : ℝ :=
  ∑ T ∈ (transversalCellTriples Q).filter
      (fun T => MatchesThreeProfiles P M (fun i => g (T i))),
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g (T 0)) (g (T 1))
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (g (T 0)) (g (T 2))
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (g (T 1)) (g (T 2))
      * (g (T 0)).card * (g (T 1)).card * (g (T 2)).card

open Classical in
/-- Both sides live on the triples whose REPRESENTATIVE boxes match profiles. -/
theorem representativeInducedCount_eq_sum_matching (hQ : Q ≤ binaryProfilePartition M s)
    {g : Finset V → Finset V} (hg : ∀ C ∈ Q.parts, g C ⊆ C) :
    (representativeInducedCount P M Q g : ℝ)
      = ∑ T ∈ (transversalCellTriples Q).filter
          (fun T => MatchesThreeProfiles P M (fun i => g (T i))),
          (inducedEmbeddingCountOn P M (fun i => g (T i)) : ℝ) := by
  classical
  rw [representativeInducedCount]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not
    (transversalCellTriples Q) (fun T => MatchesThreeProfiles P M (fun i => g (T i)))
    (fun T => (inducedEmbeddingCountOn P M (fun i => g (T i)) : ℝ))]
  have hzero : ∑ T ∈ (transversalCellTriples Q).filter
      (fun T => ¬ MatchesThreeProfiles P M (fun i => g (T i))),
      (inducedEmbeddingCountOn P M (fun i => g (T i)) : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [Finset.mem_filter] at hT
    rw [inducedEmbeddingCountOn_eq_zero_of_not_matchesThreeProfiles_of_subset hQ
      (transversalCellTriples_cell_mem hT.1)
      (fun i => hg _ (transversalCellTriples_cell_mem hT.1 i)) hT.2]
    norm_num
  rw [hzero, add_zero]

@[simp] theorem representativeInducedCount_id (P : FiniteRelModel L (Fin 3))
    (M : FiniteRelModel L V) (Q : Finpartition s) :
    representativeInducedCount P M Q (fun C => C) = transversalInducedCount P M Q := rfl

open Classical in
@[simp] theorem representativeInducedEstimate_id (P : FiniteRelModel L (Fin 3))
    (M : FiniteRelModel L V) (Q : Finpartition s) :
    representativeInducedEstimate P M Q (fun C => C) = coarseInducedEstimate P M Q := rfl

/-! ### The indexed-box estimate -/

open Classical in
/-- **The indexed-box triple estimate.** Proxy cells index the triples; the boxes counted are
the representatives `g C ⊆ C`. The bad-pair set `D` is a set of PROXY pairs, its uniformity
hypothesis is about the REPRESENTATIVE boxes, and its mass is proxy-weighted — which is
exactly the shape a selected-pair set has. No representative cover is needed and no uncovered
mass appears: proxy disjointness carries the accounting, and the boxes only shrink. -/
theorem abs_representativeInducedCount_sub_estimate_le
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {g : Finset V → Finset V} (hg : ∀ C ∈ Q.parts, g C ⊆ C)
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g A) (g B) ε →
        (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (g A) (g B) ε →
        (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (g A) (g B) ε →
        (A, B) ∈ D) :
    |(representativeInducedCount P M Q g : ℝ) - representativeInducedEstimate P M Q g|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 := by
  classical
  set S := (transversalCellTriples Q).filter
    (fun T => MatchesThreeProfiles P M (fun i => g (T i))) with hS
  set bad : (Fin 3 → Finset V) → Prop := fun T =>
    (T 0, T 1) ∈ D ∨ (T 0, T 2) ∈ D ∨ (T 1, T 2) ∈ D with hbad
  set f : (Fin 3 → Finset V) → ℝ := fun T =>
    (inducedEmbeddingCountOn P M (fun i => g (T i)) : ℝ)
      - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g (T 0)) (g (T 1))
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (g (T 0)) (g (T 2))
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (g (T 1)) (g (T 2))
          * (g (T 0)).card * (g (T 1)).card * (g (T 2)).card with hf
  have hdiff : (representativeInducedCount P M Q g : ℝ)
        - representativeInducedEstimate P M Q g = ∑ T ∈ S, f T := by
    rw [representativeInducedCount_eq_sum_matching hQ hg, representativeInducedEstimate, hS,
      hf, ← Finset.sum_sub_distrib]
  -- Representative volume never exceeds proxy volume.
  have hvolle : ∀ T ∈ transversalCellTriples Q,
      ((g (T 0)).card * (g (T 1)).card * (g (T 2)).card : ℝ)
        ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
    intro T hT
    have h : ∀ i, ((g (T i)).card : ℝ) ≤ ((T i).card : ℝ) := fun i => by
      exact_mod_cast Finset.card_le_card (hg _ (transversalCellTriples_cell_mem hT i))
    have h0 : ∀ i, (0 : ℝ) ≤ ((g (T i)).card : ℝ) := fun i => by positivity
    exact mul_le_mul (mul_le_mul (h 0) (h 1) (h0 1) (by positivity)) (h 2) (h0 2)
      (by positivity)
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← Finset.sum_filter_add_sum_filter_not S bad (fun T => |f T|)]
  have hs3 : (0 : ℝ) ≤ (s.card : ℝ) ^ 3 := by positivity
  have hSsub : S ⊆ transversalCellTriples Q := by rw [hS]; exact Finset.filter_subset _ _
  -- Bad triples: the crude bound on the representative box, then the proxy volume.
  have hbadsum : ∑ T ∈ S.filter bad, |f T| ≤ 3 * β * (s.card : ℝ) ^ 3 := by
    have hstep : ∑ T ∈ S.filter bad, |f T|
        ≤ ∑ T ∈ S.filter bad, ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
      Finset.sum_le_sum fun T hT =>
        le_trans (abs_count_sub_densityProduct_le_volume (fun i => g (T i)))
          (hvolle T (hSsub (Finset.mem_filter.mp hT).1))
    refine hstep.trans ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
      (fun T _ _ => by positivity)) (badTripleVolume_le hD hmass)
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hSsub hT.1, hT.2⟩
  -- Good triples: the pointwise `7 * ε` estimate on the representative boxes.
  have hgoodsum : ∑ T ∈ S.filter (fun T => ¬ bad T), |f T| ≤ 7 * ε * (s.card : ℝ) ^ 3 := by
    have hstep : ∀ T ∈ S.filter (fun T => ¬ bad T),
        |f T| ≤ 7 * ε * ((T 0).card * (T 1).card * (T 2).card : ℝ) := by
      intro T hT
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hT
      obtain ⟨⟨hTtrans, hTmatch⟩, hTgood⟩ := hT
      rw [hbad] at hTgood
      push Not at hTgood
      have hmem : ∀ i, T i ∈ Q.parts := transversalCellTriples_cell_mem hTtrans
      have hsub : ∀ i, g (T i) ⊆ T i := fun i => hg _ (hmem i)
      have heta : ![g (T 0), g (T 1), g (T 2)] = fun i => g (T i) := by
        funext i; fin_cases i <;> rfl
      have h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1))
          (g (T 0)) (g (T 1)) ε := by
        by_contra hcon
        exact hTgood.1 (hD01 _ (hmem 0) _ (hmem 1)
          (transversalCellTriples_ne hTtrans (by decide : (0 : Fin 3) ≠ 1)) hcon)
      have h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2))
          (g (T 0)) (g (T 2)) ε := by
        by_contra hcon
        exact hTgood.2.1 (hD02 _ (hmem 0) _ (hmem 2)
          (transversalCellTriples_ne hTtrans (by decide : (0 : Fin 3) ≠ 2)) hcon)
      have h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2))
          (g (T 1)) (g (T 2)) ε := by
        by_contra hcon
        exact hTgood.2.2 (hD12 _ (hmem 1) _ (hmem 2)
          (transversalCellTriples_ne hTtrans (by decide : (1 : Fin 3) ≠ 2)) hcon)
      have hmain := abs_inducedEmbeddingCountOn_three_sub_le
        (A := g (T 0)) (B := g (T 1)) (C := g (T 2)) hnull
        (hTmatch 0) (hTmatch 1) (hTmatch 2)
        ((transversalCellTriples_disjoint hTtrans (by decide : (0 : Fin 3) ≠ 1)).mono
          (hsub 0) (hsub 1))
        ((transversalCellTriples_disjoint hTtrans (by decide : (0 : Fin 3) ≠ 2)).mono
          (hsub 0) (hsub 2))
        ((transversalCellTriples_disjoint hTtrans (by decide : (1 : Fin 3) ≠ 2)).mono
          (hsub 1) (hsub 2))
        hε0 hε1 h01 h02 h12
      rw [heta] at hmain
      simp only [hf]
      have hvT := hvolle T hTtrans
      nlinarith [hmain, hvT, hε0]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hvol : ∑ T ∈ S.filter (fun T => ¬ bad T),
        ((T 0).card * (T 1).card * (T 2).card : ℝ) ≤ (s.card : ℝ) ^ 3 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
        (fun T _ _ => by positivity)) (sum_transversal_volume_le Q)
      exact hSsub (Finset.mem_filter.mp hT).1
    nlinarith [hvol, hε0]
  linarith [hbadsum, hgoodsum]

/-! ### The partition case -/

open Classical in
/-- The original partition estimate is the case `g C = C`: the boxes counted are the cells
themselves. -/
theorem abs_transversalInducedCount_sub_coarseInducedEstimate_le
    (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε → (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε → (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε → (A, B) ∈ D) :
    |(transversalInducedCount P M Q : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 := by
  have h := abs_representativeInducedCount_sub_estimate_le (g := fun C => C) hQ hnull
    (fun C _ => le_refl C) hD hε0 hε1 hmass
    (fun A hA B hB _ hcon => hD01 A hA B hB hcon)
    (fun A hA B hB _ hcon => hD02 A hA B hB hcon)
    (fun A hA B hB _ hcon => hD12 A hA B hB hcon)
  rwa [representativeInducedCount_id, representativeInducedEstimate_id] at h

/-! ### Tests -/

section Tests

-- The box map may shrink strictly, and `D` never needs a diagonal pair: the uniformity
-- hypotheses are asked only of DISTINCT cells. So a nonuniform diagonal box `(g A, g A)` is
-- no obstacle, which is what makes a set of proxy-pair events admissible as `D`.
example (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M)
    {g : Finset V → Finset V} (hg : ∀ C ∈ Q.parts, g C ⊆ C)
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts)
    {ε β : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmass : ∑ p ∈ D, ((p.1.card : ℝ) * p.2.card) ≤ β * (s.card : ℝ) ^ 2)
    (hD01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g A) (g B) ε →
        (A, B) ∈ D)
    (hD02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (g A) (g B) ε →
        (A, B) ∈ D)
    (hD12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts, A ≠ B →
      ¬ IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (g A) (g B) ε →
        (A, B) ∈ D)
    -- a diagonal box may fail uniformity, and `D` still need not contain `(A, A)`
    {A : Finset V} (hA : A ∈ Q.parts) (hdiag : ¬ IsUniformPair
      (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (g A) (g A) ε)
    (hnotmem : (A, A) ∉ D) :
    |(representativeInducedCount P M Q g : ℝ) - representativeInducedEstimate P M Q g|
      ≤ (7 * ε + 3 * β) * (s.card : ℝ) ^ 3 :=
  abs_representativeInducedCount_sub_estimate_le hQ hnull hg hD hε0 hε1 hmass hD01 hD02 hD12

-- The identity box map recovers the partition notions definitionally.
example (Q : Finpartition s) :
    representativeInducedCount P M Q (fun C => C) = transversalInducedCount P M Q :=
  representativeInducedCount_id P M Q

-- The raw count is a natural number, as the type policy requires; the cast appears only in
-- the analytic statement. Stated as an ascription, since an equation would hold at any
-- return type.
example (Q : Finpartition s) (g : Finset V → Finset V) : ℕ :=
  representativeInducedCount P M Q g

-- The crude bound holds on every triple, with no uniformity hypothesis at all — which is
-- what makes it the right estimate for a bad triple.
example (T : Fin 3 → Finset V) :
    |(inducedEmbeddingCountOn P M T : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
            * (T 0).card * (T 1).card * (T 2).card|
      ≤ ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
  abs_count_sub_densityProduct_le_volume T

-- With an empty bad-pair set the estimate degenerates to the pure `7 * ε` bound: `β = 0`
-- contributes nothing, so the two error sources really are separate.
example (hQ : Q ≤ binaryProfilePartition M s) (hnull : NullaryCompatible P M) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu01 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε)
    (hu02 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A B ε)
    (hu12 : ∀ A ∈ Q.parts, ∀ B ∈ Q.parts,
      IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B ε) :
    |(transversalInducedCount P M Q : ℝ) - coarseInducedEstimate P M Q|
      ≤ (7 * ε + 3 * 0) * (s.card : ℝ) ^ 3 :=
  abs_transversalInducedCount_sub_coarseInducedEstimate_le hQ hnull
    (D := ∅) (Finset.empty_subset _) hε0 hε1 (by simp)
    (fun A hA B hB h => absurd (hu01 A hA B hB) h)
    (fun A hA B hB h => absurd (hu02 A hA B hB) h)
    (fun A hA B hB h => absurd (hu12 A hA B hB) h)

end Tests

end RegularityLemmata
