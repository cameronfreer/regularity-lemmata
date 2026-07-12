/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryStrong
import RegularityLemmata.Relational.ThreeVertexCounting

/-!
# Transversal induced-count substrate

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), substrate layer: the definitions and
mass identities for comparing the actual number of induced three-vertex pattern embeddings
whose three images lie in **distinct** coarse cells against the step-model estimate from the
three required coarse palette densities.

`transversalCellTriples Q` enumerates the ordered triples of *distinct* cells of a partition
`Q` (injectivity of `Fin 3 → Q.parts`); partition disjointness then supplies the box
disjointness that the exact three-vertex bridge (`inducedEmbeddingCountOn_three`) needs.
`transversalInducedCount` sums the induced count over these boxes; `coarseInducedEstimate`
is the real-valued step estimate, restricted (via `MatchesThreeProfiles`) to triples whose
cells carry the pattern's required vertex profiles — a cell may have a well-defined palette
density yet the wrong unary/loop profile for a coordinate.

The mass identity `sum_transversal_volume_le` bounds the total box volume by `|s|³`, the
normalization for the error terms in the strong-counting theorem.

The **profile-mismatch vanishing** (`inducedEmbeddingCountOn_eq_zero_of_not_matchesThreeProfiles`)
lets the unfiltered actual count and the profile-filtered estimate share one index set. The
**refinement decomposition** (`inducedEmbeddingCountOn_refinement_three`) rewrites the induced
count over a coarse box as a sum over the fine boxes (`refinementTriples`) refining it — a
disjoint union of `piFinset`s, not bespoke bijections — and `sum_refinement_volume_eq` records
that refining preserves total volume. Together with the coarse-estimate bounds
(`coarseInducedEstimate_nonneg`, `coarseInducedEstimate_le_cube`) and the flat pair-to-triple
lifting (`selectedPairTripleMass_*_le`), these are the exact-rewriting substrate that the
strong-counting theorem (in `Relational/BinaryStrongCounting.lean`) assembles over.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- Ordered triples of **distinct** cells of `Q` (the box disjointness for transversal
induced counting comes from partition disjointness of distinct cells). -/
def transversalCellTriples (Q : Finpartition s) : Finset (Fin 3 → Finset V) :=
  (Fintype.piFinset fun _ => Q.parts).filter Function.Injective

/-- The three cells of a transversal triple carry the pattern's required vertex profiles. -/
def MatchesThreeProfiles (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (T : Fin 3 → Finset V) : Prop :=
  ∀ i, ∀ v ∈ T i, binaryVertexProfile M v = binaryVertexProfile P i

instance (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V) :
    DecidablePred (MatchesThreeProfiles P M) :=
  fun T => inferInstanceAs
    (Decidable (∀ i, ∀ v ∈ T i, binaryVertexProfile M v = binaryVertexProfile P i))

/-- The actual number of induced pattern embeddings whose images lie in distinct cells. -/
def transversalInducedCount (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℕ :=
  ∑ T ∈ transversalCellTriples Q, inducedEmbeddingCountOn P M T

/-- The coarse step-model estimate: the product of the three required palette densities
times the box volume, over profile-matching transversal triples. -/
noncomputable def coarseInducedEstimate (P : FiniteRelModel L (Fin 3)) (M : FiniteRelModel L V)
    (Q : Finpartition s) : ℝ :=
  ∑ T ∈ (transversalCellTriples Q).filter (MatchesThreeProfiles P M),
    pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1) *
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2) *
      pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) *
      (T 0).card * (T 1).card * (T 2).card

/-! ### Elimination lemmas -/

variable {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {Q : Finpartition s}
  {T U : Fin 3 → Finset V} {i j : Fin 3}

theorem mem_transversalCellTriples :
    T ∈ transversalCellTriples Q ↔ (∀ i, T i ∈ Q.parts) ∧ Function.Injective T := by
  rw [transversalCellTriples, Finset.mem_filter, Fintype.mem_piFinset]

theorem transversalCellTriples_cell_mem (hT : T ∈ transversalCellTriples Q) (i : Fin 3) :
    T i ∈ Q.parts :=
  (mem_transversalCellTriples.mp hT).1 i

theorem transversalCellTriples_ne (hT : T ∈ transversalCellTriples Q) (hij : i ≠ j) :
    T i ≠ T j :=
  fun h => hij ((mem_transversalCellTriples.mp hT).2 h)

theorem transversalCellTriples_disjoint (hT : T ∈ transversalCellTriples Q) (hij : i ≠ j) :
    Disjoint (T i) (T j) :=
  Q.disjoint (Finset.mem_coe.mpr (transversalCellTriples_cell_mem hT i))
    (Finset.mem_coe.mpr (transversalCellTriples_cell_mem hT j)) (transversalCellTriples_ne hT hij)

omit [DecidableEq V] in
theorem MatchesThreeProfiles.mono (h : MatchesThreeProfiles P M T) (hsub : ∀ i, U i ⊆ T i) :
    MatchesThreeProfiles P M U :=
  fun i v hv => h i v (hsub i hv)

/-! ### The profile-mismatch vanishing -/

/-- On a partition refining the vertex-profile partition, every cell has constant profile. -/
theorem binaryVertexProfile_eq_of_mem_of_le_profile (hQ : Q ≤ binaryProfilePartition M s)
    {C : Finset V} (hC : C ∈ Q.parts) {x y : V} (hx : x ∈ C) (hy : y ∈ C) :
    binaryVertexProfile M x = binaryVertexProfile M y := by
  obtain ⟨t, ht, hCt⟩ := hQ hC
  exact binaryVertexProfile_eq_of_mem_part M ht (hCt hx) (hCt hy)

/-- A transversal box whose cells refine the vertex-profile partition but do **not** match
the pattern's required profiles contributes zero induced embeddings. -/
theorem inducedEmbeddingCountOn_eq_zero_of_not_matchesThreeProfiles [AtMostBinary L]
    (hQ : Q ≤ binaryProfilePartition M s) (hT : ∀ i, T i ∈ Q.parts)
    (hmatch : ¬ MatchesThreeProfiles P M T) :
    inducedEmbeddingCountOn P M T = 0 := by
  rw [MatchesThreeProfiles] at hmatch
  push Not at hmatch
  obtain ⟨i, v, hv, hne⟩ := hmatch
  refine inducedEmbeddingCountOn_eq_zero_of_profile_mismatch (i := i) fun w hw => ?_
  have hwv : binaryVertexProfile M w = binaryVertexProfile M v :=
    binaryVertexProfile_eq_of_mem_of_le_profile hQ (hT i) hw hv
  exact fun hcontra => hne (hwv.symm.trans hcontra.symm)

/-! ### Refinement decomposition -/

/-- The fine cells of `Q` contained in a cell `C`. -/
def refinementFiber (Q : Finpartition s) (C : Finset V) : Finset (Finset V) :=
  Q.parts.filter (· ⊆ C)

/-- The fine boxes refining a coarse box `T` coordinatewise. -/
def refinementTriples (Q : Finpartition s) (T : Fin 3 → Finset V) : Finset (Fin 3 → Finset V) :=
  Fintype.piFinset fun i => refinementFiber Q (T i)

/-- **Box cover.** A box over coarse cells is the disjoint union of the boxes over the fine
cells refining each coordinate. -/
theorem piFinset_eq_biUnion_refinement {Q Pc : Finpartition s} (hQP : Q ≤ Pc)
    (hT : ∀ i, T i ∈ Pc.parts) :
    Fintype.piFinset T
      = (Fintype.piFinset fun i => refinementFiber Q (T i)).biUnion Fintype.piFinset := by
  ext f
  rw [Fintype.mem_piFinset, Finset.mem_biUnion]
  constructor
  · intro hf
    have hAi : ∀ i, ∃ A ∈ refinementFiber Q (T i), f i ∈ A := by
      intro i
      have hmem : f i ∈ (refinementFiber Q (T i)).biUnion id := by
        rw [refinementFiber, biUnion_filter_subset_eq hQP (hT i)]; exact hf i
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨A, hA, hfA⟩ := hmem
      exact ⟨A, hA, hfA⟩
    choose W hW hfW using hAi
    exact ⟨W, Fintype.mem_piFinset.mpr hW, Fintype.mem_piFinset.mpr hfW⟩
  · rintro ⟨W, hW, hfW⟩
    rw [Fintype.mem_piFinset] at hW hfW
    intro i
    have hWi := hW i
    rw [refinementFiber, Finset.mem_filter] at hWi
    exact hWi.2 (hfW i)

/-- The fine boxes below distinct coordinate-fibers are pairwise disjoint. -/
theorem piFinset_refinement_pairwiseDisjoint {Q : Finpartition s} :
    (↑(Fintype.piFinset fun i => refinementFiber Q (T i)) :
        Set (Fin 3 → Finset V)).PairwiseDisjoint Fintype.piFinset := by
  intro W hW W' hW' hWW'
  rw [Finset.mem_coe, Fintype.mem_piFinset] at hW hW'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro f hfW hfW'
  rw [Fintype.mem_piFinset] at hfW hfW'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hWW'
  have hWi : W i ∈ Q.parts := by
    have := hW i; rw [refinementFiber, Finset.mem_filter] at this; exact this.1
  have hW'i : W' i ∈ Q.parts := by
    have := hW' i; rw [refinementFiber, Finset.mem_filter] at this; exact this.1
  exact Finset.disjoint_left.mp
    (Q.disjoint (Finset.mem_coe.mpr hWi) (Finset.mem_coe.mpr hW'i) hi) (hfW i) (hfW' i)

/-- **Box additivity of induced counts.** No profile matching or transversality is needed. -/
theorem inducedEmbeddingCountOn_refinement_three {Pc : Finpartition s} (hQP : Q ≤ Pc)
    (hT : ∀ i, T i ∈ Pc.parts) :
    inducedEmbeddingCountOn P M T
      = ∑ W ∈ refinementTriples Q T, inducedEmbeddingCountOn P M W := by
  rw [refinementTriples]
  rw [inducedEmbeddingCountOn, piFinset_eq_biUnion_refinement hQP hT, Finset.filter_biUnion,
    Finset.card_biUnion fun W hW W' hW' hWW' =>
      (piFinset_refinement_pairwiseDisjoint (Finset.mem_coe.mpr hW) (Finset.mem_coe.mpr hW') hWW').mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)]
  exact Finset.sum_congr rfl fun u _ => rfl

/-- Fine cells inside distinct coarse cells are distinct — this is what turns failure of
uniformity into an `IsBadPair` (whose definition excludes the diagonal). -/
theorem fine_cells_ne_of_subset_distinct_coarse {Q Pc : Finpartition s} {A B X Y : Finset V}
    (hA : A ∈ Q.parts) (hAX : A ⊆ X) (hBY : B ⊆ Y) (hXY : X ≠ Y)
    (hX : X ∈ Pc.parts) (hY : Y ∈ Pc.parts) :
    A ≠ B := by
  intro hAB
  obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hA
  exact absurd (hBY (hAB ▸ ha))
    (Finset.disjoint_left.mp
      (Pc.disjoint (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hY) hXY) (hAX ha))

/-! ### Mass identities -/

/-- **Total transversal box volume is at most `|s|³`.** -/
theorem sum_transversal_volume_le (Q : Finpartition s) :
    ∑ T ∈ transversalCellTriples Q, ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ (s.card : ℝ) ^ 3 := by
  have hsub : transversalCellTriples Q ⊆ Fintype.piFinset fun _ => Q.parts :=
    Finset.filter_subset _ _
  calc ∑ T ∈ transversalCellTriples Q, ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ Fintype.piFinset fun _ => Q.parts, ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ T ∈ Fintype.piFinset fun _ => Q.parts, ∏ i, ((T i).card : ℝ) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Fin.prod_univ_three]
    _ = ∏ _i : Fin 3, ∑ A ∈ Q.parts, (A.card : ℝ) :=
        Finset.sum_prod_piFinset Q.parts fun _ A => (A.card : ℝ)
    _ = (s.card : ℝ) ^ 3 := by
        rw [sum_card_parts_cast Q, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The fine cells of `Q` contained in a coarse cell partition its cardinality. -/
theorem sum_card_filter_subset_eq {Q Pc : Finpartition s} (hQP : Q ≤ Pc) {C : Finset V}
    (hC : C ∈ Pc.parts) :
    ∑ A ∈ Q.parts.filter (· ⊆ C), (A.card : ℝ) = C.card := by
  have hnat : C.card = ∑ A ∈ Q.parts.filter (· ⊆ C), A.card := by
    conv_lhs => rw [← biUnion_filter_subset_eq hQP hC]
    rw [Finset.card_biUnion fun A hA A' hA' hAA' =>
      Q.disjoint (Finset.mem_coe.mpr (Finset.mem_filter.mp hA).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp hA').1) hAA']
    simp
  rw [hnat, Nat.cast_sum]

/-- **Refinement volume identity.** Refining a box preserves total volume. -/
theorem sum_refinement_volume_eq {Q Pc : Finpartition s} (hQP : Q ≤ Pc)
    (hT : ∀ i, T i ∈ Pc.parts) :
    ∑ W ∈ refinementTriples Q T, ((W 0).card * (W 1).card * (W 2).card : ℝ)
      = (T 0).card * (T 1).card * (T 2).card := by
  rw [refinementTriples]
  calc ∑ W ∈ Fintype.piFinset (fun i => refinementFiber Q (T i)),
          ((W 0).card * (W 1).card * (W 2).card : ℝ)
      = ∑ W ∈ Fintype.piFinset (fun i => refinementFiber Q (T i)), ∏ i, ((W i).card : ℝ) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [Fin.prod_univ_three]
    _ = ∏ i, ∑ A ∈ refinementFiber Q (T i), (A.card : ℝ) :=
        (Finset.prod_univ_sum (fun i => refinementFiber Q (T i)) fun _ A => (A.card : ℝ)).symm
    _ = ∏ i, ((T i).card : ℝ) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [refinementFiber]; exact sum_card_filter_subset_eq hQP (hT i)
    _ = (T 0).card * (T 1).card * (T 2).card := by rw [Fin.prod_univ_three]

/-! ### Bounds on the coarse estimate -/

theorem coarseInducedEstimate_nonneg (Q : Finpartition s) : 0 ≤ coarseInducedEstimate P M Q := by
  rw [coarseInducedEstimate]
  refine Finset.sum_nonneg fun T _ => ?_
  have h1 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 0 1))
    (A := T 0) (B := T 1)
  have h2 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 0 2))
    (A := T 0) (B := T 2)
  have h3 := pairDensity_nonneg (R := HasBinaryPairPalette M (binaryPairPalette P 1 2))
    (A := T 1) (B := T 2)
  positivity

theorem coarseInducedEstimate_le_cube (Q : Finpartition s) :
    coarseInducedEstimate P M Q ≤ (s.card : ℝ) ^ 3 := by
  rw [coarseInducedEstimate]
  refine le_trans (Finset.sum_le_sum fun T _ => ?_)
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun T _ _ => by positivity) (sum_transversal_volume_le Q))
  have hd : pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
      * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ pairDensity_le_one pairDensity_nonneg pairDensity_le_one)
      pairDensity_nonneg pairDensity_le_one
  have hv : (0 : ℝ) ≤ (T 0).card * (T 1).card * (T 2).card := by positivity
  calc pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
        * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2)
        * (T 0).card * (T 1).card * (T 2).card
      = (pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) (T 0) (T 1)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) (T 0) (T 2)
          * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) (T 1) (T 2))
          * ((T 0).card * (T 1).card * (T 2).card) := by ring
    _ ≤ 1 * ((T 0).card * (T 1).card * (T 2).card) := mul_le_mul_of_nonneg_right hd hv
    _ = (T 0).card * (T 1).card * (T 2).card := by ring

/-! ### Pair-to-triple lifting -/

/-- **Lift a selected `(0,1)`-pair family to transversal triples.** The mass of transversal
triples whose first two cells lie in `D` is at most the `D`-pair mass times `|s|` (the third
coordinate ranges over all cells). -/
theorem selectedPairTripleMass_zero_one_le {Q : Finpartition s}
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts) :
    ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 0, T 1) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * s.card := by
  have hle : ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 0, T 1) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 0, T 1) ∈ D),
          ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _)) fun T _ _ => by positivity
  refine le_trans hle ?_
  have hreindex : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 0, T 1) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ q ∈ D ×ˢ Q.parts, ((q.1.1.card : ℝ) * q.1.2.card * q.2.card) := by
    refine Finset.sum_nbij' (fun T => ((T 0, T 1), T 2)) (fun q => ![q.1.1, q.1.2, q.2])
      (fun T hT => ?_) (fun q hq => ?_) (fun T _ => ?_) (fun q _ => ?_) (fun T _ => rfl)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.2, hT.1 2⟩
    · rw [Finset.mem_product] at hq
      have hq1 := Finset.mem_product.mp (hD hq.1)
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, hq.1⟩
      fin_cases i
      · exact hq1.1
      · exact hq1.2
      · exact hq.2
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hreindex, Finset.sum_product, Finset.sum_mul]
  refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
  dsimp only
  rw [← Finset.mul_sum, sum_card_parts_cast]

/-- **Lift a selected `(0,2)`-pair family to transversal triples.** -/
theorem selectedPairTripleMass_zero_two_le {Q : Finpartition s}
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts) :
    ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 0, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * s.card := by
  have hle : ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 0, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 0, T 2) ∈ D),
          ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _)) fun T _ _ => by positivity
  refine le_trans hle ?_
  have hreindex : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 0, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ q ∈ D ×ˢ Q.parts, ((q.1.1.card : ℝ) * q.1.2.card * q.2.card) := by
    refine Finset.sum_nbij' (fun T => ((T 0, T 2), T 1)) (fun q => ![q.1.1, q.2, q.1.2])
      (fun T hT => ?_) (fun q hq => ?_) (fun T _ => ?_) (fun q _ => ?_) (fun T _ => by ring)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.2, hT.1 1⟩
    · rw [Finset.mem_product] at hq
      have hq1 := Finset.mem_product.mp (hD hq.1)
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, hq.1⟩
      fin_cases i
      · exact hq1.1
      · exact hq.2
      · exact hq1.2
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hreindex, Finset.sum_product, Finset.sum_mul]
  refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
  dsimp only
  rw [← Finset.mul_sum, sum_card_parts_cast]

/-- **Lift a selected `(1,2)`-pair family to transversal triples.** -/
theorem selectedPairTripleMass_one_two_le {Q : Finpartition s}
    {D : Finset (Finset V × Finset V)} (hD : D ⊆ Q.parts ×ˢ Q.parts) :
    ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ (∑ p ∈ D, (p.1.card : ℝ) * p.2.card) * s.card := by
  have hle : ∑ T ∈ (transversalCellTriples Q).filter (fun T => (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      ≤ ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 1, T 2) ∈ D),
          ((T 0).card * (T 1).card * (T 2).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _)) fun T _ _ => by positivity
  refine le_trans hle ?_
  have hreindex : ∑ T ∈ (Fintype.piFinset fun _ : Fin 3 => Q.parts).filter (fun T => (T 1, T 2) ∈ D),
        ((T 0).card * (T 1).card * (T 2).card : ℝ)
      = ∑ q ∈ D ×ˢ Q.parts, ((q.1.1.card : ℝ) * q.1.2.card * q.2.card) := by
    refine Finset.sum_nbij' (fun T => ((T 1, T 2), T 0)) (fun q => ![q.2, q.1.1, q.1.2])
      (fun T hT => ?_) (fun q hq => ?_) (fun T _ => ?_) (fun q _ => ?_) (fun T _ => by ring)
    · rw [Finset.mem_filter, Fintype.mem_piFinset] at hT
      exact Finset.mem_product.mpr ⟨hT.2, hT.1 0⟩
    · rw [Finset.mem_product] at hq
      have hq1 := Finset.mem_product.mp (hD hq.1)
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, hq.1⟩
      fin_cases i
      · exact hq.2
      · exact hq1.1
      · exact hq1.2
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hreindex, Finset.sum_product, Finset.sum_mul]
  refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
  dsimp only
  rw [← Finset.mul_sum, sum_card_parts_cast]

/-! ### Tests and adversarial examples -/

section Tests

/-- The unique model of the empty language (no relations to interpret). -/
private def emptyModel (V : Type*) : FiniteRelModel FirstOrder.Language.empty V :=
  ⟨fun {_} R _ => R.elim⟩

-- **Genuinely numeric decomposition.** Over the full `Fin 3` box in the empty language, the
-- coarse induced count (the `3! = 6` injective self-maps) equals the sum over its singleton
-- refinement boxes — both `6`.
example :
    inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3))
        ![Finset.univ, Finset.univ, Finset.univ] = 6
      ∧ ∑ W ∈ refinementTriples (⊥ : Finpartition (Finset.univ : Finset (Fin 3)))
            ![Finset.univ, Finset.univ, Finset.univ],
          inducedEmbeddingCountOn (emptyModel (Fin 3)) (emptyModel (Fin 3)) W = 6 := by
  decide

-- Empty host: no cells, so the transversal triples are empty and both counts vanish.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3))
    (M : FiniteRelModel (singleRelLang 2) (Fin 2)) :
    transversalInducedCount P M (⊥ : Finpartition (∅ : Finset (Fin 2))) = 0
      ∧ coarseInducedEstimate P M (⊥ : Finpartition (∅ : Finset (Fin 2))) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [transversalInducedCount, transversalCellTriples]; simp
  · rw [coarseInducedEstimate, transversalCellTriples]; simp

-- A partition into three singleton cells has exactly `3! = 6` ordered transversal triples.
example : (transversalCellTriples (⊥ : Finpartition (Finset.univ : Finset (Fin 3)))).card = 6 := by
  decide

-- The refinement decomposition, as a statement-level instance.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) (M : FiniteRelModel (singleRelLang 2) (Fin 4))
    {Q Pc : Finpartition (Finset.univ : Finset (Fin 4))} (hQP : Q ≤ Pc)
    {T : Fin 3 → Finset (Fin 4)} (hT : ∀ i, T i ∈ Pc.parts) :
    inducedEmbeddingCountOn P M T = ∑ W ∈ refinementTriples Q T, inducedEmbeddingCountOn P M W :=
  inducedEmbeddingCountOn_refinement_three hQP hT

end Tests

end RegularityLemmata
