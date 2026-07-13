/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.TransversalCounting

/-!
# Nested selected-pair lifting

Phase 10 unit 7 (design freeze in `ARCHITECTURE.md`), lifting layer: charging fine
coordinate-pairs selected by a coarse/fine predicate through partition refinements, so the
strong-counting theorem (`Relational/BinaryStrongCounting.lean`) can bound its nonuniform and
density-deviant contributions.

`selectedFinePairs Q Pc sel` flattens, over each coarse pair, the fine pairs its selection
`sel` keeps; `sum_selectedFinePairs_mass` reindexes their mass to match the nesting of
`BinaryPaletteStrongWitness.deviant_mass_le`. The nested wrappers
`selectedRefinementPairTripleMass_*_le` lift the flat pair-to-triple bounds of
`Relational/TransversalCounting.lean` to sums over coarse-transversal triples and their fine
refinements (embedding into fine transversal triples, whose refinement families are pairwise
disjoint), reusing the flat lemmas rather than three independent coordinate arguments.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### Selected fine pairs relative to their coarse parents -/

/-- The fine pairs selected by `sel` on the coarse pair they refine. -/
def selectedFinePairs (Q Pc : Finpartition s)
    (sel : (Finset V × Finset V) → (Finset V × Finset V) → Prop) [DecidableRel sel] :
    Finset (Finset V × Finset V) :=
  (Pc.parts ×ˢ Pc.parts).biUnion fun pd =>
    (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd)

variable {Q Pc : Finpartition s}
  {sel : (Finset V × Finset V) → (Finset V × Finset V) → Prop} [DecidableRel sel]

theorem selectedFinePairs_subset : selectedFinePairs Q Pc sel ⊆ Q.parts ×ˢ Q.parts := by
  intro p hp
  rw [selectedFinePairs, Finset.mem_biUnion] at hp
  obtain ⟨pd, _, hp⟩ := hp
  rw [Finset.mem_filter, Finset.mem_product] at hp
  exact Finset.mem_product.mpr
    ⟨Finset.filter_subset _ _ hp.1.1, Finset.filter_subset _ _ hp.1.2⟩

/-- A fine cell has a unique coarse parent. -/
private theorem coarse_parent_eq {A X X' : Finset V} (hAne : A.Nonempty)
    (hAX : A ⊆ X) (hAX' : A ⊆ X') (hX : X ∈ Pc.parts) (hX' : X' ∈ Pc.parts) : X = X' := by
  by_contra hne
  obtain ⟨a, ha⟩ := hAne
  exact Finset.disjoint_left.mp
    (Pc.disjoint (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hX') hne) (hAX ha) (hAX' ha)

/-- The coarse-pair fibers are pairwise disjoint (unique coarse parent). -/
theorem pairwiseDisjoint_refinementPairFibers :
    (↑(Pc.parts ×ˢ Pc.parts) : Set (Finset V × Finset V)).PairwiseDisjoint
      fun pd => (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd) := by
  intro pd hpd pd' hpd' hne
  rw [Finset.mem_coe, Finset.mem_product] at hpd hpd'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [Finset.mem_filter, Finset.mem_product] at hp hp'
  have h1 := Finset.mem_filter.mp hp.1.1
  have h1' := Finset.mem_filter.mp hp'.1.1
  have h2 := Finset.mem_filter.mp hp.1.2
  have h2' := Finset.mem_filter.mp hp'.1.2
  exact hne (Prod.ext (coarse_parent_eq (Q.nonempty_of_mem_parts h1.1) h1.2 h1'.2 hpd.1 hpd'.1)
    (coarse_parent_eq (Q.nonempty_of_mem_parts h2.1) h2.2 h2'.2 hpd.2 hpd'.2))

/-- **Selected-pair mass reindex**, matching the nesting of `deviant_mass_le`. -/
theorem sum_selectedFinePairs_mass :
    ∑ p ∈ selectedFinePairs Q Pc sel, ((p.1.card : ℝ) * p.2.card)
      = ∑ pd ∈ Pc.parts ×ˢ Pc.parts,
          ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd),
            ((p.1.card : ℝ) * p.2.card) := by
  rw [selectedFinePairs, Finset.sum_biUnion pairwiseDisjoint_refinementPairFibers]

/-- A refinement of a transversal box selects a fine pair iff the coarse pair is selected. -/
theorem mem_selectedFinePairs_of_refines {T W : Fin 3 → Finset V} {i j : Fin 3}
    (hT : T ∈ transversalCellTriples Pc) (hW : W ∈ refinementTriples Q T) :
    (W i, W j) ∈ selectedFinePairs Q Pc sel ↔ sel (T i, T j) (W i, W j) := by
  rw [refinementTriples, Fintype.mem_piFinset] at hW
  have hWi := hW i
  have hWj := hW j
  rw [refinementFiber, Finset.mem_filter] at hWi hWj
  have hTi := transversalCellTriples_cell_mem hT i
  have hTj := transversalCellTriples_cell_mem hT j
  constructor
  · intro hmem
    rw [selectedFinePairs, Finset.mem_biUnion] at hmem
    obtain ⟨pd, hpd, hmem⟩ := hmem
    rw [Finset.mem_filter, Finset.mem_product] at hmem
    rw [Finset.mem_product] at hpd
    have hpd1 := Finset.mem_filter.mp hmem.1.1
    have hpd2 := Finset.mem_filter.mp hmem.1.2
    have e1 : T i = pd.1 := coarse_parent_eq (Q.nonempty_of_mem_parts hWi.1) hWi.2 hpd1.2 hTi hpd.1
    have e2 : T j = pd.2 := coarse_parent_eq (Q.nonempty_of_mem_parts hWj.1) hWj.2 hpd2.2 hTj hpd.2
    rw [e1, e2]
    exact hmem.2
  · intro hsel
    rw [selectedFinePairs, Finset.mem_biUnion]
    exact ⟨(T i, T j), Finset.mem_product.mpr ⟨hTi, hTj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hW i, hW j⟩, hsel⟩⟩

/-! ### Embedding refinements into fine transversal triples -/

/-- The refinement boxes of a transversal coarse triple are themselves transversal. -/
theorem refinementTriples_subset_transversal {T : Fin 3 → Finset V}
    (hT : T ∈ transversalCellTriples Pc) : refinementTriples Q T ⊆ transversalCellTriples Q := by
  intro W hW
  rw [refinementTriples, Fintype.mem_piFinset] at hW
  rw [mem_transversalCellTriples]
  refine ⟨fun i => Finset.filter_subset _ _ (hW i), fun {i j} h => ?_⟩
  by_contra hij
  have hWi := hW i
  have hWj := hW j
  rw [refinementFiber, Finset.mem_filter] at hWi hWj
  exact fine_cells_ne_of_subset_distinct_coarse hWi.1 hWi.2 hWj.2
    (transversalCellTriples_ne hT hij) (transversalCellTriples_cell_mem hT i)
    (transversalCellTriples_cell_mem hT j) h

/-- Distinct transversal coarse triples have disjoint refinement families. -/
theorem pairwiseDisjoint_refinementTriples :
    (↑(transversalCellTriples Pc) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      (refinementTriples Q) := by
  intro T hT T' hT' hne
  rw [Finset.mem_coe] at hT hT'
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro W hW hW'
  rw [refinementTriples, Fintype.mem_piFinset] at hW hW'
  refine hne (funext fun i => ?_)
  have hWi := hW i
  have hW'i := hW' i
  rw [refinementFiber, Finset.mem_filter] at hWi hW'i
  exact coarse_parent_eq (Q.nonempty_of_mem_parts hWi.1) hWi.2 hW'i.2
    (transversalCellTriples_cell_mem hT i) (transversalCellTriples_cell_mem hT' i)

/-! ### Nested lifting wrappers -/

/-- **Nested `(0,1)` lifting.** -/
theorem selectedRefinementPairTripleMass_zero_one_le :
    ∑ T ∈ transversalCellTriples Pc,
        ∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 0, T 1) (W 0, W 1)),
          ((W 0).card * (W 1).card * (W 2).card : ℝ)
      ≤ (∑ pd ∈ Pc.parts ×ˢ Pc.parts,
          ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd),
            ((p.1.card : ℝ) * p.2.card)) * s.card := by
  rw [← sum_selectedFinePairs_mass]
  have hfc : ∀ T ∈ transversalCellTriples Pc,
      (∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 0, T 1) (W 0, W 1)),
        ((W 0).card * (W 1).card * (W 2).card : ℝ))
      = ∑ W ∈ (refinementTriples Q T).filter
          (fun W => (W 0, W 1) ∈ selectedFinePairs Q Pc sel),
        ((W 0).card * (W 1).card * (W 2).card : ℝ) := fun T hT =>
    Finset.sum_congr
      (Finset.filter_congr fun W hW => (mem_selectedFinePairs_of_refines hT hW).symm) fun _ _ => rfl
  have hdisj : (↑(transversalCellTriples Pc) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      fun T => (refinementTriples Q T).filter
        (fun W => (W 0, W 1) ∈ selectedFinePairs Q Pc sel) := fun T hT T' hT' hne =>
    (pairwiseDisjoint_refinementTriples hT hT' hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  refine le_trans ?_ (selectedPairTripleMass_zero_one_le selectedFinePairs_subset)
  rw [Finset.sum_congr rfl hfc, ← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro W hW
    rw [Finset.mem_biUnion] at hW
    obtain ⟨T, hT, hWmem⟩ := hW
    rw [Finset.mem_filter] at hWmem ⊢
    exact ⟨refinementTriples_subset_transversal hT hWmem.1, hWmem.2⟩
  · intro W _ _; positivity

/-- **Nested `(0,2)` lifting.** -/
theorem selectedRefinementPairTripleMass_zero_two_le :
    ∑ T ∈ transversalCellTriples Pc,
        ∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 0, T 2) (W 0, W 2)),
          ((W 0).card * (W 1).card * (W 2).card : ℝ)
      ≤ (∑ pd ∈ Pc.parts ×ˢ Pc.parts,
          ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd),
            ((p.1.card : ℝ) * p.2.card)) * s.card := by
  rw [← sum_selectedFinePairs_mass]
  have hfc : ∀ T ∈ transversalCellTriples Pc,
      (∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 0, T 2) (W 0, W 2)),
        ((W 0).card * (W 1).card * (W 2).card : ℝ))
      = ∑ W ∈ (refinementTriples Q T).filter
          (fun W => (W 0, W 2) ∈ selectedFinePairs Q Pc sel),
        ((W 0).card * (W 1).card * (W 2).card : ℝ) := fun T hT =>
    Finset.sum_congr
      (Finset.filter_congr fun W hW => (mem_selectedFinePairs_of_refines hT hW).symm) fun _ _ => rfl
  have hdisj : (↑(transversalCellTriples Pc) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      fun T => (refinementTriples Q T).filter
        (fun W => (W 0, W 2) ∈ selectedFinePairs Q Pc sel) := fun T hT T' hT' hne =>
    (pairwiseDisjoint_refinementTriples hT hT' hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  refine le_trans ?_ (selectedPairTripleMass_zero_two_le selectedFinePairs_subset)
  rw [Finset.sum_congr rfl hfc, ← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro W hW
    rw [Finset.mem_biUnion] at hW
    obtain ⟨T, hT, hWmem⟩ := hW
    rw [Finset.mem_filter] at hWmem ⊢
    exact ⟨refinementTriples_subset_transversal hT hWmem.1, hWmem.2⟩
  · intro W _ _; positivity

/-- **Nested `(1,2)` lifting.** -/
theorem selectedRefinementPairTripleMass_one_two_le :
    ∑ T ∈ transversalCellTriples Pc,
        ∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 1, T 2) (W 1, W 2)),
          ((W 0).card * (W 1).card * (W 2).card : ℝ)
      ≤ (∑ pd ∈ Pc.parts ×ˢ Pc.parts,
          ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd),
            ((p.1.card : ℝ) * p.2.card)) * s.card := by
  rw [← sum_selectedFinePairs_mass]
  have hfc : ∀ T ∈ transversalCellTriples Pc,
      (∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 1, T 2) (W 1, W 2)),
        ((W 0).card * (W 1).card * (W 2).card : ℝ))
      = ∑ W ∈ (refinementTriples Q T).filter
          (fun W => (W 1, W 2) ∈ selectedFinePairs Q Pc sel),
        ((W 0).card * (W 1).card * (W 2).card : ℝ) := fun T hT =>
    Finset.sum_congr
      (Finset.filter_congr fun W hW => (mem_selectedFinePairs_of_refines hT hW).symm) fun _ _ => rfl
  have hdisj : (↑(transversalCellTriples Pc) : Set (Fin 3 → Finset V)).PairwiseDisjoint
      fun T => (refinementTriples Q T).filter
        (fun W => (W 1, W 2) ∈ selectedFinePairs Q Pc sel) := fun T hT T' hT' hne =>
    (pairwiseDisjoint_refinementTriples hT hT' hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  refine le_trans ?_ (selectedPairTripleMass_one_two_le selectedFinePairs_subset)
  rw [Finset.sum_congr rfl hfc, ← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro W hW
    rw [Finset.mem_biUnion] at hW
    obtain ⟨T, hT, hWmem⟩ := hW
    rw [Finset.mem_filter] at hWmem ⊢
    exact ⟨refinementTriples_subset_transversal hT hWmem.1, hWmem.2⟩
  · intro W _ _; positivity

/-! ### Tests and adversarial examples -/

section Tests

-- Concrete `selectedFinePairs`: over the discrete partition of `Fin 3`, keeping every fine
-- pair gives the `3·3 = 9` ordered pairs of singletons.
example : (selectedFinePairs (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) ⊥
    (fun _ _ => True)).card = 9 := by decide

-- The nested `(0,1)` lifting wrapper, as a statement-level instance.
example {Q Pc : Finpartition s}
    {sel : (Finset V × Finset V) → (Finset V × Finset V) → Prop} [DecidableRel sel] :
    ∑ T ∈ transversalCellTriples Pc,
        ∑ W ∈ (refinementTriples Q T).filter (fun W => sel (T 0, T 1) (W 0, W 1)),
          ((W 0).card * (W 1).card * (W 2).card : ℝ)
      ≤ (∑ pd ∈ Pc.parts ×ˢ Pc.parts,
          ∑ p ∈ (refinementFiber Q pd.1 ×ˢ refinementFiber Q pd.2).filter (sel pd),
            ((p.1.card : ℝ) * p.2.card)) * s.card :=
  selectedRefinementPairTripleMass_zero_one_le

-- **`¬ IsUniformPair` is not interchangeable with `IsBadPair` on the diagonal.** The
-- diagonal pair `({0,1}, {0,1})` fails `1/4`-uniformity (the subblocks `{0}` and `{1}`
-- deviate by `1/2`) yet is *not* an `IsBadPair` (whose definition excludes diagonals). This
-- is exactly why the regularity charge must select `IsBadPair`, not bare failure of
-- uniformity, to stay under `badMassNum`.
example :
    ¬ IsUniformPair (fun a b : Fin 2 => a = b) {0, 1} {0, 1} (1 / 4)
      ∧ ¬ IsBadPair (fun a b : Fin 2 => a = b) (1 / 4) {0, 1} {0, 1} := by
  refine ⟨fun h => ?_, fun hbad => hbad.1 rfl⟩
  have hd1 : pairDensity (fun a b : Fin 2 => a = b) {0} {1} = 0 := by
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 2 => a = b) {0} {1} = 0 from by decide]; simp
  have hd2 : pairDensity (fun a b : Fin 2 => a = b) {0, 1} {0, 1} = 1 / 2 := by
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 2 => a = b) {0, 1} {0, 1} = 2 from by decide,
      show ({0, 1} : Finset (Fin 2)).card = 2 from by decide]
    norm_num
  have hdev := h (show ({0} : Finset (Fin 2)) ⊆ {0, 1} by decide)
    (show ({1} : Finset (Fin 2)) ⊆ {0, 1} by decide)
    (by rw [show ({0, 1} : Finset (Fin 2)).card = 2 from by decide,
      show ({0} : Finset (Fin 2)).card = 1 from by decide]; norm_num)
    (by rw [show ({0, 1} : Finset (Fin 2)).card = 2 from by decide,
      show ({1} : Finset (Fin 2)).card = 1 from by decide]; norm_num)
  rw [hd1, hd2, abs_le] at hdev
  linarith [hdev.1]

end Tests

end RegularityLemmata
