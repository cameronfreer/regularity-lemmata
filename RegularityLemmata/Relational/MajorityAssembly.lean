/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.ProductHybrid
import RegularityLemmata.Finite.Tuple
import RegularityLemmata.Relational.CellwiseEdit
import RegularityLemmata.Relational.Edit

/-!
# Majority rounding from summed coordinate defects

The global edit cost of the cellwise majority rounding `FiniteRelModel.majorityRound M P`, for a
symbol of arity `n + 1`, bounded by section defects of the **ambient** host, reassembled across
cell boxes by the tuple-to-part map.

* Box level (`editDistance_majorityRound_eq_minorityCount`): on any cell box `∏ Cᵢ` with
  `Cᵢ ∈ P.parts`, the edit distance to the majority value is exactly the minority count of the
  box, a division-free `ℕ` identity derived from the existing real-valued form
  `editDistance_majorityRound_eq_min` (which is kept as stated).
* Reassembly (`partResampleDefect`, `sum_coordDisagreement_div_eq_sum_partResampleDefect`): the
  coordinate defect of a box, normalized by the size of its `j`-th factor, is the sum over the
  box's tuples of the *part-resampling defect* at coordinate `j`: the fraction of replacements of
  `w j` inside its own part `P.part (w j)` that flip the relation. Summing the box quantities over
  all cell boxes therefore gives a sum over the ambient tuples of `s^(n+1)`, with no cellwise
  claim about any individual box.
* Global majority bound (`editDistance_majorityRound_le_sum_partResampleDefect`): the edit
  distance of the rounding on `s^(n+1)` is at most `∑ⱼ ∑_{w ∈ s^(n+1)} partResampleDefect j w`.
* Labelled fibres (`labelPartition`, `labelFibre`): a labelling `lab : V → Λ` of the host
  induces the finpartition of `s` into its nonempty fibres (mathlib's
  `Finpartition.ofSetSetoid` on the kernel setoid, so no parallel partition structure). Labels
  with an empty fibre are simply unused; the reassembly over **label tuples**
  (`sum_piFinset_const_eq_sum_labelBoxes`) and the labelled form of the global bound
  (`editDistance_majorityRound_labelPartition_le`) range over all label tuples, boxes with an
  unused label being empty.
* Decency (`sum_partResampleDefect_le`, `editDistance_majorityRound_le`): if a set `E` of
  exceptional parts has total size at most `λ·|s|`, and for every ordinary part `l` and coordinate
  `j` at most a `γ`-fraction of the ambient off-tuples `rest ∈ s^n` have an inclusively `θ`-mixed
  section `a ↦ R (insertNth j a rest)` on `l`, then the edit distance is at most
  `(n + 1) · |s|^(n+1) · (2θ + γ/2 + λ/2)`. Nullary symbols are copied exactly
  (`editDistance_majorityRound_nullary`).

The decency hypothesis is stated on the ambient off-tuples `s^n`, so it needs no cell-box
bookkeeping from the consumer. Requiring the same mixedness fraction inside every off-coordinate
cell box would imply the ambient hypothesis by summation, not conversely. The composition with a
displacement of the partition itself is not part of this file.

The product substrate (`prefixHybrid`, `coordDisagreement`, `minorityCount`, the normalized
resampling bound) is `Finite/ProductHybrid.lean`, used here with the constant coordinate family;
the split of a box sum at one coordinate is `sum_piFinset_succAbove` in `Finite/Tuple.lean`.
-/

namespace RegularityLemmata

open Finset

variable {V : Type*} [DecidableEq V] {s : Finset V}

section BoxSum

/-- Summing over the tuples of `s^m` is summing over the cell boxes of a partition `P` of `s`
and then over each box: the constant-partition specialization of `biUnion_boxCells_tuples`. -/
theorem sum_const_eq_sum_cellBoxes {m : ℕ} (P : Finpartition s) (f : (Fin m → V) → ℝ) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin m ↦ s), f w
      = ∑ C ∈ Fintype.piFinset (fun _ : Fin m ↦ P.parts), ∑ w ∈ Fintype.piFinset C, f w := by
  classical
  rw [show Fintype.piFinset (fun _ : Fin m ↦ s)
      = (Fintype.piFinset fun _ : Fin m ↦ P.parts).biUnion Fintype.piFinset from
      (biUnion_boxCells_tuples (A := fun _ : Fin m ↦ s) fun _ ↦ P).symm,
    Finset.sum_biUnion]
  intro C hC D hD hCD
  exact boxCells_pairwiseDisjoint (A := fun _ : Fin m ↦ s) (fun _ ↦ P)
    (Finset.mem_coe.mpr hC) (Finset.mem_coe.mpr hD) hCD

end BoxSum

section Resample

variable {n : ℕ} (R : (Fin (n + 1) → V) → Prop) [DecidablePred R] (P : Finpartition s)

/-- The part-resampling defect of coordinate `j` at the tuple `w`: the fraction of replacements
`a ∈ P.part (w j)` of the `j`-th coordinate, inside its own part, on which `R` flips. `0` when
`w j ∉ s` (the part is then empty). -/
noncomputable def partResampleDefect (j : Fin (n + 1)) (w : Fin (n + 1) → V) : ℝ :=
  (((P.part (w j)).filter fun a ↦ ¬ (R w ↔ R (Function.update w j a))).card : ℝ)
    / (P.part (w j)).card

omit [DecidableEq V] in
/-- The coordinate defect of a box, counted tuple by tuple. -/
theorem coordDisagreement_eq_sum_box (A : Fin (n + 1) → Finset V) (j : Fin (n + 1)) :
    coordDisagreement R A j
      = ∑ w ∈ Fintype.piFinset A,
          ((A j).filter fun a ↦ ¬ (R w ↔ R (Function.update w j a))).card := by
  unfold coordDisagreement
  rw [Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

/-- **Reassembly.** Summing the normalized coordinate defects of all cell boxes of `P` gives the
sum of the part-resampling defects over the ambient tuples of `s^(n+1)`. -/
theorem sum_coordDisagreement_div_eq_sum_partResampleDefect :
    ∑ C ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ P.parts),
        ∑ j : Fin (n + 1), (coordDisagreement R C j : ℝ) / (C j).card
      = ∑ j : Fin (n + 1), ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s),
          partResampleDefect R P j w := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sum_const_eq_sum_cellBoxes P]
  refine Finset.sum_congr rfl fun C hC ↦ ?_
  have hC' : ∀ i, C i ∈ P.parts := Fintype.mem_piFinset.mp hC
  rw [coordDisagreement_eq_sum_box]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  unfold partResampleDefect
  rw [P.part_eq_of_mem (hC' j) (Fintype.mem_piFinset.mp hw j)]

end Resample

section Majority

variable {L : FirstOrder.Language} [FiniteRelational L]

/-- **Box level.** On a cell box of `P`, the edit distance from `M` to its majority rounding is
exactly the minority count of the box: the `ℕ` form of `editDistance_majorityRound_eq_min`. -/
theorem editDistance_majorityRound_eq_minorityCount (M : FiniteRelModel L V) (P : Finpartition s)
    {m : ℕ} (S : L.Relations m) (C : Fin m → Finset V) (hC : ∀ i, C i ∈ P.parts) :
    editDistance (M.Holds S) ((M.majorityRound P).Holds S) C = minorityCount (M.Holds S) C := by
  classical
  have hreal : (editDistance (M.Holds S) ((M.majorityRound P).Holds S) C : ℝ)
      = min (tupleDensity (M.Holds S) C) (1 - tupleDensity (M.Holds S) C)
          * ∏ i, ((C i).card : ℝ) :=
    editDistance_majorityRound_eq_min M P S fun i ↦ ⟨C i, hC i⟩
  have hbox : (0 : ℝ) < ∏ i, ((C i).card : ℝ) :=
    Finset.prod_pos fun i _ ↦ by exact_mod_cast (P.nonempty_of_mem_parts (hC i)).card_pos
  have hn : ((Fintype.piFinset C).card : ℝ) = ∏ i, ((C i).card : ℝ) := by
    rw [Fintype.card_piFinset]; push_cast; rfl
  have hc : tupleCount (M.Holds S) C ≤ (Fintype.piFinset C).card :=
    tupleCount_le_card (R := M.Holds S) (A := C)
  have key : (editDistance (M.Holds S) ((M.majorityRound P).Holds S) C : ℝ)
      = (minorityCount (M.Holds S) C : ℝ) := by
    rw [hreal, minorityCount_eq_min_tupleCount, Nat.cast_min, Nat.cast_sub hc]
    unfold tupleDensity densityOn tupleCount
    rw [hn, min_mul_of_nonneg _ _ hbox.le, div_mul_cancel₀ _ hbox.ne', sub_mul, one_mul,
      div_mul_cancel₀ _ hbox.ne']
  exact_mod_cast key

/-- **Global majority bound.** The edit distance of the majority rounding on `s^(n+1)` is at
most the sum, over coordinates `j` and ambient tuples `w`, of the part-resampling defects. -/
theorem editDistance_majorityRound_le_sum_partResampleDefect (M : FiniteRelModel L V)
    (P : Finpartition s) {n : ℕ} (S : L.Relations (n + 1)) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
      ≤ ∑ j : Fin (n + 1), ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s),
          partResampleDefect (M.Holds S) P j w := by
  classical
  rw [editDistance_const_eq_sum_cellBoxes, ← sum_coordDisagreement_div_eq_sum_partResampleDefect]
  push_cast
  refine Finset.sum_le_sum fun C hC ↦ ?_
  have hC' : ∀ i, C i ∈ P.parts := Fintype.mem_piFinset.mp hC
  rw [editDistance_majorityRound_eq_minorityCount M P S C hC']
  exact minorityCount_le_sum_coordDisagreement_div (M.Holds S) C

/-- Nullary symbols are copied exactly by the majority rounding. -/
theorem editDistance_majorityRound_nullary (M : FiniteRelModel L V) (P : Finpartition s)
    (S : L.Relations 0) :
    editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 0 ↦ s) = 0 :=
  editDistance_const_eq_zero_of_nullaryCompatible (nullaryCompatible_majorityRound M P) s rfl S

end Majority

section Decency

variable {n : ℕ} (R : (Fin (n + 1) → V) → Prop) [DecidablePred R] (P : Finpartition s)

/-- The part-resampling defects of a whole row `b ↦ insertNth j b rest`, `b` ranging over a part
`l`, sum to the section disagreement of `a ↦ R (insertNth j a rest)` on `l`, divided by `|l|`. -/
theorem sum_partResampleDefect_row (j : Fin (n + 1)) (rest : Fin n → V) {l : Finset V}
    (hl : l ∈ P.parts) :
    ∑ b ∈ l, partResampleDefect R P j (Fin.insertNth j b rest)
      = (sectionDisagreement l fun a ↦ R (Fin.insertNth j a rest) : ℝ) / l.card := by
  rw [sectionDisagreement_eq_sum]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  unfold partResampleDefect
  rw [Fin.insertNth_apply_same, P.part_eq_of_mem hl hb]
  congr 3
  ext a
  simp only [Finset.mem_filter, Fin.update_insertNth]

/-- **Decency ⇒ summed resampling defect.** With exceptional parts `E ⊆ P.parts` of total size at
most `λ·|s|`, and at most a `γ`-fraction of the ambient off-tuples inclusively `θ`-mixed on each
ordinary part, the part-resampling defects at coordinate `j` sum to at most
`|s|^(n+1) · (2θ + γ/2 + λ/2)`. -/
theorem sum_partResampleDefect_le (j : Fin (n + 1)) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ l ∈ P.parts, l ∉ E →
      (((Fintype.piFinset (fun _ : Fin n ↦ s)).filter fun rest ↦
          InclusiveMixed θ (densityOn l fun a ↦ R (Fin.insertNth j a rest))).card : ℝ)
        ≤ γ * (Fintype.piFinset (fun _ : Fin n ↦ s)).card) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s), partResampleDefect R P j w
      ≤ (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2) := by
  classical
  set Y := Fintype.piFinset (fun _ : Fin n ↦ s) with hY
  have hYcard : (Y.card : ℝ) = (s.card : ℝ) ^ n := by
    rw [hY, Fintype.card_piFinset_const, Nat.cast_pow]
  have hparts : ∀ g : V → ℝ, ∑ b ∈ s, g b = ∑ l ∈ P.parts, ∑ b ∈ l, g b := by
    intro g
    conv_lhs => rw [← P.biUnion_parts]
    exact Finset.sum_biUnion P.disjoint
  -- Split by off-tuple, then by part, and identify each row with a section disagreement.
  have hsum : ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s), partResampleDefect R P j w
      = ∑ l ∈ P.parts, (l.card : ℝ) * ∑ rest ∈ Y,
          (sectionDisagreement l fun a ↦ R (Fin.insertNth j a rest) : ℝ) / (l.card : ℝ) ^ 2 := by
    rw [sum_piFinset_succAbove (fun _ ↦ s) j]
    simp_rw [hparts]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun rest _ ↦ ?_
    rw [sum_partResampleDefect_row R P j rest hl]
    have : (0 : ℝ) < l.card := by exact_mod_cast (P.nonempty_of_mem_parts hl).card_pos
    field_simp
  -- Bound each part: decency on ordinary parts, the universal `1/2` on exceptional parts.
  have hpart : ∀ l ∈ P.parts, ∑ rest ∈ Y,
      (sectionDisagreement l fun a ↦ R (Fin.insertNth j a rest) : ℝ) / (l.card : ℝ) ^ 2
        ≤ (2 * θ + γ / 2) * Y.card + (if l ∈ E then (Y.card : ℝ) / 2 else 0) := by
    intro l hl
    by_cases hlE : l ∈ E
    · simp only [hlE, ↓reduceIte]
      have hhalf : ∀ rest ∈ Y,
          (sectionDisagreement l fun a ↦ R (Fin.insertNth j a rest) : ℝ) / (l.card : ℝ) ^ 2
            ≤ 1 / 2 := fun rest _ ↦ by
        rw [sectionDisagreement_div_sq]; exact two_mul_mul_one_sub_le_half
      calc _ ≤ ∑ _rest ∈ Y, (1 / 2 : ℝ) := Finset.sum_le_sum hhalf
        _ = (Y.card : ℝ) / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := by
          have : (0 : ℝ) ≤ (2 * θ + γ / 2) * Y.card := by positivity
          linarith
    · simp only [hlE, ↓reduceIte, add_zero]
      exact sum_normalizedDisagreement_le Y l (fun rest a ↦ R (Fin.insertNth j a rest)) hθ
        (hdec l hl hlE)
  have hcardE : ∑ l ∈ P.parts, (if l ∈ E then (l.card : ℝ) else 0) = ∑ l ∈ E, (l.card : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hE]
  have hcardParts : ∑ l ∈ P.parts, (l.card : ℝ) = s.card := by
    exact_mod_cast P.sum_card_parts
  have hnonneg : ∀ l ∈ P.parts, (0 : ℝ) ≤ l.card := fun l _ ↦ by positivity
  calc ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s), partResampleDefect R P j w
      = ∑ l ∈ P.parts, (l.card : ℝ) * ∑ rest ∈ Y,
          (sectionDisagreement l fun a ↦ R (Fin.insertNth j a rest) : ℝ) / (l.card : ℝ) ^ 2 :=
        hsum
    _ ≤ ∑ l ∈ P.parts, (l.card : ℝ)
          * ((2 * θ + γ / 2) * Y.card + (if l ∈ E then (Y.card : ℝ) / 2 else 0)) :=
        Finset.sum_le_sum fun l hl ↦ mul_le_mul_of_nonneg_left (hpart l hl) (hnonneg l hl)
    _ = (2 * θ + γ / 2) * Y.card * ∑ l ∈ P.parts, (l.card : ℝ)
          + (Y.card : ℝ) / 2 * ∑ l ∈ P.parts, (if l ∈ E then (l.card : ℝ) else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        split_ifs <;> ring
    _ = (2 * θ + γ / 2) * Y.card * s.card + (Y.card : ℝ) / 2 * ∑ l ∈ E, (l.card : ℝ) := by
        rw [hcardParts, hcardE]
    _ ≤ (2 * θ + γ / 2) * Y.card * s.card + (Y.card : ℝ) / 2 * (lam * s.card) := by
        have : (0 : ℝ) ≤ (Y.card : ℝ) / 2 := by positivity
        have := mul_le_mul_of_nonneg_left hlam this
        linarith
    _ = (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2) := by
        rw [hYcard]; ring

end Decency

/-! ### Labelled fibres: unused labels allowed -/

section Labels

variable {Λ : Type*} [DecidableEq Λ] (lab : V → Λ) (s : Finset V)

instance instDecidableRelKer : DecidableRel (Setoid.ker lab).r :=
  fun a b ↦ inferInstanceAs (Decidable (lab a = lab b))

/-- The fibre of a label: the elements of `s` carrying it (empty for an unused label). -/
def labelFibre (a : Λ) : Finset V := s.filter fun v ↦ lab v = a

/-- The partition of `s` into the nonempty fibres of a labelling: mathlib's
`Finpartition.ofSetSetoid` on the kernel setoid of `lab`. Unused labels contribute no part. -/
def labelPartition : Finpartition s := Finpartition.ofSetSetoid (Setoid.ker lab) s

omit [DecidableEq V] in
theorem labelFibre_eq_empty_iff (a : Λ) : labelFibre lab s a = ∅ ↔ ∀ v ∈ s, lab v ≠ a := by
  simp [labelFibre, Finset.filter_eq_empty_iff]

/-- The part of an element of `s` is the fibre of its label. -/
theorem labelPartition_part_eq {b : V} (hb : b ∈ s) :
    (labelPartition lab s).part b = labelFibre lab s (lab b) := by
  ext v
  rw [labelPartition, Finpartition.mem_part_ofSetSetoid_iff_rel]
  simp only [labelFibre, Finset.mem_filter, hb, true_and]
  exact ⟨fun h ↦ ⟨h.1, h.2.symm⟩, fun h ↦ ⟨h.1, h.2.symm⟩⟩

omit [DecidableEq V] in
/-- **Reassembly over label tuples.** A sum over `s^m` is the sum over all label tuples `c` of
the sum over the box `∏ᵢ labelFibre (c i)`; boxes with an unused label are empty. -/
theorem sum_piFinset_const_eq_sum_labelBoxes [Fintype Λ] {m : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin m → V) → M) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin m ↦ s), f w
      = ∑ c : Fin m → Λ, ∑ w ∈ Fintype.piFinset (fun i ↦ labelFibre lab s (c i)), f w := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w ↦ lab ∘ w) (t := Finset.univ)
    (fun w _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext w
  simp only [Finset.mem_filter, Fintype.mem_piFinset, labelFibre, funext_iff, Function.comp]
  exact ⟨fun ⟨h1, h2⟩ i ↦ ⟨h1 i, h2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

/-- For the label partition, the part-resampling defect resamples inside the fibre of the
label of `w j`. -/
theorem partResampleDefect_labelPartition {n : ℕ} (R : (Fin (n + 1) → V) → Prop)
    [DecidablePred R] (j : Fin (n + 1)) {w : Fin (n + 1) → V} (hw : w j ∈ s) :
    partResampleDefect R (labelPartition lab s) j w
      = (((labelFibre lab s (lab (w j))).filter
            fun a ↦ ¬ (R w ↔ R (Function.update w j a))).card : ℝ)
          / (labelFibre lab s (lab (w j))).card := by
  unfold partResampleDefect
  rw [labelPartition_part_eq lab s hw]

/-- **The labelled global bound.** For the label partition, the edit distance of the majority
rounding is at most the sum over coordinates, label tuples `c`, and tuples of the label box of
the resampling defect inside the fibre of `c j`; boxes with an unused label are empty. -/
theorem editDistance_majorityRound_labelPartition_le [Fintype Λ] {L : FirstOrder.Language}
    [FiniteRelational L] (M : FiniteRelModel L V) {n : ℕ} (S : L.Relations (n + 1)) :
    (editDistance (M.Holds S) ((M.majorityRound (labelPartition lab s)).Holds S)
        (fun _ : Fin (n + 1) ↦ s) : ℝ)
      ≤ ∑ j : Fin (n + 1), ∑ c : Fin (n + 1) → Λ,
          ∑ w ∈ Fintype.piFinset (fun i ↦ labelFibre lab s (c i)),
            (((labelFibre lab s (c j)).filter
                fun a ↦ ¬ (M.Holds S w ↔ M.Holds S (Function.update w j a))).card : ℝ)
              / (labelFibre lab s (c j)).card := by
  refine (editDistance_majorityRound_le_sum_partResampleDefect M (labelPartition lab s) S).trans
    (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_))
  rw [sum_piFinset_const_eq_sum_labelBoxes lab s]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun w hw ↦ ?_
  have hw' := Fintype.mem_piFinset.mp hw j
  rw [labelFibre, Finset.mem_filter] at hw'
  rw [partResampleDefect_labelPartition lab s _ j hw'.1, hw'.2]

end Labels

section Assembly

variable {L : FirstOrder.Language} [FiniteRelational L]

/-- **Majority rounding cost from summed coordinate defects.** For a symbol of arity `n + 1`,
exceptional parts `E ⊆ P.parts` of total size at most `λ·|s|`, and decency (at most a
`γ`-fraction of ambient off-tuples inclusively `θ`-mixed) on every ordinary part and coordinate,
the edit distance from `M` to its majority rounding on `s^(n+1)` is at most
`(n + 1) · |s|^(n+1) · (2θ + γ/2 + λ/2)`. -/
theorem editDistance_majorityRound_le (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ}
    (S : L.Relations (n + 1)) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (j : Fin (n + 1)), ∀ l ∈ P.parts, l ∉ E →
      (((Fintype.piFinset (fun _ : Fin n ↦ s)).filter fun rest ↦
          InclusiveMixed θ (densityOn l fun a ↦ M.Holds S (Fin.insertNth j a rest))).card : ℝ)
        ≤ γ * (Fintype.piFinset (fun _ : Fin n ↦ s)).card) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
      ≤ (n + 1) * (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2) := by
  calc (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
      ≤ ∑ j : Fin (n + 1), ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s),
          partResampleDefect (M.Holds S) P j w :=
        editDistance_majorityRound_le_sum_partResampleDefect M P S
    _ ≤ ∑ _j : Fin (n + 1), (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2) :=
        Finset.sum_le_sum fun j _ ↦
          sum_partResampleDefect_le (M.Holds S) P j hθ hγ E hE hlam (hdec j)
    _ = (n + 1) * (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

end Assembly

/-! ### Tests -/

section Tests

-- The part-resampling defect vanishes on a relation constant along coordinate `j`.
example (P : Finpartition s) (R : (Fin 2 → V) → Prop) [DecidablePred R]
    (h : ∀ w a, R (Function.update w 1 a) ↔ R w) (w : Fin 2 → V) :
    partResampleDefect R P 1 w = 0 := by
  unfold partResampleDefect
  rw [Finset.filter_false_of_mem fun a _ ↦ by rw [h]; exact not_not.mpr Iff.rfl]
  simp

-- Endpoint: the empty host gives a zero total (every part-resampling sum is over `∅^(n+1) = ∅`).
example (R : (Fin 3 → V) → Prop) [DecidablePred R] (P : Finpartition (∅ : Finset V))
    (j : Fin 3) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin 3 ↦ (∅ : Finset V)), partResampleDefect R P j w = 0 := by
  rw [Fintype.piFinset_empty, Finset.sum_empty]

-- **An unused label.** `lab₃ = ![0, 0, 2]` on `Fin 3` never uses label `1`: its fibre is empty,
-- the partition has the two parts `{0, 1}` and `{2}`, and the reassembly over the nine label
-- pairs still recovers `|s|² = 9` (every box with a `1` is empty).
private def lab₃ : Fin 3 → Fin 3 := ![0, 0, 2]
example : labelFibre lab₃ Finset.univ 1 = ∅ := by decide
example : (labelPartition lab₃ Finset.univ).parts = {{0, 1}, {2}} := by decide
example : ∑ c : Fin 2 → Fin 3,
    (Fintype.piFinset fun i ↦ labelFibre lab₃ Finset.univ (c i)).card = 9 := by decide
example : ∑ c : Fin 2 → Fin 3,
      (Fintype.piFinset fun i ↦ labelFibre lab₃ Finset.univ (c i)).card
    = (Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 3))).card := by
  have h := sum_piFinset_const_eq_sum_labelBoxes lab₃ Finset.univ (m := 2) (fun _ ↦ (1 : ℕ))
  calc ∑ c : Fin 2 → Fin 3, (Fintype.piFinset fun i ↦ labelFibre lab₃ Finset.univ (c i)).card
      = ∑ c : Fin 2 → Fin 3, ∑ _w ∈ Fintype.piFinset fun i ↦ labelFibre lab₃ Finset.univ (c i),
          (1 : ℕ) := Finset.sum_congr rfl fun c _ ↦ Finset.card_eq_sum_ones _
    _ = ∑ _w ∈ Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 3)), (1 : ℕ) := h.symm
    _ = _ := (Finset.card_eq_sum_ones _).symm

end Tests

end RegularityLemmata
