/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.PartitionDefect
import RegularityLemmata.Relational.MajorityAssembly

/-!
# Majority rounding at the join of arbitrary coordinate partitions

* **Bridge to the partition defect.** The summed part-resampling defect of a relation at
  coordinate `j` (`partResampleDefect`, `RegularityLemmata/Relational/MajorityAssembly.lean`)
  is the family defect of the sections `a ↦ R (insertNth j a rest)`, `rest` over the ambient
  off-tuples (`sum_partResampleDefect_eq_familyDefect`).
* **Labelled partitions.** For `labelPartition lab s` the defect is the sum over *all* labels of
  the fibre defects, an unused (empty) fibre contributing `0`
  (`partitionDefect_labelPartition`).
* **The join.** `coordinateJoin P` (`RegularityLemmata/Partition/Basic.lean`) is the common
  refinement of the coordinate partitions `P : Fin (n+1) → Finpartition s`, below every `P j`,
  with at most `∏ⱼ #(P j).parts` parts.
* **Majority rounding for arbitrary coordinate partitions**
  (`editDistance_majorityRound_coordinateJoin_le`): rounding `M` at the join has edit distance
  on `s^(n+1)` at most `∑ⱼ familyDefect (P j)` of the coordinate-`j` sections, i.e. the sum of
  the coordinate defects **each measured in its own partition**. The rounded model is
  indivisible for the join (`majorityRound_isIndivisibleFor`), whose part count is bounded as
  above. Proof: the one-partition bound at the join, the bridge, and refinement monotonicity
  `partitionDefect_mono` along `coordinateJoin_le`.

Compiled consumers (source, not published API modules): a directed binary relation with two
partitions,
<https://github.com/cameronfreer/regularity-lemmata/blob/main/examples/DirectedJoinRounding.lean>,
and a symmetric relation with one partition,
<https://github.com/cameronfreer/regularity-lemmata/blob/main/examples/SymmetricRounding.lean>.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### Bridge to the partition defect -/

/-- The summed part-resampling defect at coordinate `j` is the family defect of the
coordinate-`j` sections over the ambient off-tuples. -/
theorem sum_partResampleDefect_eq_familyDefect {n : ℕ} (R : (Fin (n + 1) → V) → Prop)
    [DecidablePred R] (P : Finpartition s) (j : Fin (n + 1)) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin (n + 1) ↦ s), partResampleDefect R P j w
      = familyDefect P (Fintype.piFinset (fun _ : Fin n ↦ s))
          fun rest a ↦ R (Fin.insertNth j a rest) := by
  classical
  rw [sum_piFinset_succAbove (fun _ ↦ s) j]
  refine Finset.sum_congr rfl fun rest _ ↦ ?_
  have hparts : ∀ g : V → ℝ, ∑ b ∈ s, g b = ∑ l ∈ P.parts, ∑ b ∈ l, g b := by
    intro g
    conv_lhs => rw [← P.biUnion_parts]
    exact Finset.sum_biUnion P.disjoint
  rw [hparts]
  exact Finset.sum_congr rfl fun l hl ↦ sum_partResampleDefect_row R P j rest hl

/-! ### Labelled partitions -/

section Labels

variable {Λ : Type*} [DecidableEq Λ] (lab : V → Λ) (s : Finset V)

/-- The defect of a labelled partition is the sum over all labels of the fibre defects; an
unused label has an empty fibre and contributes `0`. -/
theorem partitionDefect_labelPartition [Fintype Λ] (p : V → Prop) [DecidablePred p] :
    partitionDefect (labelPartition lab s) p
      = ∑ a : Λ, (sectionDisagreement (labelFibre lab s a) p : ℝ) / (labelFibre lab s a).card := by
  classical
  unfold partitionDefect
  rw [labelPartition_parts, Finset.sum_image]
  · refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha ↦ ?_)
    have : labelFibre lab s a = ∅ := by
      rw [labelFibre_eq_empty_iff]
      intro v hv hva
      exact ha (Finset.mem_image.mpr ⟨v, hv, hva⟩)
    rw [this]; simp
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    have hva : v ∈ labelFibre lab s (lab v) := Finset.mem_filter.mpr ⟨hv, rfl⟩
    rw [hab, labelFibre, Finset.mem_filter] at hva
    exact hva.2

end Labels

/-! ### Majority rounding for arbitrary coordinate partitions -/

variable {L : FirstOrder.Language} [FiniteRelational L]

/-- **The majority bound by the summed coordinate defects, each in its own partition.**
Rounding `M` at the join of the coordinate partitions `P j` has edit distance on `s^(n+1)` at
most `∑ⱼ familyDefect (P j)` of the coordinate-`j` sections. -/
theorem editDistance_majorityRound_coordinateJoin_le (M : FiniteRelModel L V) {n : ℕ}
    (P : Fin (n + 1) → Finpartition s) (S : L.Relations (n + 1)) :
    (editDistance (M.Holds S) ((M.majorityRound (coordinateJoin P)).Holds S)
        (fun _ : Fin (n + 1) ↦ s) : ℝ)
      ≤ ∑ j : Fin (n + 1), familyDefect (P j) (Fintype.piFinset (fun _ : Fin n ↦ s))
          fun rest a ↦ M.Holds S (Fin.insertNth j a rest) := by
  refine (editDistance_majorityRound_le_sum_partResampleDefect M (coordinateJoin P) S).trans
    (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [sum_partResampleDefect_eq_familyDefect]
  exact familyDefect_mono (coordinateJoin_le P j) _ _

/-- The rounded model packaged: indivisible for the join, nullary-exact, part count bounded by
the product, and the edit bound above for the given symbol. -/
theorem exists_isIndivisibleFor_coordinateJoin (M : FiniteRelModel L V) {n : ℕ}
    (P : Fin (n + 1) → Finpartition s) (S : L.Relations (n + 1)) :
    ∃ N : FiniteRelModel L V, N.IsIndivisibleFor (coordinateJoin P) ∧ NullaryCompatible M N ∧
      (coordinateJoin P).parts.card ≤ ∏ j, (P j).parts.card ∧
      (editDistance (M.Holds S) (N.Holds S) (fun _ : Fin (n + 1) ↦ s) : ℝ)
        ≤ ∑ j : Fin (n + 1), familyDefect (P j) (Fintype.piFinset (fun _ : Fin n ↦ s))
            fun rest a ↦ M.Holds S (Fin.insertNth j a rest) :=
  ⟨M.majorityRound (coordinateJoin P), majorityRound_isIndivisibleFor M _,
    nullaryCompatible_majorityRound M _, card_parts_coordinateJoin_le P,
    editDistance_majorityRound_coordinateJoin_le M P S⟩

/-! ### Tests -/

section Tests

-- The labelled defect on `![0, 0, 2] : Fin 3 → Fin 3` (label `1` unused) for the section
-- `(· = 0)`: fibre `{0, 1}` contributes `2·1·1/2 = 1`, the empty fibre `0`, fibre `{2}` `0`.
private def lab₃ : Fin 3 → Fin 3 := ![0, 0, 2]
example : partitionDefect (labelPartition lab₃ Finset.univ) (fun a ↦ a = 0) = 1 := by
  rw [partitionDefect_labelPartition, Fin.sum_univ_three]
  rw [show labelFibre lab₃ Finset.univ 0 = {0, 1} by decide,
    show labelFibre lab₃ Finset.univ 1 = ∅ by decide,
    show labelFibre lab₃ Finset.univ 2 = {2} by decide,
    show sectionDisagreement ({0, 1} : Finset (Fin 3)) (fun a ↦ a = 0) = 2 by decide,
    show sectionDisagreement ({2} : Finset (Fin 3)) (fun a ↦ a = 0) = 0 by decide]
  simp

-- Join cardinality on two coordinates.
example (P₁ P₂ : Finpartition s) : (coordinateJoin ![P₁, P₂]).parts.card
    ≤ P₁.parts.card * P₂.parts.card := by
  have := card_parts_coordinateJoin_le ![P₁, P₂]
  simpa [Fin.prod_univ_two] using this

end Tests

end RegularityLemmata
