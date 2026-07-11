/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.Basic
import Mathlib.Order.Partition.Equipartition
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Cell splitting and equitable partitions

Within-cell splitting: `twoPartition` splits one finset into a nonempty subset and its
complement, and `refineBySplit` refines a partition by splitting a single part —
adding exactly one part (the elementary step of energy-increment iterations).

Chunking, remainder distribution, and balanced splitting are mathlib's
`Finpartition.equitabilise` / `Finpartition.IsEquipartition`; this file only re-exports
the two facts the almost-refinement layer consumes (part sizes in `{m, m+1}` and the
per-parent uncovered remainder bound `Finpartition.card_parts_equitabilise_subset_le`)
plus `Finpartition.exists_equipartition_card_eq`. Size bounds for equipartitions are
`Finpartition.IsEquipartition.average_le_card_part` / `card_part_le_average_add_one`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-! ### Splitting one cell -/

/-- Split a cell `C` into `A` and `C \ A`, producing a two-part partition of `C`. -/
def twoPartition (C A : Finset α) (hA : A ⊆ C)
    (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) : Finpartition C :=
  (Finpartition.indiscrete (Finset.Nonempty.ne_empty hAne)).extend
    (Finset.Nonempty.ne_empty hBne)
    disjoint_sdiff_self_right
    (Finset.union_sdiff_of_subset hA)

/-- The two-part partition has exactly 2 parts. -/
theorem twoPartition_card {C A : Finset α} {hA : A ⊆ C}
    {hAne : A.Nonempty} {hBne : (C \ A).Nonempty} :
    (twoPartition C A hA hAne hBne).parts.card = 2 := by
  unfold twoPartition
  rw [Finpartition.card_extend, Finpartition.indiscrete_parts, Finset.card_singleton]

/-- Refine a partition by splitting the part `C` into `A` and `C \ A`. -/
def refineBySplit (P : Finpartition s) (C : Finset α) (_hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    Finpartition s :=
  P.bind (fun D hD =>
    if h : D = C then h ▸ twoPartition C A hA hAne hBne
    else Finpartition.indiscrete (by rintro rfl; exact absurd hD P.bot_notMem))

/-- The refined partition refines (`≤`) the original. -/
theorem refineBySplit_le (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    refineBySplit P C hC A hA hAne hBne ≤ P := by
  intro b hb
  simp only [refineBySplit, Finpartition.mem_bind] at hb
  obtain ⟨D, hD, hb'⟩ := hb
  refine ⟨D, hD, ?_⟩
  set Q : Finpartition D := if h : D = C then h ▸ twoPartition C A hA hAne hBne
    else Finpartition.indiscrete (by rintro rfl; exact absurd hD P.bot_notMem) with hQ_def
  have hb_mem : b ∈ Q.parts := by convert hb'
  exact Q.le hb_mem

/-- Splitting one part adds exactly one part. -/
theorem refineBySplit_parts_card_eq (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts.card = P.parts.card + 1 := by
  simp only [refineBySplit, Finpartition.card_bind]
  set S := P.parts.attach
  set x₀ : { x // x ∈ P.parts } := ⟨C, hC⟩
  set f : { x // x ∈ P.parts } → ℕ := fun D =>
    (if h : D.1 = C then h ▸ twoPartition C A hA hAne hBne
     else Finpartition.indiscrete
      (show D.1 ≠ ⊥ by intro h; exact absurd (h ▸ D.2) P.bot_notMem)).parts.card
  have hx₀ : x₀ ∈ S := Finset.mem_attach _ _
  rw [show ∑ D ∈ S, _ = ∑ D ∈ S, f D from Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [← Finset.add_sum_erase S f hx₀]
  have hC_term : f x₀ = 2 := by simp [f, x₀, twoPartition_card]
  rw [hC_term]
  have hrest : ∀ D ∈ S.erase x₀, f D = 1 := by
    intro ⟨D, hD⟩ hmem
    have hne : D ≠ C := by
      intro heq; exact (Finset.mem_erase.mp hmem).1 (Subtype.ext heq)
    simp [f, hne, Finpartition.indiscrete_parts]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const]
  have hcard_erase : (S.erase x₀).card = P.parts.card - 1 := by
    rw [Finset.card_erase_of_mem hx₀, Finset.card_attach]
  rw [hcard_erase]
  have hpos : 0 < P.parts.card := Finset.card_pos.mpr ⟨C, hC⟩
  simp; omega

/-- Splitting one part adds at most one part. -/
theorem refineBySplit_parts_card_le (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts.card ≤ P.parts.card + 1 :=
  (refineBySplit_parts_card_eq P C hC A hA hAne hBne).le

/-! ### Exact characterizations of the split -/

/-- The two-part partition consists of exactly `A` and `C \ A`. -/
theorem twoPartition_parts {C A : Finset α} {hA : A ⊆ C} {hAne : A.Nonempty}
    {hBne : (C \ A).Nonempty} :
    (twoPartition C A hA hAne hBne).parts = {A, C \ A} := by
  rw [twoPartition, Finpartition.extend_parts, Finpartition.indiscrete_parts,
    Finset.pair_comm]

/-- Exact parts formula for the one-cell split. -/
theorem refineBySplit_parts (P : Finpartition s) (C : Finset α) (hC : C ∈ P.parts)
    (A : Finset α) (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    (refineBySplit P C hC A hA hAne hBne).parts = (P.parts.erase C) ∪ {A, C \ A} := by
  ext b
  simp only [refineBySplit, Finpartition.mem_bind, Finset.mem_union, Finset.mem_erase,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨D, hD, hb⟩
    by_cases h : D = C
    · subst h
      rw [dif_pos rfl] at hb
      have hb' : b ∈ (twoPartition D A hA hAne hBne).parts := hb
      rw [twoPartition_parts, Finset.mem_insert, Finset.mem_singleton] at hb'
      exact Or.inr hb'
    · rw [dif_neg h, Finpartition.indiscrete_parts, Finset.mem_singleton] at hb
      subst hb
      exact Or.inl ⟨h, hD⟩
  · rintro (⟨hbC, hbP⟩ | hb)
    · refine ⟨b, hbP, ?_⟩
      rw [dif_neg hbC, Finpartition.indiscrete_parts, Finset.mem_singleton]
    · refine ⟨C, hC, ?_⟩
      rw [dif_pos rfl]
      show b ∈ (twoPartition C A hA hAne hBne).parts
      rw [twoPartition_parts, Finset.mem_insert, Finset.mem_singleton]
      exact hb

/-- Membership in the split partition. -/
theorem mem_refineBySplit {P : Finpartition s} {C : Finset α} {hC : C ∈ P.parts}
    {A : Finset α} {hA : A ⊆ C} {hAne : A.Nonempty} {hBne : (C \ A).Nonempty}
    {b : Finset α} :
    b ∈ (refineBySplit P C hC A hA hAne hBne).parts ↔
      (b ∈ P.parts ∧ b ≠ C) ∨ b = A ∨ b = C \ A := by
  rw [refineBySplit_parts, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_singleton, and_comm]

/-- The split pieces are parts of the split partition. -/
theorem left_mem_refineBySplit {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    A ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inr (Or.inl rfl))

theorem sdiff_mem_refineBySplit {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty) :
    C \ A ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inr (Or.inr rfl))

/-- Every part other than the split one survives untouched. -/
theorem mem_refineBySplit_of_ne {P : Finpartition s} {C : Finset α} (hC : C ∈ P.parts)
    {A : Finset α} (hA : A ⊆ C) (hAne : A.Nonempty) (hBne : (C \ A).Nonempty)
    {D : Finset α} (hD : D ∈ P.parts) (hne : D ≠ C) :
    D ∈ (refineBySplit P C hC A hA hAne hBne).parts :=
  mem_refineBySplit.mpr (Or.inl ⟨hD, hne⟩)

/-! ### Equitabilise re-exports

The consumers below are `Partition/AlmostRefines.lean` and the graph ladder. -/

variable {a b m : ℕ} {P : Finpartition s}

/-- Part sizes of an equitabilisation lie in `{m, m + 1}`
(mathlib's `Finpartition.card_eq_of_mem_parts_equitabilise`). -/
theorem equitabilise_card_part {h : a * m + b * (m + 1) = s.card} {t : Finset α}
    (ht : t ∈ (P.equitabilise h).parts) : t.card = m ∨ t.card = m + 1 :=
  Finpartition.card_eq_of_mem_parts_equitabilise ht

/-- The uncovered remainder of each original part has size at most `m`
(mathlib's `Finpartition.card_parts_equitabilise_subset_le`, restated with
`Finset.filter`). This is the primitive behind `AlmostRefinesAt`. -/
theorem equitabilise_uncovered_card_le {h : a * m + b * (m + 1) = s.card} {t : Finset α}
    (ht : t ∈ P.parts) :
    (t \ ((P.equitabilise h).parts.filter (· ⊆ t)).biUnion id).card ≤ m :=
  P.card_parts_equitabilise_subset_le (h := h) ht

/-! ### Tests and adversarial examples -/

-- `twoPartition` on an explicit 4-element finset.
example :
    (twoPartition ({0, 1, 2, 3} : Finset (Fin 4)) {0, 1} (by decide) (by decide)
      (by decide)).parts.card = 2 := twoPartition_card

-- `refineBySplit` on the indiscrete partition of a 4-element finset: 1 + 1 parts.
example :
    (refineBySplit (⊤ : Finpartition ({0, 1, 2, 3} : Finset (Fin 4))) {0, 1, 2, 3}
      (by decide) {0, 1} (by decide) (by decide) (by decide)).parts.card = 2 := by
  rw [refineBySplit_parts_card_eq]
  decide

-- Degenerate split: a 2-element cell splits into singletons; a singleton cell admits
-- no further split (the `(C \ A).Nonempty` hypothesis is unsatisfiable for A = C).
example :
    (twoPartition ({0, 1} : Finset (Fin 4)) {0} (by decide) (by decide)
      (by decide)).parts.card = 2 := twoPartition_card
example : ¬ (({0} : Finset (Fin 4)) \ {0}).Nonempty := by decide

-- Equipartitions of size 3 of a 7-element set exist (mathlib wrap).
example :
    ∃ P : Finpartition ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      P.IsEquipartition ∧ P.parts.card = 3 :=
  Finpartition.exists_equipartition_card_eq _ (by norm_num) (by decide)

-- Equitabilising a 7-element ground set with 2·2 + 1·3 = 7: all parts have size 2 or 3.
example (P : Finpartition ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7))) :
    ∀ t ∈ (P.equitabilise (show 2 * 2 + 1 * (2 + 1) = _ from by decide)).parts,
      t.card = 2 ∨ t.card = 2 + 1 :=
  fun _ ht => equitabilise_card_part ht

end RegularityLemmata
