/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.FinCases

/-!
# Heterogeneous tuple boxes and lower faces

Finite tuples live in boxes `Fintype.piFinset A` for `A : Fin k → Finset α`. This file
provides the coordinate-deletion operation on tuples (`lowerFace`, via `Fin.succAbove`),
its computed behavior at arity 3, and the identification of `Fin 2`-boxes with binary
products via mathlib's `finTwoArrowEquiv`.

Mathlib provides the box itself (`Fintype.piFinset`), its cardinality
(`Fintype.card_piFinset`), and the pair equivalence (`finTwoArrowEquiv`); this file only
adds the glue used by the density and counting layers, including the split of a sum over a
box at one coordinate into the pivot value and the lower-box tuple (`sum_piFinset_succAbove`,
via mathlib's `Fin.insertNth`) and the count of tuples meeting a set (`card_filter_apply_mem`,
`card_filter_exists_apply_mem_le`).
-/

namespace RegularityLemmata

variable {α : Type*}

/-! ### Lower faces (coordinate deletion) -/

/-- The `i`-th lower face of a `(j+1)`-tuple: the `j`-tuple obtained by deleting
coordinate `i`, with the remaining coordinates in order (via `Fin.succAbove`). -/
def lowerFace {j : ℕ} (v : Fin (j + 1) → α) (i : Fin (j + 1)) : Fin j → α :=
  fun k => v (i.succAbove k)

@[simp] theorem lowerFace_apply {j : ℕ} (v : Fin (j + 1) → α) (i : Fin (j + 1)) (k : Fin j) :
    lowerFace v i k = v (i.succAbove k) := rfl

/-- A sum over the box `∏ᵢ A i` split at coordinate `j`: the pivot value `b ∈ A j` and the
off-coordinate tuple in the lower box `∏_{i ≠ j} A i` (indexed via `Fin.succAbove`). -/
theorem sum_piFinset_succAbove {M : Type*} [AddCommMonoid M] {n : ℕ}
    (A : Fin (n + 1) → Finset α) (j : Fin (n + 1)) (f : (Fin (n + 1) → α) → M) :
    ∑ w ∈ Fintype.piFinset A, f w
      = ∑ rest ∈ Fintype.piFinset (fun i ↦ A (j.succAbove i)), ∑ b ∈ A j,
          f (Fin.insertNth j b rest) := by
  rw [← Finset.sum_product' (s := Fintype.piFinset (fun i ↦ A (j.succAbove i))) (t := A j)
    (f := fun rest b ↦ f (Fin.insertNth j b rest))]
  symm
  refine Finset.sum_nbij' (fun q ↦ Fin.insertNth j q.2 q.1)
    (fun w ↦ (Fin.removeNth j w, w j)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rest, b⟩ hq
    rw [Finset.mem_product] at hq
    rw [Fin.mem_piFinset_iff_pivot_removeNth j]
    simpa [Fin.removeNth, Fintype.mem_piFinset] using ⟨hq.2, Fintype.mem_piFinset.mp hq.1⟩
  · intro w hw
    rw [Fin.mem_piFinset_iff_pivot_removeNth j] at hw
    rw [Finset.mem_product]
    exact ⟨hw.2, hw.1⟩
  · rintro ⟨rest, b⟩ _
    simp
  · intro w _
    simp
  · rintro ⟨rest, b⟩ _
    rfl

/-- The tuples of `s^(n+1)` whose `j`-th coordinate lies in `D ⊆ s`: exactly `|D| · |s|^n`. -/
theorem card_filter_apply_mem [DecidableEq α] {s D : Finset α} (hD : D ⊆ s) {n : ℕ}
    (j : Fin (n + 1)) :
    ((Fintype.piFinset fun _ : Fin (n + 1) ↦ s).filter fun x ↦ x j ∈ D).card
      = D.card * s.card ^ n := by
  classical
  rw [Finset.card_filter, sum_piFinset_succAbove (fun _ ↦ s) j]
  simp only [Fin.insertNth_apply_same]
  rw [Finset.sum_const, Fintype.card_piFinset_const, smul_eq_mul, ← Finset.card_filter,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hD]
  exact Nat.mul_comm _ _

/-- Union bound: at most `(n+1) · |D| · |s|^n` tuples of `s^(n+1)` meet `D ⊆ s`. -/
theorem card_filter_exists_apply_mem_le [DecidableEq α] {s D : Finset α} (hD : D ⊆ s) (n : ℕ) :
    ((Fintype.piFinset fun _ : Fin (n + 1) ↦ s).filter fun x ↦ ∃ i, x i ∈ D).card
      ≤ (n + 1) * D.card * s.card ^ n := by
  classical
  calc ((Fintype.piFinset fun _ : Fin (n + 1) ↦ s).filter fun x ↦ ∃ i, x i ∈ D).card
      ≤ (Finset.univ.biUnion fun j : Fin (n + 1) ↦
          (Fintype.piFinset fun _ : Fin (n + 1) ↦ s).filter fun x ↦ x j ∈ D).card := by
        refine Finset.card_le_card fun x hx ↦ ?_
        rw [Finset.mem_filter] at hx
        obtain ⟨hxs, j, hj⟩ := hx
        rw [Finset.mem_biUnion]
        exact ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hxs, hj⟩⟩
    _ ≤ ∑ j : Fin (n + 1),
          ((Fintype.piFinset fun _ : Fin (n + 1) ↦ s).filter fun x ↦ x j ∈ D).card :=
        Finset.card_biUnion_le
    _ = (n + 1) * D.card * s.card ^ n := by
        rw [Finset.sum_congr rfl fun j _ ↦ card_filter_apply_mem hD j, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        exact (Nat.mul_assoc _ _ _).symm

/-- Lower faces of injective tuples are injective. -/
theorem lowerFace_injective {j : ℕ} {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (i : Fin (j + 1)) : Function.Injective (lowerFace v i) :=
  hv.comp Fin.succAbove_right_injective

/-! ### Arity-3 face indexing -/

/-- Arity-3 face indexing: dropping coordinate `i` keeps the complementary ordered pair. -/
theorem succAbove_faces_three :
    ((0 : Fin 3).succAbove 0 = 1 ∧ (0 : Fin 3).succAbove 1 = 2) ∧
    ((1 : Fin 3).succAbove 0 = 0 ∧ (1 : Fin 3).succAbove 1 = 2) ∧
    ((2 : Fin 3).succAbove 0 = 0 ∧ (2 : Fin 3).succAbove 1 = 1) := by decide

/-- The pair encoding of a lower face reads off the two surviving coordinates. -/
@[simp] theorem finTwoArrowEquiv_lowerFace (v : Fin 3 → α) (i : Fin 3) :
    finTwoArrowEquiv α (lowerFace v i) = (v (i.succAbove 0), v (i.succAbove 1)) := rfl

theorem finTwoArrowEquiv_lowerFace_zero (v : Fin 3 → α) :
    finTwoArrowEquiv α (lowerFace v 0) = (v 1, v 2) := by
  rw [finTwoArrowEquiv_lowerFace,
    show (0 : Fin 3).succAbove 0 = 1 from by decide,
    show (0 : Fin 3).succAbove 1 = 2 from by decide]

theorem finTwoArrowEquiv_lowerFace_one (v : Fin 3 → α) :
    finTwoArrowEquiv α (lowerFace v 1) = (v 0, v 2) := by
  rw [finTwoArrowEquiv_lowerFace,
    show (1 : Fin 3).succAbove 0 = 0 from by decide,
    show (1 : Fin 3).succAbove 1 = 2 from by decide]

theorem finTwoArrowEquiv_lowerFace_two (v : Fin 3 → α) :
    finTwoArrowEquiv α (lowerFace v 2) = (v 0, v 1) := by
  rw [finTwoArrowEquiv_lowerFace,
    show (2 : Fin 3).succAbove 0 = 0 from by decide,
    show (2 : Fin 3).succAbove 1 = 1 from by decide]

/-- Membership transports across the pair encoding: `w ∈ P` iff its pair encoding lies in
the `finTwoArrowEquiv`-image of `P`. -/
theorem mem_map_finTwoArrowEquiv (P : Finset (Fin 2 → α)) (w : Fin 2 → α) :
    finTwoArrowEquiv α w ∈ P.map (finTwoArrowEquiv α).toEmbedding ↔ w ∈ P := by
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-! ### `Fin 1` boxes

The arity-one companions of the `Fin 2` lemmas below, under the encoding `a ↦ ![a]`. No
`DecidableEq α` is needed: the transfer is a bijection, not an image. -/

/-- Cardinality of a `Fin 1` box. -/
theorem card_piFinset_one (A : Fin 1 → Finset α) :
    (Fintype.piFinset A).card = (A 0).card := by
  rw [Fintype.card_piFinset, Fin.prod_univ_one]

/-- Filter cardinalities agree across the arity-one encoding `a ↦ ![a]`. -/
theorem card_filter_piFinset_one (A : Fin 1 → Finset α) (R : (Fin 1 → α) → Prop)
    [DecidablePred R] :
    ((Fintype.piFinset A).filter R).card = ((A 0).filter fun a ↦ R ![a]).card := by
  refine Finset.card_bij' (fun x _ ↦ x 0) (fun a _ ↦ ![a]) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Fintype.mem_piFinset.mp hx.1 0, ?_⟩
    rw [show (![x 0] : Fin 1 → α) = x from funext fun i ↦ by fin_cases i; rfl]
    exact hx.2
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, ha.2⟩
    fin_cases i
    simpa using ha.1
  · intro x hx
    exact funext fun i ↦ by fin_cases i; rfl
  · intro a ha
    simp

/-! ### `Fin 2` boxes as binary products -/

/-- A `Fin 2` box is a binary product under the pair encoding. Stated for an arbitrary
family `A : Fin 2 → Finset α`; instantiate with `![C, D]` for the two-set form. -/
theorem image_finTwoArrowEquiv_piFinset [DecidableEq α] (A : Fin 2 → Finset α) :
    (Fintype.piFinset A).image (finTwoArrowEquiv α) = A 0 ×ˢ A 1 := by
  ext ⟨a, b⟩
  rw [Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨f, hf, hfe⟩
    have h0 : f 0 = a := congrArg Prod.fst hfe
    have h1 : f 1 = b := congrArg Prod.snd hfe
    exact ⟨h0 ▸ Fintype.mem_piFinset.mp hf 0, h1 ▸ Fintype.mem_piFinset.mp hf 1⟩
  · rintro ⟨ha, hb⟩
    refine ⟨![a, b], Fintype.mem_piFinset.mpr fun i => ?_, rfl⟩
    fin_cases i
    · simpa using ha
    · simpa using hb

/-- Cardinality of a `Fin 2` box. -/
theorem card_piFinset_two (A : Fin 2 → Finset α) :
    (Fintype.piFinset A).card = (A 0).card * (A 1).card := by
  rw [Fintype.card_piFinset, Fin.prod_univ_two]

/-- Filtering a `Fin 2` box corresponds to filtering the binary product. -/
theorem filter_piFinset_two_image [DecidableEq α] (A : Fin 2 → Finset α)
    (R : (Fin 2 → α) → Prop) [DecidablePred R] :
    ((Fintype.piFinset A).filter R).image (finTwoArrowEquiv α) =
      (A 0 ×ˢ A 1).filter fun p => R ![p.1, p.2] := by
  ext ⟨a, b⟩
  rw [Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨f, hf, hfe⟩
    rw [Finset.mem_filter] at hf
    have h0 : f 0 = a := congrArg Prod.fst hfe
    have h1 : f 1 = b := congrArg Prod.snd hfe
    have hfeq : f = ![a, b] := by
      funext i; fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨h0 ▸ Fintype.mem_piFinset.mp hf.1 0, h1 ▸ Fintype.mem_piFinset.mp hf.1 1⟩, ?_⟩
    rw [← hfeq]
    exact hf.2
  · rintro ⟨⟨ha, hb⟩, hR⟩
    refine ⟨![a, b],
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, hR⟩, rfl⟩
    fin_cases i
    · simpa using ha
    · simpa using hb

/-- Filter cardinalities agree across the pair encoding. -/
theorem card_filter_piFinset_two [DecidableEq α] (A : Fin 2 → Finset α)
    (R : (Fin 2 → α) → Prop) [DecidablePred R] :
    ((Fintype.piFinset A).filter R).card =
      ((A 0 ×ˢ A 1).filter fun p => R ![p.1, p.2]).card := by
  rw [← filter_piFinset_two_image A R]
  exact (Finset.card_image_of_injective _ (finTwoArrowEquiv α).injective).symm

/-! ### Tests and adversarial examples -/

-- The empty-arity box contains exactly the empty tuple, even over empty coordinate sets.
example : (Fintype.piFinset (fun _ : Fin 0 => (∅ : Finset (Fin 2)))).card = 1 := by decide

-- A box with one empty coordinate is empty.
example : (Fintype.piFinset ![({0, 1} : Finset (Fin 3)), ∅, {2}]).card = 0 := by decide

-- Two-coordinate box cardinality, computed and via `card_piFinset_two`.
example : (Fintype.piFinset ![({0, 1} : Finset (Fin 3)), {0, 1, 2}]).card = 6 := by decide
example : (Fintype.piFinset ![({0, 1} : Finset (Fin 3)), {0, 1, 2}]).card = 6 := by
  rw [card_piFinset_two]; decide

-- Lower faces of a concrete triple, all three coordinates.
example : lowerFace (![0, 1, 2] : Fin 3 → Fin 3) 0 = ![1, 2] := by decide
example : lowerFace (![0, 1, 2] : Fin 3 → Fin 3) 1 = ![0, 2] := by decide
example : lowerFace (![0, 1, 2] : Fin 3 → Fin 3) 2 = ![0, 1] := by decide

-- Pair encodings of lower faces.
example : finTwoArrowEquiv (Fin 3) (lowerFace ![0, 1, 2] 1) = (0, 2) := by decide

end RegularityLemmata
