/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.RelationalApproximation

/-!
# A symmetric relation rounded at one partition

A compiled consumer of the arbitrary-partition majority bound for a **symmetric** binary
relation `S` (`S(a, b) ↔ S(b, a)`) and a single partition `P` used on both coordinates: the
join of the constant family is `P` itself (`coordinateJoin_const`), the column defects equal the
row defects by symmetry, so the edit distance of the majority rounding at `P` is at most
**twice the row defects** `2 · ∑_{b ∈ s} partitionDefect P (a ↦ S(a, b))`, and the rounded
relation is again symmetric (`majorityRound_symm`): the majority on the cell
`P.part a × P.part b` is the majority on `P.part b × P.part a`.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- A binary symbol is symmetric in `M`. -/
def Symmetric (M : FiniteRelModel L V) (S : L.Relations 2) : Prop :=
  ∀ a b, M.Holds S ![a, b] ↔ M.Holds S ![b, a]

/-- The row defect at `b`: the partition defect of `a ↦ S(a, b)`. -/
noncomputable def symRowDefect (M : FiniteRelModel L V) (S : L.Relations 2) (P : Finpartition s)
    (b : V) : ℝ :=
  partitionDefect P fun a ↦ M.Holds S ![a, b]

omit [DecidableEq V] in
private theorem cons_eq_vec (a : V) (rest : Fin 1 → V) : Fin.cons a rest = ![a, rest 0] := by
  ext i; fin_cases i <;> rfl

omit [DecidableEq V] in
private theorem insertNth_one_eq_vec (b : V) (rest : Fin 1 → V) :
    Fin.insertNth (1 : Fin 2) b rest = ![rest 0, b] := by
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.insertNth_last']
  ext i; fin_cases i <;> rfl

omit [DecidableEq V] in
private theorem eq_vecCons_two (x : Fin 2 → V) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

/-- Under symmetry the column defect at `a` is the row defect at `a`. -/
theorem colDefect_eq_rowDefect (M : FiniteRelModel L V) (S : L.Relations 2) (hsym : Symmetric M S)
    (P : Finpartition s) (a : V) :
    partitionDefect P (fun b ↦ M.Holds S ![a, b]) = symRowDefect M S P a := by
  unfold symRowDefect partitionDefect
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 2
  unfold sectionDisagreement
  congr 1
  refine Finset.filter_congr fun q _ ↦ ?_
  show ¬ (M.Holds S ![a, q.1] ↔ M.Holds S ![a, q.2]) ↔ ¬ (M.Holds S ![q.1, a] ↔ M.Holds S ![q.2, a])
  rw [hsym a q.1, hsym a q.2]

/-- The coordinate-`0` family defect is the summed row defect. -/
theorem familyDefect_zero_eq_sum_symRowDefect (M : FiniteRelModel L V) (S : L.Relations 2)
    (P : Finpartition s) :
    familyDefect P (Fintype.piFinset (fun _ : Fin 1 ↦ s))
        (fun rest a ↦ M.Holds S (Fin.insertNth 0 a rest))
      = ∑ b ∈ s, symRowDefect M S P b := by
  unfold familyDefect symRowDefect
  refine Finset.sum_nbij' (fun rest ↦ rest 0) (fun b _ ↦ b) ?_ ?_ ?_ ?_ ?_
  · intro rest h; exact Fintype.mem_piFinset.mp h 0
  · intro b hb; exact Fintype.mem_piFinset.mpr fun _ ↦ hb
  · intro rest _; funext i; fin_cases i; rfl
  · intro b _; rfl
  · intro rest _
    congr 1
    ext a
    show M.Holds S (Fin.insertNth 0 a rest) ↔ M.Holds S ![a, rest 0]
    rw [Fin.insertNth_zero', cons_eq_vec]

/-- Under symmetry the coordinate-`1` family defect is also the summed row defect. -/
theorem familyDefect_one_eq_sum_symRowDefect (M : FiniteRelModel L V) (S : L.Relations 2)
    (hsym : Symmetric M S) (P : Finpartition s) :
    familyDefect P (Fintype.piFinset (fun _ : Fin 1 ↦ s))
        (fun rest b ↦ M.Holds S (Fin.insertNth 1 b rest))
      = ∑ b ∈ s, symRowDefect M S P b := by
  unfold familyDefect
  refine Finset.sum_nbij' (fun rest ↦ rest 0) (fun b _ ↦ b) ?_ ?_ ?_ ?_ ?_
  · intro rest h; exact Fintype.mem_piFinset.mp h 0
  · intro b hb; exact Fintype.mem_piFinset.mpr fun _ ↦ hb
  · intro rest _; funext i; fin_cases i; rfl
  · intro b _; rfl
  · intro rest _
    rw [← colDefect_eq_rowDefect M S hsym]
    congr 1
    ext b
    show M.Holds S (Fin.insertNth 1 b rest) ↔ M.Holds S ![rest 0, b]
    rw [insertNth_one_eq_vec]

/-- **Symmetric relation, one partition.** The majority rounding at `P` is within twice the
summed row defects. -/
theorem editDistance_majorityRound_symm_le (M : FiniteRelModel L V) (S : L.Relations 2)
    (hsym : Symmetric M S) (P : Finpartition s) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 2 ↦ s) : ℝ)
      ≤ 2 * ∑ b ∈ s, symRowDefect M S P b := by
  have h := editDistance_majorityRound_coordinateJoin_le M (fun _ : Fin 2 ↦ P) S
  rw [coordinateJoin_const, Fin.sum_univ_two, familyDefect_zero_eq_sum_symRowDefect M S P,
    familyDefect_one_eq_sum_symRowDefect M S hsym P] at h
  linarith

omit [DecidableEq V] in
/-- The box of the swapped pair is the swapped box, and the count of a symmetric relation on
it is unchanged. -/
private theorem tupleCount_swap (M : FiniteRelModel L V) (S : L.Relations 2) (hsym : Symmetric M S)
    (A B : Finset V) :
    tupleCount (M.Holds S) ![A, B] = tupleCount (M.Holds S) ![B, A] := by
  unfold tupleCount
  refine Finset.card_nbij' (fun x ↦ ![x 1, x 0]) (fun x ↦ ![x 1, x 0]) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
    refine ⟨fun i ↦ ?_, ?_⟩
    · fin_cases i
      · exact hx.1 1
      · exact hx.1 0
    · rw [eq_vecCons_two x] at hx; exact (hsym _ _).mp hx.2
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
    refine ⟨fun i ↦ ?_, ?_⟩
    · fin_cases i
      · exact hx.1 1
      · exact hx.1 0
    · rw [eq_vecCons_two x] at hx; exact (hsym _ _).mp hx.2
  · intro x _; ext i; fin_cases i <;> rfl
  · intro x _; ext i; fin_cases i <;> rfl

/-- **The rounded relation is symmetric.** -/
theorem majorityRound_symm (M : FiniteRelModel L V) (S : L.Relations 2) (hsym : Symmetric M S)
    (P : Finpartition s) : Symmetric (M.majorityRound P) S := by
  intro a b
  rw [majorityRound_holds_iff, majorityRound_holds_iff]
  have hbox : (fun i ↦ P.part (![a, b] i)) = ![P.part a, P.part b] := by
    ext i; fin_cases i <;> rfl
  have hbox' : (fun i ↦ P.part (![b, a] i)) = ![P.part b, P.part a] := by
    ext i; fin_cases i <;> rfl
  rw [hbox, hbox', tupleCount_swap M S hsym, Fintype.card_piFinset, Fintype.card_piFinset,
    Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Nat.mul_comm]

end RegularityLemmataExamples
