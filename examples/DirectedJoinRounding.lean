/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.RelationalApproximation

/-!
# A directed binary relation rounded at the join of two partitions

A compiled consumer of `exists_isIndivisibleFor_coordinateJoin` through the
`RelationalApproximation` facade at arity `2`: a directed relation `S` on the host `s`, a row
partition `P₁` (coordinate `0`) and a column partition `P₂` (coordinate `1`), rounded at their
join `P₁ ⊓ P₂`. The rounded model is indivisible for `P₁ ⊓ P₂`, which has at most
`#P₁ · #P₂` parts, and the edit distance is at most the **row defects at `P₁`** plus the
**column defects at `P₂`**: `∑_{b ∈ s} partitionDefect P₁ (a ↦ S(a, b))` and
`∑_{a ∈ s} partitionDefect P₂ (b ↦ S(a, b))`, each coordinate measured in its own partition.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- The row defect at `b`: the partition defect of `a ↦ S(a, b)`. -/
noncomputable def rowDefect (M : FiniteRelModel L V) (S : L.Relations 2) (P : Finpartition s)
    (b : V) : ℝ :=
  partitionDefect P fun a ↦ M.Holds S ![a, b]

/-- The column defect at `a`: the partition defect of `b ↦ S(a, b)`. -/
noncomputable def colDefect (M : FiniteRelModel L V) (S : L.Relations 2) (P : Finpartition s)
    (a : V) : ℝ :=
  partitionDefect P fun b ↦ M.Holds S ![a, b]

omit [DecidableEq V] in
private theorem cons_eq_vec (a : V) (rest : Fin 1 → V) : Fin.cons a rest = ![a, rest 0] := by
  ext i; fin_cases i <;> rfl

omit [DecidableEq V] in
private theorem insertNth_one_eq_vec (b : V) (rest : Fin 1 → V) :
    Fin.insertNth (1 : Fin 2) b rest = ![rest 0, b] := by
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.insertNth_last']
  ext i; fin_cases i <;> rfl

/-- The coordinate-`0` family defect over `s^1` is the sum of the row defects. -/
theorem familyDefect_zero_eq_sum_rowDefect (M : FiniteRelModel L V) (S : L.Relations 2)
    (P : Finpartition s) :
    familyDefect P (Fintype.piFinset (fun _ : Fin 1 ↦ s))
        (fun rest a ↦ M.Holds S (Fin.insertNth 0 a rest))
      = ∑ b ∈ s, rowDefect M S P b := by
  unfold familyDefect rowDefect
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

/-- The coordinate-`1` family defect over `s^1` is the sum of the column defects. -/
theorem familyDefect_one_eq_sum_colDefect (M : FiniteRelModel L V) (S : L.Relations 2)
    (P : Finpartition s) :
    familyDefect P (Fintype.piFinset (fun _ : Fin 1 ↦ s))
        (fun rest b ↦ M.Holds S (Fin.insertNth 1 b rest))
      = ∑ a ∈ s, colDefect M S P a := by
  unfold familyDefect colDefect
  refine Finset.sum_nbij' (fun rest ↦ rest 0) (fun a _ ↦ a) ?_ ?_ ?_ ?_ ?_
  · intro rest h; exact Fintype.mem_piFinset.mp h 0
  · intro a ha; exact Fintype.mem_piFinset.mpr fun _ ↦ ha
  · intro rest _; funext i; fin_cases i; rfl
  · intro a _; rfl
  · intro rest _
    congr 1
    ext b
    show M.Holds S (Fin.insertNth 1 b rest) ↔ M.Holds S ![rest 0, b]
    rw [insertNth_one_eq_vec]

/-- **Directed relation, two partitions.** One rounded model, indivisible for `P₁ ⊓ P₂` (at most
`#P₁ · #P₂` parts), nullary-exact, with edit distance at most row defects at `P₁` plus column
defects at `P₂`. -/
theorem exists_directed_rounding (M : FiniteRelModel L V) (S : L.Relations 2)
    (P₁ P₂ : Finpartition s) :
    ∃ N : FiniteRelModel L V, N.IsIndivisibleFor (P₁ ⊓ P₂) ∧ NullaryCompatible M N ∧
      (P₁ ⊓ P₂).parts.card ≤ P₁.parts.card * P₂.parts.card ∧
      (editDistance (M.Holds S) (N.Holds S) (fun _ : Fin 2 ↦ s) : ℝ)
        ≤ ∑ b ∈ s, rowDefect M S P₁ b + ∑ a ∈ s, colDefect M S P₂ a := by
  obtain ⟨N, hind, hnull, hcard, hedit⟩ := exists_isIndivisibleFor_coordinateJoin M ![P₁, P₂] S
  rw [coordinateJoin_two] at hind hcard
  refine ⟨N, hind, hnull, by simpa [Fin.prod_univ_two] using hcard, ?_⟩
  rw [Fin.sum_univ_two] at hedit
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hedit
  rw [familyDefect_zero_eq_sum_rowDefect, familyDefect_one_eq_sum_colDefect] at hedit
  exact hedit

end RegularityLemmataExamples
