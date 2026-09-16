/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.MajorityAssembly

/-!
# Ternary majority rounding: a compiled consumer

The majority-rounding cost theorem `editDistance_majorityRound_le` instantiated at a ternary
symbol, with the arity-generic constant `(n + 1) · |s|^(n+1)` read off as `3 · |s|³`, together
with the pieces a consumer touches on the way: the ternary decency hypothesis spelled out on the
ambient off-pairs `s²`, the box-level identity (edit distance to the majority equals the minority
count on every cell box), the no-exceptional-part specialization, and the nullary copy.

Everything below is a statement-level instantiation of proved results; no choice of language,
model, or partition is made here.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- Ternary decency: for every coordinate `j : Fin 3` and every ordinary part `l ∉ E`, at most a
`γ`-fraction of the ambient off-pairs `rest ∈ s²` have an inclusively `θ`-mixed section
`a ↦ S (insertNth j a rest)` on `l`. -/
def TernaryDecent (M : FiniteRelModel L V) (P : Finpartition s) (S : L.Relations 3)
    (E : Finset (Finset V)) (θ γ : ℝ) : Prop :=
  ∀ j : Fin 3, ∀ l ∈ P.parts, l ∉ E →
    (((Fintype.piFinset (fun _ : Fin 2 ↦ s)).filter fun rest ↦
        InclusiveMixed θ (densityOn l fun a ↦ M.Holds S (Fin.insertNth j a rest))).card : ℝ)
      ≤ γ * (Fintype.piFinset (fun _ : Fin 2 ↦ s)).card

/-- **Ternary majority rounding.** Exceptional parts of total size at most `λ·|s|` and ternary
decency give edit distance at most `3 · |s|³ · (2θ + γ/2 + λ/2)`. -/
theorem ternary_editDistance_majorityRound_le (M : FiniteRelModel L V) (P : Finpartition s)
    (S : L.Relations 3) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (E : Finset (Finset V))
    (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : TernaryDecent M P S E θ γ) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 3 ↦ s) : ℝ)
      ≤ 3 * (s.card : ℝ) ^ 3 * (2 * θ + γ / 2 + lam / 2) := by
  have h := editDistance_majorityRound_le M P S hθ hγ E hE hlam hdec
  norm_num at h
  exact h

/-- Without exceptional parts (`E = ∅`, `λ = 0`) the bound is `3 · |s|³ · (2θ + γ/2)`. -/
theorem ternary_editDistance_majorityRound_le_of_decent (M : FiniteRelModel L V)
    (P : Finpartition s) (S : L.Relations 3) {θ γ : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
    (hdec : TernaryDecent M P S ∅ θ γ) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 3 ↦ s) : ℝ)
      ≤ 3 * (s.card : ℝ) ^ 3 * (2 * θ + γ / 2) := by
  have h := ternary_editDistance_majorityRound_le M P S hθ hγ ∅ (Finset.empty_subset _)
    (lam := 0) (by simp) hdec
  simpa using h

/-- **Box level, ternary.** On every cell box the edit distance to the majority rounding is the
minority count of the box, an exact `ℕ` identity. -/
example (M : FiniteRelModel L V) (P : Finpartition s) (S : L.Relations 3)
    (C : Fin 3 → Finset V) (hC : ∀ i, C i ∈ P.parts) :
    editDistance (M.Holds S) ((M.majorityRound P).Holds S) C = minorityCount (M.Holds S) C :=
  editDistance_majorityRound_eq_minorityCount M P S C hC

/-- **Global bound before decency**: the edit distance is at most the summed part-resampling
defects over the three coordinates and all ambient triples. -/
example (M : FiniteRelModel L V) (P : Finpartition s) (S : L.Relations 3) :
    (editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 3 ↦ s) : ℝ)
      ≤ ∑ j : Fin 3, ∑ w ∈ Fintype.piFinset (fun _ : Fin 3 ↦ s),
          partResampleDefect (M.Holds S) P j w :=
  editDistance_majorityRound_le_sum_partResampleDefect M P S

/-- Nullary symbols are copied exactly. -/
example (M : FiniteRelModel L V) (P : Finpartition s) (S : L.Relations 0) :
    editDistance (M.Holds S) ((M.majorityRound P).Holds S) (fun _ : Fin 0 ↦ s) = 0 :=
  editDistance_majorityRound_nullary M P S

end RegularityLemmataExamples
