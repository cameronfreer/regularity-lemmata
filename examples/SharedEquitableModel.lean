/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.RelationalApproximation

/-!
# One shared equitable partition and one model for two symbols

A compiled consumer of the composition `exists_equitable_isIndivisibleFor` through the
`RelationalApproximation` facade: from a model `M`, an old partition `P` with a designated (free)
old part, and a requested part count `t`, one equipartition `Q` with exactly `t` parts and **one**
model `N`, indivisible for `Q` and nullary-compatible with `M`, whose edit distance from `M` on a
binary symbol `S₂` and on a ternary symbol `S₃` is bounded **by the same `Q` and `N`**, each at its
own arity: `2·|s|²·(2θ + γ/2 + λ/2) + 2·((K−1)·⌊|s|/t⌋)·|s|` and
`3·|s|³·(2θ + γ/2 + λ/2) + 3·((K−1)·⌊|s|/t⌋)·|s|²`, `K = #P.parts`.

The decency hypotheses are those of `editDistance_majorityRound_le` at `P`, spelled out per symbol
on the ambient off-tuples. Nothing here chooses a language, a model, or a partition.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V}

/-- Decency of `M` at `P` for a symbol of arity `n + 1`, with exceptional parts `E`. -/
def Decent (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ} (S : L.Relations (n + 1))
    (E : Finset (Finset V)) (θ γ : ℝ) : Prop :=
  ∀ (j : Fin (n + 1)), ∀ l ∈ P.parts, l ∉ E →
    (((Fintype.piFinset (fun _ : Fin n ↦ s)).filter fun rest ↦
        InclusiveMixed θ (densityOn l fun a ↦ M.Holds S (Fin.insertNth j a rest))).card : ℝ)
      ≤ γ * (Fintype.piFinset (fun _ : Fin n ↦ s)).card

/-- **Two symbols, one `Q`, one `N`.** -/
theorem exists_shared_equitable_model (M : FiniteRelModel L V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (S₂ : L.Relations 2) (S₃ : L.Relations 3) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (h₂ : Decent M P S₂ E θ γ) (h₃ : Decent M P S₃ E θ γ) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel L V), Q.IsEquipartition ∧ Q.parts.card = t ∧
      N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      (editDistance (M.Holds S₂) (N.Holds S₂) (fun _ : Fin 2 ↦ s) : ℝ)
        ≤ 2 * (s.card : ℝ) ^ 2 * (2 * θ + γ / 2 + lam / 2)
          + 2 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) * s.card ∧
      (editDistance (M.Holds S₃) (N.Holds S₃) (fun _ : Fin 3 ↦ s) : ℝ)
        ≤ 3 * (s.card : ℝ) ^ 3 * (2 * θ + γ / 2 + lam / 2)
          + 3 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) * (s.card : ℝ) ^ 2 := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, hbound⟩ :=
    exists_equitable_isIndivisibleFor M P ht₀ ht hts
  refine ⟨Q, N, hQ, hcard, hind, hnull, ?_, ?_⟩
  · have h := hbound S₂ hθ hγ E hE hlam h₂
    norm_num at h ⊢
    exact h
  · have h := hbound S₃ hθ hγ E hE hlam h₃
    norm_num at h ⊢
    exact h

end RegularityLemmataExamples
