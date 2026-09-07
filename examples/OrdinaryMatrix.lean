/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Kernel

/-!
# Worked specialization 1: an ordinary matrix

A real matrix with entries in `[-1, 1]`, indexed by `Fin m × Fin n`, is a rectangular kernel at
**unit carrier weights**; its total mass is `m · n`, a rectangle's mass is its number of cells,
and the cut norm is the classical one — the largest absolute sum over a submatrix `S ×ˢ T`.
The cut-matrix decomposition then reads exactly as in Frieze–Kannan: at most `⌈1/ε²⌉₊` cut
matrices `cₖ · 𝟙_{Sₖ} ⊗ 𝟙_{Tₖ}` with `|cₖ| ≤ 1/ε`, leaving a residual whose every submatrix sum is
at most `ε · m · n` in absolute value.

Only the advertised import `RegularityLemmata.Kernel` is used.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

/-- A matrix as a kernel: entries in `[-1, 1]`, unit weights. -/
theorem ordinaryMatrix_cutDecomposition {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset (Fin m)) (T : Fin k → Finset (Fin n)),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ l, |c l| ≤ 1 / ε) ∧
      (∀ l, S l ⊆ Finset.univ ∧ T l ⊆ Finset.univ) ∧
      -- every submatrix sum of the residual is at most `ε · m · n`
      ∀ S' ⊆ (Finset.univ : Finset (Fin m)), ∀ T' ⊆ (Finset.univ : Finset (Fin n)),
        |∑ i ∈ S', ∑ j ∈ T', (M i j - rectCombination c S T i j)| ≤ ε * (m * n) := by
  obtain ⟨k, c, S, T, hk, hc, hST, hcut⟩ :=
    kernel_frieze_kannan_cutDecomposition (A := Finset.univ) (B := Finset.univ) M
      (fun _ => 1) (fun _ => 1) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
      (fun i _ j _ => hM i j) hε
  refine ⟨k, c, S, T, hk, hc, hST, fun S' hS' T' hT' => ?_⟩
  have h := rectCutNorm_le_iff.mp hcut S' hS' T' hT'
  simp only [rectSum, one_mul, finsetMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  exact h

end RegularityLemmataExamples
