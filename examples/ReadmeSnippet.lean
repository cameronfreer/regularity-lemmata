/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Kernel

open RegularityLemmata

/-- A real matrix with entries in `[-1, 1]`, indexed by `Fin m × Fin n`, is a sum of at most
`⌈1/ε²⌉₊` weighted submatrix indicators with coefficients of absolute value at most `1/ε`, up to
a residual whose cut norm (the largest absolute submatrix sum) is at most `ε · m · n`. -/
example {m n : ℕ} (M : Fin m → Fin n → ℝ) (hM : ∀ i j, |M i j| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset (Fin m)) (T : Fin k → Finset (Fin n)),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧ (∀ l, |c l| ≤ 1 / ε) ∧ (∀ l, S l ⊆ Finset.univ ∧ T l ⊆ Finset.univ) ∧
      rectCutNorm (fun i j => M i j - rectCombination c S T i j) (fun _ => 1) (fun _ => 1)
          Finset.univ Finset.univ
        ≤ ε * (finsetMass (fun _ : Fin m => (1 : ℝ)) Finset.univ
            * finsetMass (fun _ : Fin n => (1 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition (A := Finset.univ) (B := Finset.univ) M
    (fun _ => 1) (fun _ => 1) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun i _ j _ => hM i j) hε
