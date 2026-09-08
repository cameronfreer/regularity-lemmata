import RegularityLemmata.Kernel

/-!
# Consumer check: the `Kernel` facade

The three kernel uses a downstream project is expected to make, through the advertised facade
alone: the step-partition summit, the cut-matrix decomposition, and the bridge between their
error measures.
-/

open RegularityLemmata

namespace Consumer

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- The cut-matrix decomposition, consumed as stated. -/
theorem decomposition (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X)
    (B : Finset Y) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y),
      n ≤ ⌈1 / ε ^ 2⌉₊ ∧ (∀ k, |c k| ≤ 1 / ε) ∧ (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧
      rectCutNorm (fun x y => f x y - rectCombination c S T x y) wX wY A B
        ≤ ε * (finsetMass wX A * finsetMass wY B) :=
  kernel_frieze_kannan_cutDecomposition f wX wY hwX hwY hf hε

/-- The two error measures agree on the stepped residual. -/
example (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) {A : Finset X} {B : Finset Y}
    (P : Finpartition A) (Q : Finpartition B) :
    rectCutDiscrepancy f wX wY P Q = rectCutNorm (rectResidual f wX wY P Q) wX wY A B :=
  rectCutDiscrepancy_eq_rectCutNorm_rectResidual f wX wY P Q

end Consumer
