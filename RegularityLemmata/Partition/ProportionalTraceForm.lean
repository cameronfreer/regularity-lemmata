/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import RegularityLemmata.Partition.SimultaneousSampling
import RegularityLemmata.Partition.TraceComplementClosure

/-!
# The proportional sampling form for traces

The sampling route runs INSIDE each parent cell and only needs, for every trace (test set)
`C` in the complement-closed trace family, an UPPER proportional window
`|C ∩ block| ≤ |C|·s/n + t`: the closure supplies the complement of each trace, so one-sided
control of every closure member yields two-sided control of every raw trace — and downstream
transfer arguments consume exactly the cross-multiplied form `n·|C ∩ B| ≤ s·|C| + ζ·n·s`.

Contents: the specialization of `exists_equiv_forall_blocks_window` to one-sided upper windows
(the lower-violation families are literally empty at `lo = 0`, halving the event count), and
the pure arithmetic bridge from the `ℕ`-division window to the real-valued cross-multiplied
trace estimate.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- At `lo = 0` there are no lower violations. -/
theorem lowerViolations_zero (A : Finset α) (s : ℕ) : lowerViolations A s 0 = ∅ := by
  rw [lowerViolations, Finset.filter_eq_empty_iff]
  intro S _
  omega

/-- **One-sided proportional sampling.**  If the upper-violation total, multiplied by the block
count, is below `C(n, s)`, some equivalence keeps every trace of `F` under its upper window on
every equal block simultaneously.  The lower windows are free (`lo = 0`). -/
theorem exists_equiv_forall_blocks_upper {n s m : ℕ}
    (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hi : Finset α → ℕ)
    (hsum : m * ∑ C ∈ F, (upperViolations C s (hi C)).card < n.choose s) :
    ∃ e : Fin n ≃ α, ∀ C ∈ F, ∀ j, j < m → (C ∩ sampleBlock e s j).card ≤ hi C := by
  have hsum' : m * ∑ C ∈ F,
      ((upperViolations C s (hi C)).card + (lowerViolations C s 0).card) < n.choose s := by
    have : ∀ C ∈ F, (upperViolations C s (hi C)).card + (lowerViolations C s 0).card
        = (upperViolations C s (hi C)).card := by
      intro C _
      rw [lowerViolations_zero, Finset.card_empty, Nat.add_zero]
    rw [Finset.sum_congr rfl this]
    exact hsum
  obtain ⟨e, he⟩ := exists_equiv_forall_blocks_window hn hnm F (fun _ ↦ 0) hi hsum'
  exact ⟨e, fun C hC j hj ↦ (he C hC j hj).2⟩

omit [Fintype α] [DecidableEq α] in
/-- **The cross-multiplied trace estimate.**  The `ℕ`-division upper window
`TB ≤ TA·s/n + t` with slack `t ≤ ζ·s` yields the real-valued form
`n·TB ≤ s·TA + ζ·n·s` consumed by the sampled-line transfer downstream. -/
theorem cross_mul_le_of_upper_window {n s TA TB t : ℕ} {ζ : ℝ}
    (hTB : TB ≤ TA * s / n + t) (ht : (t : ℝ) ≤ ζ * s) :
    (n : ℝ) * TB ≤ (s : ℝ) * TA + ζ * n * s := by
  have hfloor : n * (TA * s / n) ≤ TA * s := by
    rw [mul_comm]
    exact Nat.div_mul_le_self (TA * s) n
  have hnat : n * TB ≤ TA * s + n * t := by
    calc n * TB ≤ n * (TA * s / n + t) := Nat.mul_le_mul_left n hTB
      _ = n * (TA * s / n) + n * t := Nat.mul_add n _ _
      _ ≤ TA * s + n * t := Nat.add_le_add_right hfloor _
  have hcast : (n : ℝ) * TB ≤ (TA : ℝ) * s + (n : ℝ) * t := by
    exact_mod_cast hnat
  have hnt : (n : ℝ) * t ≤ (n : ℝ) * (ζ * s) :=
    mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
  nlinarith

end RegularityLemmata
