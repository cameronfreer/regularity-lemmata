/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Kernel

/-!
# Worked specialization 2: a weighted bipartite graph

A bipartite graph between two vertex classes `U` and `V`, given as a relation `E : U → V → Prop`,
with **nonnegative vertex weights** `wU`, `wV` on the two sides. Its kernel is the relation
indicator `relationKernel E`, the mass of a vertex set is its total weight, and a rectangle sum
`rectSum (relationKernel E) wU wV S T` is the weighted edge count between `S` and `T`. The
decomposition writes the edge indicator as at most `⌈1/ε²⌉₊` weighted complete bipartite pieces
plus a residual whose weighted edge count across every `S ×ˢ T` is within `ε · wU(U) · wV(V)`.

Only the advertised import `RegularityLemmata.Kernel` is used.
-/

namespace RegularityLemmataExamples

open RegularityLemmata

/-- The edge indicator of a weighted bipartite graph decomposes into few weighted complete
bipartite pieces up to a small weighted cut error. -/
theorem weightedBipartiteGraph_cutDecomposition {U V : Type*} [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) [DecidableRel E] (wU : U → ℝ) (wV : V → ℝ) (A : Finset U) (B : Finset V)
    (hwU : ∀ u ∈ A, 0 ≤ wU u) (hwV : ∀ v ∈ B, 0 ≤ wV v) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset U) (T : Fin k → Finset V),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ l, |c l| ≤ 1 / ε) ∧
      (∀ l, S l ⊆ A ∧ T l ⊆ B) ∧
      rectCutNorm (fun u v => relationKernel E u v - rectCombination c S T u v) wU wV A B
        ≤ ε * (finsetMass wU A * finsetMass wV B) :=
  kernel_frieze_kannan_cutDecomposition (relationKernel E) wU wV hwU hwV
    (isAbsUnitBoundedOnRectangle_relationKernel E A B) hε

/-- At unit weights the residual bound is the classical one: every `S ×ˢ T` has weighted edge
count within `ε · |A| · |B|` of its prediction by the pieces. -/
theorem weightedBipartiteGraph_cutDecomposition_unit {U V : Type*} [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) [DecidableRel E] (A : Finset U) (B : Finset V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (S : Fin k → Finset U) (T : Fin k → Finset V),
      k ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ l, |c l| ≤ 1 / ε) ∧
      (∀ l, S l ⊆ A ∧ T l ⊆ B) ∧
      rectCutNorm (fun u v => relationKernel E u v - rectCombination c S T u v)
        (fun _ => 1) (fun _ => 1) A B ≤ ε * (A.card * B.card) := by
  obtain ⟨k, c, S, T, hk, hc, hST, hcut⟩ := weightedBipartiteGraph_cutDecomposition E
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) A B (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) hε
  refine ⟨k, c, S, T, hk, hc, hST, ?_⟩
  simpa [finsetMass] using hcut

end RegularityLemmataExamples
