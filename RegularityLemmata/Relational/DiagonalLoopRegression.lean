/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.PatternCounts

/-!
# Named diagonal-loop regression

Adding only loops changes induced embeddings of a simple pattern, but not its
injective preservation-only count. These are the existing model-level counts,
not substitute counting definitions. The small finite instance is kernel-checked.
-/

namespace RegularityLemmata.DiagonalLoopRegression

open FirstOrder FiniteRelModel

def language : Language.{0, 0} := ⟨fun _ ↦ Empty, fun n ↦ if n = 2 then Unit else Empty⟩

instance : FiniteRelational language where
  arityBound := 2
  functionsEmpty := fun _ ↦ inferInstanceAs (IsEmpty Empty)
  relationsFintype := fun n ↦ by
    by_cases h : n = 2 <;> simp only [language, h, ite_true, ite_false] <;> infer_instance
  relationsDecidableEq := fun n ↦ by
    by_cases h : n = 2 <;> simp only [language, h, ite_true, ite_false] <;> infer_instance
  relationsEmptyAbove := fun n hn ↦ by
    have h : n ≠ 2 := by omega
    simp only [language, h, ite_false]
    infer_instance

/-- Complete binary relation, optionally including loops. -/
def complete (n : ℕ) (loops : Bool) : FiniteRelModel language (Fin n) where
  rel := fun {r} _ x ↦ match r, x with
    | 2, x => loops || decide (x 0 ≠ x 1)
    | _, _ => false

/-- The two models agree on every off-diagonal binary tuple. -/
theorem offDiagonal_agreement (n : ℕ) (x : Fin 2 → Fin n) (hx : x 0 ≠ x 1) :
    (complete n false).Holds (n := 2) () x ↔ (complete n true).Holds (n := 2) () x := by
  change (false || decide (x 0 ≠ x 1)) = true ↔ (true || decide (x 0 ≠ x 1)) = true
  simp [hx]

/-- The irreflexive two-vertex pattern has six induced embeddings into the
irreflexive three-vertex complete relation, and none after only loops are added. -/
theorem induced_count_changes_on_loops :
    inducedEmbeddingCount (complete 2 false) (complete 3 false) = 6 ∧
      inducedEmbeddingCount (complete 2 false) (complete 3 true) = 0 := by decide

/-- Injective homomorphisms do not test the pattern's absent loops. -/
theorem injective_hom_count_ignores_added_loops :
    injectiveHomCount (complete 2 false) (complete 3 false) = 6 ∧
      injectiveHomCount (complete 2 false) (complete 3 true) = 6 := by decide

/-- All homomorphisms may change through collisions; here the three constant
maps are added, exactly the two-vertex collision charge. -/
theorem hom_count_collision_difference :
    homCount (complete 2 false) (complete 3 false) = 6 ∧
      homCount (complete 2 false) (complete 3 true) = 9 := by decide

end RegularityLemmata.DiagonalLoopRegression

#print axioms RegularityLemmata.DiagonalLoopRegression.induced_count_changes_on_loops
#print axioms RegularityLemmata.DiagonalLoopRegression.injective_hom_count_ignores_added_loops
#print axioms RegularityLemmata.DiagonalLoopRegression.hom_count_collision_difference
