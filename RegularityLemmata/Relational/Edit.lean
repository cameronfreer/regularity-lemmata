/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Counts
import RegularityLemmata.Finite.Edit

/-!
# Per-symbol and aggregate edit calculus

Phase 8 unit 5 (design freeze in `ARCHITECTURE.md`): **per-symbol edits are
primitive**, reusing the finite edit substrate (`Finite/Edit.lean`, house
`¬(P ↔ Q)` disagreement form). The full per-symbol count includes diagonals and is
normalized by `|V|^n`; the injective version by the falling factorial — with the
exact ordered = injective + noninjective split and the collision bound.

Only then is the aggregate defined, with the **frozen cross-arity weighting**:
every symbol–tuple incidence has weight one —

`aggregateEditCount = Σ_{s : RelSymbol L} relationEditCount M N s.2`,
`aggregateTupleBudget = Σ_{s : RelSymbol L} |V|^(arity s)`,
`relativeAggregateEdit = count / budget` (guard-free).

The aggregate is **not** normalized by `|V|^arityBound` and the per-symbol relative
edits are **not** averaged — those conventions behave differently across arities.
Nullary symbols contribute budget `1` even on an empty carrier; the zero-symbol
language (`FirstOrder.Language.empty`) has count, budget, and relative edit all
zero — both are permanent tests.
-/

namespace RegularityLemmata

open FirstOrder

namespace FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}
  [Fintype V] [DecidableEq V]

/-! ### Per-symbol edits (primitive) -/

/-- The tuples on which two models disagree about `R` (diagonals included). -/
def relationEditSet (M N : FiniteRelModel L V) {n : ℕ} (R : L.Relations n) :
    Finset (Fin n → V) :=
  editSet (M.Holds R) (N.Holds R) fun _ => Finset.univ

/-- The full per-symbol edit count (diagonals included). -/
def relationEditCount (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℕ :=
  editDistance (M.Holds R) (N.Holds R) fun _ => Finset.univ

/-- Relative per-symbol edit, normalized by `|V|^n` (guard-free). -/
noncomputable def relativeRelationEdit (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℝ :=
  (relationEditCount M N R : ℝ) / (Fintype.card V : ℝ) ^ n

/-- The injective disagreement set. -/
def injectiveRelationEditSet (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : Finset (Fin n → V) :=
  (injectiveTuples V n).filter fun x => ¬(M.Holds R x ↔ N.Holds R x)

/-- The injective per-symbol edit count. -/
def injectiveRelationEditCount (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℕ :=
  (injectiveRelationEditSet M N R).card

/-- Relative injective per-symbol edit, normalized by the falling factorial. -/
noncomputable def relativeInjectiveRelationEdit (M N : FiniteRelModel L V)
    {n : ℕ} (R : L.Relations n) : ℝ :=
  (injectiveRelationEditCount M N R : ℝ) / ((Fintype.card V).descFactorial n : ℝ)

omit [DecidableEq V] in
theorem relationEditCount_comm (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relationEditCount M N R = relationEditCount N M R :=
  editDistance_comm

omit [DecidableEq V] in
@[simp] theorem relationEditCount_self (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relationEditCount M M R = 0 :=
  editDistance_self

omit [DecidableEq V] in
theorem relationEditCount_triangle (M N P : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) :
    relationEditCount M P R
      ≤ relationEditCount M N R + relationEditCount N P R :=
  editDistance_triangle

omit [DecidableEq V] in
theorem relationEditCount_le_pow (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relationEditCount M N R ≤ Fintype.card V ^ n := by
  refine le_trans editDistance_le_card (le_of_eq ?_)
  rw [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

theorem injectiveRelationEditCount_le_descFactorial (M N : FiniteRelModel L V)
    {n : ℕ} (R : L.Relations n) :
    injectiveRelationEditCount M N R ≤ (Fintype.card V).descFactorial n := by
  rw [← injectiveTupleCount_eq_descFactorial, injectiveTupleCount,
    injectiveRelationEditCount, injectiveRelationEditSet]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Exact split of the per-symbol edit count by injectivity. -/
theorem relationEditCount_eq_injective_add_nonInjective
    (M N : FiniteRelModel L V) {n : ℕ} (R : L.Relations n) :
    relationEditCount M N R
      = injectiveRelationEditCount M N R
        + ((nonInjectiveMaps (Fin n) V).filter
            fun x => ¬(M.Holds R x ↔ N.Holds R x)).card := by
  classical
  rw [relationEditCount, editDistance, editSet, Fintype.piFinset_univ,
    injectiveRelationEditCount, injectiveRelationEditSet]
  have hinj : (injectiveTuples V n).filter
        (fun x => ¬(M.Holds R x ↔ N.Holds R x))
      = (Finset.univ.filter fun x => ¬(M.Holds R x ↔ N.Holds R x)).filter
          Function.Injective := by
    ext f
    simp only [Finset.mem_filter, mem_injectiveTuples, Finset.mem_univ, true_and]
    exact and_comm
  have hninj : (nonInjectiveMaps (Fin n) V).filter
        (fun x => ¬(M.Holds R x ↔ N.Holds R x))
      = (Finset.univ.filter fun x => ¬(M.Holds R x ↔ N.Holds R x)).filter
          fun f => ¬Function.Injective f := by
    ext f
    simp only [Finset.mem_filter, mem_nonInjectiveMaps, Finset.mem_univ, true_and]
    exact and_comm
  rw [hinj, hninj,
    Finset.card_filter_add_card_filter_not
      (p := fun f : Fin n → V => Function.Injective f)]

/-- The collision comparison. -/
theorem relationEditCount_le_injective_add_collisions
    (M N : FiniteRelModel L V) {n : ℕ} (R : L.Relations n) :
    relationEditCount M N R
      ≤ injectiveRelationEditCount M N R + (nonInjectiveMaps (Fin n) V).card := by
  rw [relationEditCount_eq_injective_add_nonInjective]
  exact Nat.add_le_add_left (Finset.card_filter_le _ _) _

omit [DecidableEq V] in
theorem relativeRelationEdit_nonneg (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : 0 ≤ relativeRelationEdit M N R := by
  rw [relativeRelationEdit]
  positivity

omit [DecidableEq V] in
theorem relativeRelationEdit_le_one (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relativeRelationEdit M N R ≤ 1 := by
  rw [relativeRelationEdit, ← Nat.cast_pow]
  rcases Nat.eq_zero_or_pos (Fintype.card V ^ n) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast relationEditCount_le_pow M N R

/-! ### The aggregate (defined only after the per-symbol API) -/

/-- Aggregate edit count: one unit per symbol–tuple disagreement (the frozen
cross-arity weighting). -/
def aggregateEditCount (M N : FiniteRelModel L V) : ℕ :=
  ∑ s : RelSymbol L, relationEditCount M N s.2

/-- The aggregate tuple budget: one unit per symbol–tuple incidence. -/
def aggregateTupleBudget (L : FirstOrder.Language) [FiniteRelational L]
    (V : Type*) [Fintype V] : ℕ :=
  ∑ s : RelSymbol L, Fintype.card V ^ (s.1 : ℕ)

/-- Relative aggregate edit (guard-free). NOT normalized by `|V|^arityBound`, and
NOT an average of per-symbol relative edits. -/
noncomputable def relativeAggregateEdit (M N : FiniteRelModel L V) : ℝ :=
  (aggregateEditCount M N : ℝ) / (aggregateTupleBudget L V : ℝ)

omit [DecidableEq V] in
theorem aggregateEditCount_le_budget (M N : FiniteRelModel L V) :
    aggregateEditCount M N ≤ aggregateTupleBudget L V :=
  Finset.sum_le_sum fun s _ => relationEditCount_le_pow M N s.2

omit [DecidableEq V] in
theorem aggregateEditCount_comm (M N : FiniteRelModel L V) :
    aggregateEditCount M N = aggregateEditCount N M :=
  Finset.sum_congr rfl fun s _ => relationEditCount_comm M N s.2

omit [DecidableEq V] in
@[simp] theorem aggregateEditCount_self (M : FiniteRelModel L V) :
    aggregateEditCount M M = 0 :=
  Finset.sum_eq_zero fun s _ => relationEditCount_self M s.2

omit [DecidableEq V] in
theorem aggregateEditCount_triangle (M N P : FiniteRelModel L V) :
    aggregateEditCount M P ≤ aggregateEditCount M N + aggregateEditCount N P := by
  rw [aggregateEditCount, aggregateEditCount, aggregateEditCount,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun s _ => relationEditCount_triangle M N P s.2

omit [DecidableEq V] in
/-- The aggregate vanishes exactly when every per-symbol edit vanishes. -/
theorem aggregateEditCount_eq_zero_iff (M N : FiniteRelModel L V) :
    aggregateEditCount M N = 0
      ↔ ∀ s : RelSymbol L, relationEditCount M N s.2 = 0 := by
  rw [aggregateEditCount, Finset.sum_eq_zero_iff]
  exact ⟨fun h s => h s (Finset.mem_univ s), fun h s _ => h s⟩

omit [DecidableEq V] in
theorem relativeAggregateEdit_nonneg (M N : FiniteRelModel L V) :
    0 ≤ relativeAggregateEdit M N := by
  rw [relativeAggregateEdit]
  positivity

omit [DecidableEq V] in
theorem relativeAggregateEdit_le_one (M N : FiniteRelModel L V) :
    relativeAggregateEdit M N ≤ 1 := by
  rw [relativeAggregateEdit]
  rcases Nat.eq_zero_or_pos (aggregateTupleBudget L V) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast aggregateEditCount_le_budget M N

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- The zero-symbol language: aggregate count, budget, and relative edit all zero.
example (M N : FiniteRelModel FirstOrder.Language.empty (Fin 3)) :
    aggregateEditCount M N = 0 := by
  haveI : IsEmpty (RelSymbol FirstOrder.Language.empty) := ⟨fun s => s.2.elim⟩
  rw [aggregateEditCount, Finset.univ_eq_empty, Finset.sum_empty]

example : aggregateTupleBudget FirstOrder.Language.empty (Fin 3) = 0 := by decide

example (M N : FiniteRelModel FirstOrder.Language.empty (Fin 3)) :
    relativeAggregateEdit M N = 0 := by
  haveI : IsEmpty (RelSymbol FirstOrder.Language.empty) := ⟨fun s => s.2.elim⟩
  rw [relativeAggregateEdit,
    show aggregateEditCount M N = 0 from by
      rw [aggregateEditCount, Finset.univ_eq_empty, Finset.sum_empty]]
  norm_num

-- Nullary symbols contribute budget one, even on the EMPTY carrier.
example : aggregateTupleBudget (singleRelLang 0) Empty = 1 := by decide

-- A concrete per-symbol edit: the diagonal model vs the constantly false model
-- disagree exactly on the 2 constant tuples of Fin 2; the injective edit count is
-- 0 and the split is exact.
example :
    relationEditCount
      (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 2))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 2) (Fin 2))
      (singleRelSymbol 2) = 2 := by decide

example :
    injectiveRelationEditCount
      (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 2))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 2) (Fin 2))
      (singleRelSymbol 2) = 0 := by decide

-- Aggregate = per-symbol for the one-symbol language (weight-one incidences).
example :
    aggregateEditCount
      (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 2))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 2) (Fin 2)) = 2 := by
  decide

end Tests

end RegularityLemmata
