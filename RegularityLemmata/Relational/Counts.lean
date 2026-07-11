/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Transport
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Injective

/-!
# Ordered and injective relation counts

Phase 8 unit 4 (design freeze in `ARCHITECTURE.md`): **ordered and injective
counts are separate APIs** — no unqualified "count" names, no silent reuse of
hypergraph semantics.

`relationCountOn` counts satisfying tuples on a heterogeneous box (wrapping the
tuple substrate's `tupleCount`); `relationCount` is the full ordered count over all
tuples `Fin n → V`, **diagonals included** — the canonical first-order count.
`injectiveRelationCount` filters through `injectiveTuples`, and the public
`nonInjectiveRelationCount` is its exact complement:

`relationCount = injectiveRelationCount + nonInjectiveRelationCount`

(`relationCount_eq_injective_add_nonInjective`), from which the collision bound via
Phase 1's `nonInjectiveMaps` follows. Densities: `relationDensity` is normalized by
`|V|^n`, `injectiveRelationDensity` by the falling factorial — never the injective
count by `|V|^n`. Both obey the guard-free `x / 0 = 0` convention.

Permanent tests: the diagonal binary relation on `Fin 2` has ordered count `2` and
injective count `0`; a true nullary relation on the **empty carrier** has both
counts `1`; a false one has both `0`; above the arity bound there is no symbol to
count.
-/

namespace RegularityLemmata

open FirstOrder

namespace FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V W : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Ordered count of satisfying tuples on a heterogeneous box (diagonals
included). -/
def relationCountOn (M : FiniteRelModel L V) {n : ℕ} (R : L.Relations n)
    (A : Fin n → Finset V) : ℕ :=
  tupleCount (M.Holds R) A

/-- **The canonical ordered relation count**: all tuples `Fin n → V`, diagonals
included. -/
def relationCount (M : FiniteRelModel L V) {n : ℕ} (R : L.Relations n) : ℕ :=
  relationCountOn M R fun _ => Finset.univ

/-- The injective relation count: satisfying tuples with pairwise distinct
coordinates. -/
def injectiveRelationCount (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℕ :=
  ((injectiveTuples V n).filter (M.Holds R)).card

/-- The satisfying **noninjective** tuples: the exact complement of the injective
count inside the ordered count. -/
def nonInjectiveRelationCount (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℕ :=
  ((nonInjectiveMaps (Fin n) V).filter (M.Holds R)).card

omit [DecidableEq V] in
theorem relationCount_eq_card_filter_univ (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) :
    relationCount M R = (Finset.univ.filter (M.Holds R)).card := by
  rw [relationCount, relationCountOn, tupleCount, Fintype.piFinset_univ]

/-- **The exact decomposition**: ordered = injective + noninjective. -/
theorem relationCount_eq_injective_add_nonInjective (M : FiniteRelModel L V)
    {n : ℕ} (R : L.Relations n) :
    relationCount M R
      = injectiveRelationCount M R + nonInjectiveRelationCount M R := by
  classical
  rw [relationCount_eq_card_filter_univ, injectiveRelationCount,
    nonInjectiveRelationCount]
  have hinj : (injectiveTuples V n).filter (M.Holds R)
      = (Finset.univ.filter (M.Holds R)).filter Function.Injective := by
    ext f
    simp only [Finset.mem_filter, mem_injectiveTuples, Finset.mem_univ, true_and]
    exact and_comm
  have hninj : (nonInjectiveMaps (Fin n) V).filter (M.Holds R)
      = (Finset.univ.filter (M.Holds R)).filter
          fun f => ¬Function.Injective f := by
    ext f
    simp only [Finset.mem_filter, mem_nonInjectiveMaps, Finset.mem_univ, true_and]
    exact and_comm
  rw [hinj, hninj,
    Finset.card_filter_add_card_filter_not
      (p := fun f : Fin n → V => Function.Injective f)]

/-- The collision bound: ordered count at most injective count plus the total
collision mass (Phase 1). -/
theorem relationCount_le_injective_add_collisions (M : FiniteRelModel L V)
    {n : ℕ} (R : L.Relations n) :
    relationCount M R
      ≤ injectiveRelationCount M R + (nonInjectiveMaps (Fin n) V).card := by
  rw [relationCount_eq_injective_add_nonInjective]
  exact Nat.add_le_add_left (Finset.card_filter_le _ _) _

/-- Ordered and injective counts agree when every satisfying tuple is injective. -/
theorem relationCount_eq_injective_of_forall (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n)
    (h : ∀ x : Fin n → V, M.Holds R x → Function.Injective x) :
    relationCount M R = injectiveRelationCount M R := by
  rw [relationCount_eq_injective_add_nonInjective, nonInjectiveRelationCount]
  rw [Finset.filter_false_of_mem, Finset.card_empty, Nat.add_zero]
  intro f hf hHolds
  rw [mem_nonInjectiveMaps] at hf
  exact hf (h f hHolds)

omit [DecidableEq V] in
theorem relationCount_le_pow (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relationCount M R ≤ Fintype.card V ^ n := by
  rw [relationCount_eq_card_filter_univ]
  refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

theorem injectiveRelationCount_le_descFactorial (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) :
    injectiveRelationCount M R ≤ (Fintype.card V).descFactorial n := by
  rw [← injectiveTupleCount_eq_descFactorial, injectiveTupleCount]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-! ### Densities (separate normalizations, guard-free) -/

/-- Ordered relation density, normalized by `|V|^n`. -/
noncomputable def relationDensity (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℝ :=
  (relationCount M R : ℝ) / (Fintype.card V : ℝ) ^ n

/-- Injective relation density, normalized by the falling factorial — never by
`|V|^n`. -/
noncomputable def injectiveRelationDensity (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : ℝ :=
  (injectiveRelationCount M R : ℝ) / ((Fintype.card V).descFactorial n : ℝ)

omit [DecidableEq V] in
theorem relationDensity_nonneg (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : 0 ≤ relationDensity M R := by
  rw [relationDensity]
  positivity

omit [DecidableEq V] in
theorem relationDensity_le_one (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relationDensity M R ≤ 1 := by
  rw [relationDensity, ← Nat.cast_pow]
  rcases Nat.eq_zero_or_pos (Fintype.card V ^ n) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast relationCount_le_pow M R

theorem injectiveRelationDensity_nonneg (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : 0 ≤ injectiveRelationDensity M R := by
  rw [injectiveRelationDensity]
  positivity

theorem injectiveRelationDensity_le_one (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : injectiveRelationDensity M R ≤ 1 := by
  rw [injectiveRelationDensity]
  rcases Nat.eq_zero_or_pos ((Fintype.card V).descFactorial n) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast injectiveRelationCount_le_descFactorial M R

/-! ### Transport formulas -/

omit [DecidableEq V] [DecidableEq W] in
/-- Relabeling preserves the ordered count. -/
theorem relationCount_relabel (M : FiniteRelModel L V) (e : V ≃ W) {n : ℕ}
    (R : L.Relations n) : relationCount (M.relabel e) R = relationCount M R := by
  classical
  rw [relationCount_eq_card_filter_univ, relationCount_eq_card_filter_univ]
  refine Finset.card_bij' (fun x _ => fun i => e.symm (x i))
    (fun y _ => fun i => e (y i)) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => funext fun i => e.apply_symm_apply (x i))
    (fun y _ => funext fun i => e.symm_apply_apply (y i))
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  · rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    show (M.relabel e).Holds R fun i => e (y i)
    rw [relabel_holds]
    have : (fun i => e.symm (e (y i))) = y := funext fun i => e.symm_apply_apply (y i)
    rw [this]
    exact hy.2

/-- Relabeling preserves the injective count. -/
theorem injectiveRelationCount_relabel (M : FiniteRelModel L V) (e : V ≃ W)
    {n : ℕ} (R : L.Relations n) :
    injectiveRelationCount (M.relabel e) R = injectiveRelationCount M R := by
  classical
  rw [injectiveRelationCount, injectiveRelationCount]
  refine Finset.card_bij' (fun x _ => fun i => e.symm (x i))
    (fun y _ => fun i => e (y i)) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => funext fun i => e.apply_symm_apply (x i))
    (fun y _ => funext fun i => e.symm_apply_apply (y i))
  · rw [Finset.mem_filter, mem_injectiveTuples] at hx ⊢
    exact ⟨e.symm.injective.comp hx.1, hx.2⟩
  · rw [Finset.mem_filter, mem_injectiveTuples] at hy ⊢
    constructor
    · intro i j hij
      exact hy.1 (e.injective hij)
    · show (M.relabel e).Holds R fun i => e (y i)
      rw [relabel_holds]
      have : (fun i => e.symm (e (y i))) = y :=
        funext fun i => e.symm_apply_apply (y i)
      rw [this]
      exact hy.2

omit [Fintype V] [DecidableEq V] in
/-- Restriction counts on the subtype are box counts on the subset. -/
theorem relationCount_restrict (M : FiniteRelModel L V) (S : Finset V) {n : ℕ}
    (R : L.Relations n) :
    relationCount (M.restrict S) R = relationCountOn M R fun _ => S := by
  classical
  rw [relationCount_eq_card_filter_univ, relationCountOn, tupleCount]
  refine Finset.card_bij' (fun x _ => fun i => (x i : V))
    (fun y hy => fun i => ⟨y i, ?_⟩) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => rfl) (fun y _ => rfl)
  · rw [Finset.mem_filter, Fintype.mem_piFinset] at hy
    exact hy.1 i
  · rw [Finset.mem_filter] at hx
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => (x i).2, hx.2⟩
  · rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, hy.2⟩

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- The diagonal binary relation on Fin 2: ordered count 2 (both constant tuples),
-- injective count 0, noninjective count 2, and the decomposition is exact.
example :
    relationCount (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 2) (Fin 2)) (singleRelSymbol 2) = 2 := by
  decide

example :
    injectiveRelationCount (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 2) (Fin 2)) (singleRelSymbol 2) = 0 := by
  decide

example :
    nonInjectiveRelationCount (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 2) (Fin 2)) (singleRelSymbol 2) = 2 := by
  decide

-- A true nullary relation on the EMPTY carrier: ordered and injective counts are
-- both 1 (the single empty tuple, which is injective).
example :
    relationCount (⟨fun {_} _ _ => true⟩ :
      FiniteRelModel (singleRelLang 0) Empty) (singleRelSymbol 0) = 1 := by
  decide

example :
    injectiveRelationCount (⟨fun {_} _ _ => true⟩ :
      FiniteRelModel (singleRelLang 0) Empty) (singleRelSymbol 0) = 1 := by
  decide

-- A false nullary relation has both counts 0.
example :
    relationCount (⟨fun {_} _ _ => false⟩ :
      FiniteRelModel (singleRelLang 0) Empty) (singleRelSymbol 0) = 0 := by
  decide

example :
    injectiveRelationCount (⟨fun {_} _ _ => false⟩ :
      FiniteRelModel (singleRelLang 0) Empty) (singleRelSymbol 0) = 0 := by
  decide

-- Above the arity bound there is no symbol to count.
example : IsEmpty ((singleRelLang 2).Relations 5) :=
  isEmpty_relations_of_lt _ (by decide : arityBound (singleRelLang 2) < 5)

end Tests

end RegularityLemmata
