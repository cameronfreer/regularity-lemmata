/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Counts
import RegularityLemmata.Relational.BinaryPattern
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

**Count across an edit** (`abs_inducedEmbeddingCountOn_sub_le_editMass`): two models on the
same carrier with nullary agreement have `s`-restricted induced counts of a `k`-vertex pattern
within `Σ_R k^(arity R) · editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) · |s|^(k−1)` of each
other. The coefficient is the atomic-incidence count — `k` and the arity profile together, `k²`
for one binary symbol — not `p(k)`; it consumes the ordered, diagonal-inclusive `s`-box edit
mass, and it needs nullary agreement genuinely (a nullary flip shifts the count by `(|s|)_k`;
the adversarial test below shows the bound failing without it). Full carrier at `s = univ`:
`abs_inducedEmbeddingCount_sub_le_editMass`.
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

theorem injectiveRelationEditCount_comm (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) :
    injectiveRelationEditCount M N R = injectiveRelationEditCount N M R := by
  rw [injectiveRelationEditCount, injectiveRelationEditCount,
    injectiveRelationEditSet, injectiveRelationEditSet]
  refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
  constructor
  · exact fun h hiff => h hiff.symm
  · exact fun h hiff => h hiff.symm

@[simp] theorem injectiveRelationEditCount_self (M : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : injectiveRelationEditCount M M R = 0 := by
  rw [injectiveRelationEditCount, injectiveRelationEditSet, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  exact fun _ _ h => h Iff.rfl

theorem injectiveRelationEditCount_triangle (M N P : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) :
    injectiveRelationEditCount M P R
      ≤ injectiveRelationEditCount M N R + injectiveRelationEditCount N P R := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  rw [injectiveRelationEditSet, Finset.mem_filter] at hx
  rw [Finset.mem_union, injectiveRelationEditSet, injectiveRelationEditSet,
    Finset.mem_filter, Finset.mem_filter]
  by_cases h12 : M.Holds R x ↔ N.Holds R x
  · exact Or.inr ⟨hx.1, fun h23 => hx.2 (h12.trans h23)⟩
  · exact Or.inl ⟨hx.1, h12⟩

theorem relativeInjectiveRelationEdit_nonneg (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : 0 ≤ relativeInjectiveRelationEdit M N R := by
  rw [relativeInjectiveRelationEdit]
  positivity

theorem relativeInjectiveRelationEdit_le_one (M N : FiniteRelModel L V) {n : ℕ}
    (R : L.Relations n) : relativeInjectiveRelationEdit M N R ≤ 1 := by
  rw [relativeInjectiveRelationEdit]
  rcases Nat.eq_zero_or_pos ((Fintype.card V).descFactorial n) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast injectiveRelationEditCount_le_descFactorial M N R

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

/-! ### Count across an edit -/

section EditTransfer

open FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V] {k : ℕ}

/-- **One symbol, one pattern tuple.** The `k`-tuples through `s` whose `x`-atom of the symbol
`S` is edited number at most `|E_S|·|s|^(k−1)`, where `E_S` is the `s`-box edit set of `S`: for
`n ≥ 1` the edited host tuple pins a coordinate (`card_filter_comp_mem_le`); at `n = 0` nullary
agreement makes the edit set empty. This is where the arity-`0` boundary is discharged. -/
private theorem card_filter_comp_mem_editSet_le (M N : FiniteRelModel L V)
    (hnull : NullaryCompatible M N) (s : Finset V) {n : ℕ} (S : L.Relations n)
    (x : Fin n → Fin k) :
    ((Fintype.piFinset fun _ : Fin k => s).filter
        fun f => f ∘ x ∈ editSet (M.Holds S) (N.Holds S) fun _ => s).card
      ≤ editDistance (M.Holds S) (N.Holds S) (fun _ => s) * s.card ^ (k - 1) := by
  classical
  cases n with
  | zero =>
    have hE : editSet (M.Holds S) (N.Holds S) (fun _ : Fin 0 => s) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_editSet] at hy
      apply hy.2
      rw [show y = Fin.elim0 from funext fun i => i.elim0]
      exact hnull S
    simp [hE, editDistance]
  | succ n => exact card_filter_comp_mem_le _ x 0

/-- **Edit transfer, one direction of the symmetric difference.** The tuples through `s` that
are induced embeddings of the pattern into `M` but not into `N` all have an edited atom, so
they are covered by the per-symbol, per-pattern-tuple pinned sets. -/
private theorem card_sdiff_embeddings_le (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V)
    (hnull : NullaryCompatible M N) (s : Finset V) :
    (((Fintype.piFinset fun _ : Fin k => s).filter
          fun f => Function.Injective f ∧ PreservesAndReflects P M f)
        \ ((Fintype.piFinset fun _ : Fin k => s).filter
          fun f => Function.Injective f ∧ PreservesAndReflects P N f)).card
      ≤ ∑ R : RelSymbol L,
          k ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s)
            * s.card ^ (k - 1) := by
  classical
  set box := Fintype.piFinset fun _ : Fin k => s with hbox
  set pinned : RelSymbol L → Finset (Fin k → V) := fun R =>
    (Finset.univ : Finset (Fin (R.1 : ℕ) → Fin k)).biUnion fun x =>
      box.filter fun f => f ∘ x ∈ editSet (M.Holds R.2) (N.Holds R.2) fun _ => s
    with hpinned
  have hcover : (box.filter fun f => Function.Injective f ∧ PreservesAndReflects P M f)
      \ (box.filter fun f => Function.Injective f ∧ PreservesAndReflects P N f)
        ⊆ Finset.univ.biUnion pinned := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨hfbox, hinj, hM⟩, hnot⟩ := hf
    have hN : ¬ PreservesAndReflects P N f := fun h => hnot ⟨hfbox, hinj, h⟩
    simp only [PreservesAndReflects, not_forall] at hN
    obtain ⟨R, x, hRx⟩ := hN
    rw [Finset.mem_biUnion]
    refine ⟨R, Finset.mem_univ _, ?_⟩
    rw [hpinned, Finset.mem_biUnion]
    refine ⟨x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hfbox, ?_⟩⟩
    rw [mem_editSet]
    refine ⟨Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hfbox (x i), fun h => ?_⟩
    exact hRx ((hM R x).trans h)
  calc _ ≤ (Finset.univ.biUnion pinned).card := Finset.card_le_card hcover
    _ ≤ ∑ R : RelSymbol L, (pinned R).card := Finset.card_biUnion_le
    _ ≤ ∑ R : RelSymbol L, ∑ x : Fin (R.1 : ℕ) → Fin k,
          (box.filter fun f => f ∘ x ∈ editSet (M.Holds R.2) (N.Holds R.2) fun _ => s).card :=
        Finset.sum_le_sum fun R _ => Finset.card_biUnion_le
    _ ≤ ∑ R : RelSymbol L, ∑ _x : Fin (R.1 : ℕ) → Fin k,
          editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s) * s.card ^ (k - 1) :=
        Finset.sum_le_sum fun R _ => Finset.sum_le_sum fun x _ =>
          card_filter_comp_mem_editSet_le M N hnull s R.2 x
    _ = ∑ R : RelSymbol L,
          k ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s)
            * s.card ^ (k - 1) := by
        refine Finset.sum_congr rfl fun R _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, smul_eq_mul, mul_assoc]

/-- **Edit transfer.** Two models on the same carrier with nullary agreement have
`s`-restricted induced counts of a `k`-vertex pattern within
`Σ_R k^(arity R) · editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) · |s|^(k−1)` of each other.

The coefficient is the atomic-incidence count `Σ_R k^(arity R)` — induced counting reads every
atom on the pattern's vertices, ordered and diagonal alike, so it depends on `k` **and** on the
language's arity profile (one binary symbol gives `k²`); it is neither `p(k)` nor a function of
`k` alone. Ordered `s`-box edit mass with diagonals included, per `relationEditSet`'s
conventions. Nullary agreement is a genuine hypothesis: a single nullary disagreement can shift
the count by the full `(|s|)_k`, which no bound of this shape absorbs (see the adversarial test).
Guard-free otherwise. Full carrier: `abs_inducedEmbeddingCount_sub_le_editMass`. -/
theorem abs_inducedEmbeddingCountOn_sub_le_editMass (P : FiniteRelModel L (Fin k))
    (M N : FiniteRelModel L V) (hnull : NullaryCompatible M N) (s : Finset V) :
    |(inducedEmbeddingCountOn P M (fun _ : Fin k => s) : ℝ)
        - inducedEmbeddingCountOn P N (fun _ : Fin k => s)|
      ≤ (∑ R : RelSymbol L,
          (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
        * (s.card : ℝ) ^ (k - 1) := by
  classical
  set A := (Fintype.piFinset fun _ : Fin k => s).filter
    fun f => Function.Injective f ∧ PreservesAndReflects P M f with hA
  set B := (Fintype.piFinset fun _ : Fin k => s).filter
    fun f => Function.Injective f ∧ PreservesAndReflects P N f with hB
  have hAB := card_sdiff_embeddings_le P M N hnull s
  have hBA := card_sdiff_embeddings_le P N M (fun S => (hnull S).symm) s
  rw [← hA, ← hB] at hAB
  rw [← hB, ← hA] at hBA
  have hsym : ∀ R : RelSymbol L, editDistance (N.Holds R.2) (M.Holds R.2) (fun _ => s)
      = editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s) := fun R => editDistance_comm
  simp only [hsym] at hBA
  have hbound : (∑ R : RelSymbol L,
        (k : ℝ) ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s))
      * (s.card : ℝ) ^ (k - 1)
      = ((∑ R : RelSymbol L,
          k ^ (R.1 : ℕ) * editDistance (M.Holds R.2) (N.Holds R.2) (fun _ => s)
            * s.card ^ (k - 1) : ℕ) : ℝ) := by
    push_cast
    rw [Finset.sum_mul]
  have hsplitA : A.card = (A \ B).card + (A ∩ B).card := (Finset.card_sdiff_add_card_inter A B).symm
  have hsplitB : B.card = (B \ A).card + (B ∩ A).card := (Finset.card_sdiff_add_card_inter B A).symm
  rw [Finset.inter_comm] at hsplitB
  show |(A.card : ℝ) - B.card| ≤ _
  rw [hbound, abs_sub_le_iff]
  constructor
  · calc (A.card : ℝ) - B.card = ((A \ B).card : ℝ) - (B \ A).card := by
          rw [hsplitA, hsplitB]; push_cast; ring
      _ ≤ ((A \ B).card : ℝ) := by linarith [(Nat.cast_nonneg (B \ A).card : (0 : ℝ) ≤ _)]
      _ ≤ _ := by exact_mod_cast hAB
  · calc (B.card : ℝ) - A.card = ((B \ A).card : ℝ) - (A \ B).card := by
          rw [hsplitA, hsplitB]; push_cast; ring
      _ ≤ ((B \ A).card : ℝ) := by linarith [(Nat.cast_nonneg (A \ B).card : (0 : ℝ) ≤ _)]
      _ ≤ _ := by exact_mod_cast hBA

/-- **Edit transfer on the full carrier**: the `s = univ` specialization, in units of
`relationEditCount` and `|V|^(k−1)`. -/
theorem abs_inducedEmbeddingCount_sub_le_editMass [Fintype V] (P : FiniteRelModel L (Fin k))
    (M N : FiniteRelModel L V) (hnull : NullaryCompatible M N) :
    |(inducedEmbeddingCount P M : ℝ) - inducedEmbeddingCount P N|
      ≤ (∑ R : RelSymbol L, (k : ℝ) ^ (R.1 : ℕ) * relationEditCount M N R.2)
        * (Fintype.card V : ℝ) ^ (k - 1) := by
  have := abs_inducedEmbeddingCountOn_sub_le_editMass P M N hnull Finset.univ
  rwa [inducedEmbeddingCountOn_univ, inducedEmbeddingCountOn_univ, Finset.card_univ] at this

end EditTransfer

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

/-! #### Edit transfer -/

/-- The one binary symbol of `singleRelLang 2`. -/
private abbrev E₂ : (singleRelLang 2).Relations 2 := ()

/-- Every pair related on `Fin 3` (loops included). -/
private def full3 : FiniteRelModel (singleRelLang 2) (Fin 3) := ⟨fun {n} _ _ ↦ decide (n = 2)⟩

/-- `full3` with the single ordered pair `(0, 1)` switched off: edit mass `1`. -/
private def flipped3 : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  ⟨fun {n} _ x ↦ if h : n = 2 then
    decide (¬ (x (Fin.cast h.symm 0) = 0 ∧ x (Fin.cast h.symm 1) = 1)) else false⟩

/-- The two-vertex pattern with every atom true (loops included). -/
private def allAtoms2 : FiniteRelModel (singleRelLang 2) (Fin 2) := ⟨fun {n} _ _ ↦ decide (n = 2)⟩

-- One edited ordered pair costs two induced embeddings (`(0,1)` and `(1,0)` both read the
-- atom), within the bound `k²·1·|V|^(k−1) = 4·1·3 = 12`. The coefficient for one binary symbol
-- is `k² = 4`, not `p(2) = 1`.
example : relationEditCount full3 flipped3 E₂ = 1 := by decide
example : inducedEmbeddingCount allAtoms2 full3 = 6 := by decide
example : inducedEmbeddingCount allAtoms2 flipped3 = 4 := by decide
example : ∑ R : RelSymbol (singleRelLang 2), (2 : ℕ) ^ (R.1 : ℕ) = 4 := by decide
example : |(inducedEmbeddingCount allAtoms2 full3 : ℝ)
      - inducedEmbeddingCount allAtoms2 flipped3|
    ≤ (∑ R : RelSymbol (singleRelLang 2),
        (2 : ℝ) ^ (R.1 : ℕ) * relationEditCount full3 flipped3 R.2)
      * (Fintype.card (Fin 3) : ℝ) ^ (2 - 1) :=
  abs_inducedEmbeddingCount_sub_le_editMass allAtoms2 full3 flipped3 fun R ↦ R.elim

-- **`k = 0` is guard-free**: the empty pattern has one embedding in either model.
private def emptyPattern : FiniteRelModel (singleRelLang 2) (Fin 0) := ⟨fun {_} _ _ ↦ false⟩

example : inducedEmbeddingCount emptyPattern full3 = 1 := by decide
example : |(inducedEmbeddingCount emptyPattern full3 : ℝ)
      - inducedEmbeddingCount emptyPattern flipped3|
    ≤ (∑ R : RelSymbol (singleRelLang 2),
        ((0 : ℕ) : ℝ) ^ (R.1 : ℕ) * relationEditCount full3 flipped3 R.2)
      * (Fintype.card (Fin 3) : ℝ) ^ (0 - 1) :=
  abs_inducedEmbeddingCount_sub_le_editMass (k := 0) emptyPattern full3 flipped3 fun R ↦ R.elim

-- **ADVERSARIAL: nullary agreement is load-bearing.** With one nullary symbol switched from
-- true to false, the edit mass is `1` and the would-be bound `Σ_R 2^0 · 1 · 3^1 = 3`, but the
-- two-vertex pattern reading the nullary atom has `6` embeddings in one model and `0` in the
-- other: the shift is the full `(3)_2 = 6 > 3`. The hypothesis `NullaryCompatible` fails here,
-- so the theorem does not apply — and no bound of its shape could.
private def nullTrue : FiniteRelModel (singleRelLang 0) (Fin 3) := ⟨fun {_} _ _ ↦ true⟩
private def nullFalse : FiniteRelModel (singleRelLang 0) (Fin 3) := ⟨fun {_} _ _ ↦ false⟩
private def nullPattern : FiniteRelModel (singleRelLang 0) (Fin 2) := ⟨fun {_} _ _ ↦ true⟩
/-- The one nullary symbol of `singleRelLang 0`. -/
private abbrev E₀ : (singleRelLang 0).Relations 0 := ()

example : ¬ NullaryCompatible nullTrue nullFalse := fun h ↦ absurd ((h E₀).mp rfl) (by decide)
example : inducedEmbeddingCount nullPattern nullTrue = 6 := by decide
example : inducedEmbeddingCount nullPattern nullFalse = 0 := by decide
example : ∑ R : RelSymbol (singleRelLang 0),
    2 ^ (R.1 : ℕ) * relationEditCount nullTrue nullFalse R.2 * Fintype.card (Fin 3) ^ (2 - 1)
      = 3 := by decide
example : ¬ (6 ≤ 3) := by decide

end Tests

end RegularityLemmata
