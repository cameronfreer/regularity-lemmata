/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Injective

/-!
# Extension counts for pattern assignments

An assignment `x : Fin n -> Fin k` fixes every vertex in its image, not just
one vertex. The free exponent is therefore `k - |image x|`. The statement
includes empty assignments and repeated coordinates; no positivity premise is
needed. This is a tuple-counting estimate, not a diagonal-edit bound.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {k n : ℕ}

/-- Pinning all coordinates touched by an assignment saves one power per
distinct image vertex. The existing one-coordinate bound remains unchanged. -/
theorem card_filter_comp_mem_le_image (s : Finset α) (E : Finset (Fin n → α))
    (x : Fin n → Fin k) :
    ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E).card ≤
      E.card * s.card ^ (k - (Finset.univ.image x).card) := by
  classical
  let I := Finset.univ.image x
  let free := {i : Fin k // i ∉ I}
  let event := (Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E
  let box := Fintype.piFinset fun _ : free ↦ s
  let enc : (Fin k → α) → (Fin n → α) × (free → α) :=
    fun f ↦ (f ∘ x, fun i ↦ f i.val)
  have hmaps : Set.MapsTo enc (↑event : Set (Fin k → α)) (↑(E ×ˢ box) :
      Set ((Fin n → α) × (free → α))) := by
    intro f hf
    obtain ⟨hfbox, hfE⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_product.mpr ⟨hfE,
      Fintype.mem_piFinset.mpr fun i ↦ Fintype.mem_piFinset.mp hfbox i.val⟩
  have hinj : Set.InjOn enc event := by
    intro f _ g _ heq
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    funext i
    by_cases hi : i ∈ I
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      subst i
      exact congrFun hfst j
    · exact congrFun hsnd ⟨i, hi⟩
  refine (Finset.card_le_card_of_injOn enc hmaps hinj).trans (le_of_eq ?_)
  rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
  have hc : Fintype.card free = k - I.card := by
    change Fintype.card {i : Fin k // ¬ i ∈ I} = _
    rw [Fintype.card_subtype_compl]
    simp
  rw [hc]

/-- In a non-diagonal assignment all `n` arguments are distinct, giving exponent
`k-n`. This bound itself imposes no simplicity assumption on a relation. -/
theorem card_filter_comp_mem_le_of_injective (s : Finset α) (E : Finset (Fin n → α))
    (x : Fin n → Fin k) (hx : Function.Injective x) :
    ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E).card ≤
      E.card * s.card ^ (k - n) := by
  simpa [Finset.card_image_of_injective _ hx] using card_filter_comp_mem_le_image s E x

/-- Only tuples consistent with the assignment's equalities can occur.
This sharper coefficient exposes contraction-specific edit mass explicitly. -/
theorem card_filter_comp_mem_le_compatible (s : Finset α) (E : Finset (Fin n → α))
    (x : Fin n → Fin k) :
    ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E).card ≤
      (E.filter fun y ↦ ∀ i j, x i = x j → y i = y j).card *
        s.card ^ (k - (Finset.univ.image x).card) := by
  classical
  have heq : ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E) =
      ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦
        f ∘ x ∈ E.filter fun y ↦ ∀ i j, x i = x j → y i = y j) := by
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hf, he⟩
      exact ⟨hf, he, fun i j hij ↦ congrArg f hij⟩
    · rintro ⟨hf, he, _⟩
      exact ⟨hf, he⟩
  rw [heq]
  exact card_filter_comp_mem_le_image s _ x

/-- Union bound over assignments, retaining each equality pattern's own edit
mass and extension exponent. No single-coordinate envelope is introduced. -/
theorem card_filter_exists_comp_mem_le (s : Finset α)
    (E : (Fin n → Fin k) → Finset (Fin n → α)) :
    ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ ∃ x, f ∘ x ∈ E x).card ≤
      ∑ x : Fin n → Fin k,
        ((E x).filter fun y ↦ ∀ i j, x i = x j → y i = y j).card *
          s.card ^ (k - (Finset.univ.image x).card) := by
  classical
  have heq : ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ ∃ x, f ∘ x ∈ E x) =
      Finset.univ.biUnion (fun x : Fin n → Fin k ↦
        (Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E x) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hf, x, hx⟩ ↦ ⟨x, hf, hx⟩, fun ⟨x, hf, hx⟩ ↦ ⟨hf, x, hx⟩⟩
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun x _ ↦ card_filter_comp_mem_le_compatible s (E x) x)

-- Two distinct pinned coordinates leave no free coordinate in a pair.
example : ((Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 3))).filter
    fun f ↦ f ∘ (![0, 1] : Fin 2 → Fin 2) ∈ ({![0, 1]} : Finset (Fin 2 → Fin 3))).card
      = 1 := by decide

-- A repeated coordinate saves just one power, not the arity of the assignment.
example : ((Fintype.piFinset fun _ : Fin 2 ↦ (Finset.univ : Finset (Fin 3))).filter
    fun f ↦ f ∘ (![0, 0] : Fin 2 → Fin 2) ∈ ({![0, 0]} : Finset (Fin 2 → Fin 3))).card
      = 3 := by decide

-- The empty assignment fixes nothing, including on the empty host.
example (s : Finset α) (E : Finset (Fin 0 → α)) :
    ((Fintype.piFinset fun _ : Fin 2 ↦ s).filter fun f ↦ f ∘ Fin.elim0 ∈ E).card ≤
      E.card * s.card ^ 2 := by
  simpa using card_filter_comp_mem_le_image s E (Fin.elim0 : Fin 0 → Fin 2)

end RegularityLemmata

#print axioms RegularityLemmata.card_filter_comp_mem_le_image
#print axioms RegularityLemmata.card_filter_comp_mem_le_of_injective
#print axioms RegularityLemmata.card_filter_comp_mem_le_compatible
#print axioms RegularityLemmata.card_filter_exists_comp_mem_le
