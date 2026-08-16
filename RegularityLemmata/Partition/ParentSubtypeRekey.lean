/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

/-!
# Exact subtype transport for parent-cell sampling

Sampling runs inside one parent cell `A` at the subtype `↥A`; this module transports traces
(test sets restricted to the cell) and blocks between the ambient carrier and the subtype
LOSSLESSLY: complement correspondence (`traceOnParent_compl`), cardinality nonincrease of the
rekeyed family, and exact intersection-count preservation (`card_inter_traceOnParent`) for
blocks mapped back through the subtype embedding.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-- Restrict an ambient finite set to the subtype carried by a parent cell. -/
def traceOnParent (A T : Finset α) : Finset A := T.subtype (fun x ↦ x ∈ A)

@[simp] theorem mem_traceOnParent (A T : Finset α) (x : A) :
    x ∈ traceOnParent A T ↔ (x : α) ∈ T := by
  simp [traceOnParent]

theorem card_traceOnParent (A T : Finset α) :
    (traceOnParent A T).card = (A ∩ T).card := by
  rw [traceOnParent, Finset.card_subtype]
  congr 1
  ext x
  simp [and_comm]

theorem traceOnParent_compl (A T : Finset α) :
    traceOnParent A (A \ T) = Finset.univ \ traceOnParent A T := by
  ext x
  simp [traceOnParent]

/-- Mapping a sampled subtype block back to the ambient carrier preserves its trace
intersection count exactly. -/
theorem map_inter_traceOnParent (A T : Finset α) (B : Finset A) :
    (B ∩ traceOnParent A T).map (Function.Embedding.subtype _) =
      B.map (Function.Embedding.subtype _) ∩ T := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_map, Finset.mem_inter, mem_traceOnParent] at hx ⊢
    rcases hx with ⟨y, ⟨hyB, hyT⟩, rfl⟩
    exact ⟨⟨y, hyB, rfl⟩, hyT⟩
  · intro hx
    simp only [Finset.mem_inter, Finset.mem_map, mem_traceOnParent] at hx ⊢
    rcases hx with ⟨⟨y, hyB, hyx⟩, hxT⟩
    subst x
    exact ⟨y, ⟨hyB, hxT⟩, rfl⟩

theorem card_inter_traceOnParent (A T : Finset α) (B : Finset A) :
    (B ∩ traceOnParent A T).card =
      (B.map (Function.Embedding.subtype _) ∩ T).card := by
  rw [← map_inter_traceOnParent A T B, Finset.card_map]

/-- Rekey an entire ambient trace family onto the parent subtype. -/
def traceFamilyOnParent (A : Finset α) (F : Finset (Finset α)) : Finset (Finset A) :=
  F.image (traceOnParent A)

theorem card_traceFamilyOnParent_le (A : Finset α) (F : Finset (Finset α)) :
    (traceFamilyOnParent A F).card ≤ F.card := by
  exact Finset.card_image_le

theorem traceOnParent_mem_traceFamilyOnParent (A : Finset α) (F : Finset (Finset α))
    {T : Finset α} (hT : T ∈ F) :
    traceOnParent A T ∈ traceFamilyOnParent A F := by
  exact Finset.mem_image.mpr ⟨T, hT, rfl⟩

end RegularityLemmata
