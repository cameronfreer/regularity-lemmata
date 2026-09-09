/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Complement closure of trace families

Simultaneous sampling must control both a raw trace (test set restricted to a cell) and its
complement relative to the parent cell, because the parent line's majority Boolean is chosen
AFTER the trace estimate — controlling only the truth trace is insufficient when the parent
majority is false.  Closing under complements costs at most a factor two; combining finitely
many symbol/coordinate families costs only the sum of their cardinalities.
-/

open Finset

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-- Close a trace family under complements relative to its parent cell. -/
def traceComplementClosure (A : Finset α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F ∪ F.image (fun T ↦ A \ T)

/-- A member `T` of the trace family `F` and its complement `A \ T` relative to the parent
cell `A` both belong to `traceComplementClosure A F`. The parent `A` is the first argument;
no relation between `T` and `A` is assumed (`A \ T` is the relative complement whatever `T`
is). House lemma, no source; consumed by `SliceCert.abs_block_density_sub_le` in
`Partition/BalancedSlicing.lean`. -/
theorem mem_traceComplementClosure (A : Finset α) (F : Finset (Finset α))
    {T : Finset α} (hT : T ∈ F) :
    T ∈ traceComplementClosure A F ∧ A \ T ∈ traceComplementClosure A F := by
  constructor
  · exact Finset.mem_union_left _ hT
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)

/-- Closing a trace family under complements at most doubles its size:
`|traceComplementClosure A F| ≤ 2 * |F|`. Coarse: the factor `2` is the union bound on
`F ∪ image (A \ ·) F`, with no credit for families already closed under complements or for
traces whose complements coincide. House lemma, no source; consumed by
`card_biUnion_traceClosure_le` below and by `exists_balanced_slicing` in
`Partition/BalancedSlicing.lean`. -/
theorem card_traceComplementClosure_le (A : Finset α) (F : Finset (Finset α)) :
    (traceComplementClosure A F).card ≤ 2 * F.card := by
  calc
    (traceComplementClosure A F).card
        ≤ F.card + (F.image (fun T ↦ A \ T)).card := by
      simpa only [traceComplementClosure] using
        Finset.card_union_le F (F.image fun T ↦ A \ T)
    _ ≤ F.card + F.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * F.card := by omega

/-- A finite union of complement-closed trace families costs at most the sum of the doubled
individual sizes. -/
theorem card_biUnion_traceClosure_le {I : Type*} [DecidableEq I]
    (labels : Finset I) (A : Finset α) (F : I → Finset (Finset α)) :
    (labels.biUnion fun i ↦ traceComplementClosure A (F i)).card
      ≤ ∑ i ∈ labels, 2 * (F i).card := by
  calc
    (labels.biUnion fun i ↦ traceComplementClosure A (F i)).card
        ≤ ∑ i ∈ labels, (traceComplementClosure A (F i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ labels, 2 * (F i).card :=
      Finset.sum_le_sum fun i _ ↦ card_traceComplementClosure_le A (F i)

end RegularityLemmata
