/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPalette
import RegularityLemmata.Partition.Basic

/-!
# The vertex-profile partition

Phase 9 unit 2 (design freeze in `ARCHITECTURE.md`): the partition of a finite
vertex set by equality of `binaryVertexProfile` — atomizing every unary relation
and every binary loop into cells, via mathlib's `Finpartition.ofSetSetoid`.

Members of one cell share their profile (`binaryVertexProfile_eq_of_mem_part`), so
every unary relation (`unary_const_on_part`) and every binary loop
(`loop_const_on_part`) is constant on a cell. The cell count is at most
`2^(#unary + #binary)` (`card_parts_binaryProfilePartition_le`). The named common
refinement `refineByBinaryProfile P = P ⊓ binaryProfilePartition M s` refines both
`P` and the profile partition, with at most `#P.parts · 2^(#unary + #binary)` cells
(`card_parts_refineByBinaryProfile_le`) — the summit consumes this without exposing
lattice plumbing.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}

instance : DecidableEq (BinaryVertexProfile L) :=
  inferInstanceAs (DecidableEq ((L.Relations 1 → Bool) × (L.Relations 2 → Bool)))

/-- The setoid identifying vertices with equal binary profiles. -/
def binaryProfileSetoid (M : FiniteRelModel L V) : Setoid V where
  r a b := binaryVertexProfile M a = binaryVertexProfile M b
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

instance (M : FiniteRelModel L V) : DecidableRel (binaryProfileSetoid M).r :=
  fun a b => inferInstanceAs (Decidable (binaryVertexProfile M a = binaryVertexProfile M b))

variable [DecidableEq V]

/-- The partition of `s` by binary vertex profile. -/
def binaryProfilePartition (M : FiniteRelModel L V) (s : Finset V) : Finpartition s :=
  Finpartition.ofSetSetoid (binaryProfileSetoid M) s

theorem binaryProfilePartition_parts (M : FiniteRelModel L V) (s : Finset V) :
    (binaryProfilePartition M s).parts
      = s.image fun a => {b ∈ s | binaryVertexProfile M a = binaryVertexProfile M b} := by
  rw [binaryProfilePartition, Finpartition.ofSetSetoid_parts]
  rfl

/-- Members of one cell share their profile. -/
theorem binaryVertexProfile_eq_of_mem_part (M : FiniteRelModel L V) {s : Finset V}
    {t : Finset V} (ht : t ∈ (binaryProfilePartition M s).parts) {a b : V}
    (ha : a ∈ t) (hb : b ∈ t) :
    binaryVertexProfile M a = binaryVertexProfile M b := by
  rw [binaryProfilePartition_parts, Finset.mem_image] at ht
  obtain ⟨c, _, rfl⟩ := ht
  rw [Finset.mem_filter] at ha hb
  exact ha.2.symm.trans hb.2

/-- Every unary relation is constant on a cell. -/
theorem unary_const_on_part (M : FiniteRelModel L V) {s : Finset V} {t : Finset V}
    (ht : t ∈ (binaryProfilePartition M s).parts) (U : L.Relations 1) {a b : V}
    (ha : a ∈ t) (hb : b ∈ t) : M.rel U ![a] = M.rel U ![b] :=
  congrFun (congrArg Prod.fst (binaryVertexProfile_eq_of_mem_part M ht ha hb)) U

/-- Every binary loop is constant on a cell. -/
theorem loop_const_on_part (M : FiniteRelModel L V) {s : Finset V} {t : Finset V}
    (ht : t ∈ (binaryProfilePartition M s).parts) (R : L.Relations 2) {a b : V}
    (ha : a ∈ t) (hb : b ∈ t) : M.rel R ![a, a] = M.rel R ![b, b] :=
  congrFun (congrArg Prod.snd (binaryVertexProfile_eq_of_mem_part M ht ha hb)) R

/-- At most `2^(#unary + #binary)` cells. -/
theorem card_parts_binaryProfilePartition_le (M : FiniteRelModel L V) (s : Finset V) :
    (binaryProfilePartition M s).parts.card ≤ Fintype.card (BinaryVertexProfile L) := by
  rw [binaryProfilePartition_parts]
  have hfactor : (s.image fun a =>
        {b ∈ s | binaryVertexProfile M a = binaryVertexProfile M b})
      = (s.image (binaryVertexProfile M)).image
          fun F => {b ∈ s | F = binaryVertexProfile M b} := by
    rw [Finset.image_image]
    exact Finset.image_congr fun a _ => rfl
  rw [hfactor]
  exact le_trans Finset.card_image_le (Finset.card_le_univ _)

/-! ### The named common refinement -/

/-- The common refinement of `P` with the vertex-profile partition. -/
def refineByBinaryProfile (M : FiniteRelModel L V) {s : Finset V} (P : Finpartition s) :
    Finpartition s :=
  P ⊓ binaryProfilePartition M s

theorem refineByBinaryProfile_le (M : FiniteRelModel L V) {s : Finset V}
    (P : Finpartition s) : refineByBinaryProfile M P ≤ P :=
  inf_le_left

theorem refineByBinaryProfile_le_profile (M : FiniteRelModel L V) {s : Finset V}
    (P : Finpartition s) : refineByBinaryProfile M P ≤ binaryProfilePartition M s :=
  inf_le_right

theorem card_parts_refineByBinaryProfile_le (M : FiniteRelModel L V) {s : Finset V}
    (P : Finpartition s) :
    (refineByBinaryProfile M P).parts.card
      ≤ P.parts.card * Fintype.card (BinaryVertexProfile L) :=
  le_trans (card_parts_inf_le P _)
    (Nat.mul_le_mul (le_refl _) (card_parts_binaryProfilePartition_le M s))

/-! ### Tests and adversarial examples -/

section Tests

/-- A one-unary-symbol test model. -/
private def unaryModel {V : Type*} (p : V → Bool) :
    FiniteRelModel (singleRelLang 1) V :=
  ⟨fun {n} _ x => if h : n = 1 then p (x (Fin.cast h.symm 0)) else false⟩

/-- A one-binary-symbol test model. -/
private def loopModel {V : Type*} [DecidableEq V] (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- Different unary colors put vertices in different profile cells.
example :
    binaryVertexProfile (unaryModel (V := Fin 2) fun v => decide (v = 0)) 0
      ≠ binaryVertexProfile (unaryModel (V := Fin 2) fun v => decide (v = 0)) 1 := by
  decide

-- Different loop values split even when the off-diagonal data agrees (here both
-- are false off the diagonal).
example :
    binaryVertexProfile (loopModel (V := Fin 2) fun a b => decide (a = b)) 0
      ≠ binaryVertexProfile (loopModel (V := Fin 2) fun _ _ => false) 0 := by
  decide

-- Empty language: the profile partition of a nonempty host has one cell.
example :
    (binaryProfilePartition (⟨fun {_} R _ => R.elim⟩ :
        FiniteRelModel FirstOrder.Language.empty (Fin 3))
      Finset.univ).parts.card = 1 := by
  decide

-- Empty host: the profile partition is empty.
example :
    (binaryProfilePartition (unaryModel (V := Fin 2) fun _ => true) ∅).parts.card
      = 0 := by
  decide

end Tests

end RegularityLemmata
