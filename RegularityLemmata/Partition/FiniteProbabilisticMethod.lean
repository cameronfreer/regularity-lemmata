/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push

/-!
# Finite probabilistic-method union bound

The deterministic endpoint of the equal-block sampling argument. Once each bad trace/block
event is represented by a finite set of permutations, a sum of their cardinalities strictly
below the permutation-space cardinality produces one permutation avoiding every event.
-/

open Finset

namespace RegularityLemmata

variable {Omega I : Type*} [Fintype Omega] [Fintype I] [DecidableEq Omega]

omit [Fintype Omega] in
/-- The union of all bad events has cardinality at most the sum of their cardinalities. -/
theorem card_biUnion_le_sum_card (bad : I → Finset Omega) :
    (univ.biUnion bad).card ≤ ∑ i : I, (bad i).card := by
  exact card_biUnion_le

/-- If the sum of bad-event cardinalities is smaller than the finite sample space, some outcome
avoids every bad event.  This is the exact finite probabilistic-method step used after the
hypergeometric/permutation concentration estimate. -/
theorem exists_avoids_all_of_sum_card_lt (bad : I → Finset Omega)
    (hbad : ∑ i : I, (bad i).card < Fintype.card Omega) :
    ∃ omega : Omega, ∀ i : I, omega ∉ bad i := by
  have hunion : (univ.biUnion bad).card < Fintype.card Omega :=
    lt_of_le_of_lt (card_biUnion_le_sum_card bad) hbad
  by_contra hnone
  push Not at hnone
  have heq : univ.biUnion bad = (univ : Finset Omega) :=
    eq_univ_of_forall fun omega ↦ by
      obtain ⟨i, hi⟩ := hnone omega
      exact mem_biUnion.mpr ⟨i, mem_univ i, hi⟩
  rw [heq, card_univ] at hunion
  exact (lt_irrefl _ hunion)

/-- Uniform-cardinality corollary: at most `|I|` bad-event families, each of size at most `B`. -/
theorem exists_avoids_all_of_uniform_bound (bad : I → Finset Omega) (B : ℕ)
    (hcard : ∀ i : I, (bad i).card ≤ B)
    (hsmall : Fintype.card I * B < Fintype.card Omega) :
    ∃ omega : Omega, ∀ i : I, omega ∉ bad i := by
  apply exists_avoids_all_of_sum_card_lt bad
  calc
    ∑ i : I, (bad i).card ≤ ∑ _i : I, B := Finset.sum_le_sum fun i _ ↦ hcard i
    _ = Fintype.card I * B := by simp
    _ < Fintype.card Omega := hsmall

end RegularityLemmata
