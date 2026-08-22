/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.HomogeneousPair
import RegularityLemmata.Partition.Basic

/-!
# Homogeneity of a partition pair

A pair of partitions is `ε`-homogeneous for `R` when **every** cell rectangle is: the
cellwise lift of `IsHomogeneousPair` to independent partitions of two heterogeneous carriers.

## One tolerance, not two

The tolerance is a single scalar. Homogeneity measures one rectangle density, so there is one
output tolerance; side asymmetry belongs in the *inputs* of a perturbation result, where the
degradation `cX + cY + 2·cX·cY` of `abs_pairDensity_sub_le_of_relative_grow` is itself
symmetric under swapping the carriers. Left/right output scalars would not express anything
natural here. Should genuinely variable tolerances be needed later, the honest generalization
is a **cell-pair schedule** `P.parts → Q.parts → ℝ`, not two scalars.

## Endpoints

The two extremes are exact rather than approximate, and both are proved here so consumers
need not re-derive them: `⊥` (all cells singletons) is homogeneous at tolerance `0`, and a
pair of indiscrete partitions is homogeneous exactly when the whole rectangle is.

Nothing in this file mentions ladders, trees, ranks, or any stability notion.
-/

namespace RegularityLemmata

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {R : α → β → Prop}
variable {A : Finset α} {B : Finset β} {ε ε' : ℝ}

/-- Every cell rectangle of the pair is `ε`-homogeneous. -/
def AreHomogeneousPartitions (R : α → β → Prop) {A : Finset α} {B : Finset β}
    (P : Finpartition A) (Q : Finpartition B) (ε : ℝ) : Prop :=
  ∀ p ∈ P.parts, ∀ q ∈ Q.parts, IsHomogeneousPair R p q ε

/-! ### Tolerance monotonicity -/

theorem AreHomogeneousPartitions.mono {P : Finpartition A} {Q : Finpartition B}
    (h : AreHomogeneousPartitions R P Q ε) (hε : ε ≤ ε') :
    AreHomogeneousPartitions R P Q ε' :=
  fun p hp q hq ↦ (h p hp q hq).mono hε

/-! ### Transpose and complement

Both are inherited cellwise from the rectangle-level equivalences, so they are `iff`s rather
than one-way transports. -/

/-- Transposing exchanges the two partitions. -/
theorem areHomogeneousPartitions_swapRel_iff {P : Finpartition A} {Q : Finpartition B} :
    AreHomogeneousPartitions (swapRel R) Q P ε ↔ AreHomogeneousPartitions R P Q ε := by
  constructor
  · intro h p hp q hq
    exact isHomogeneousPair_swapRel_iff.mp (h q hq p hp)
  · intro h q hq p hp
    exact isHomogeneousPair_swapRel_iff.mpr (h p hp q hq)

/-- Complementing the relation preserves homogeneity of the pair, empty cells included. -/
theorem areHomogeneousPartitions_not_iff {P : Finpartition A} {Q : Finpartition B} :
    AreHomogeneousPartitions (fun a b => ¬ R a b) P Q ε ↔ AreHomogeneousPartitions R P Q ε := by
  constructor
  · intro h p hp q hq
    exact isHomogeneousPair_not_iff.mp (h p hp q hq)
  · intro h p hp q hq
    exact isHomogeneousPair_not_iff.mpr (h p hp q hq)

/-! ### Endpoints -/

/-- **The trivial tolerance.** At `1/2` every partition pair is homogeneous, for every
relation — the cellwise lift of `isHomogeneousPair_of_half_le`. -/
theorem areHomogeneousPartitions_of_half_le (R : α → β → Prop) (P : Finpartition A)
    (Q : Finpartition B) (hε : (1 : ℝ) / 2 ≤ ε) : AreHomogeneousPartitions R P Q ε :=
  fun p _ q _ ↦ isHomogeneousPair_of_half_le R p q hε

/-- **The bottom partitions are exactly homogeneous.** Every cell of `⊥` is a singleton, so
every cell rectangle is a one-point rectangle with density `0` or `1`. This needs tolerance
`0`, not a positive one. -/
theorem areHomogeneousPartitions_bot (R : α → β → Prop) :
    AreHomogeneousPartitions R (⊥ : Finpartition A) (⊥ : Finpartition B) 0 := by
  intro p hp q hq
  rw [Finpartition.parts_bot, Finset.mem_map] at hp hq
  obtain ⟨a, -, rfl⟩ := hp
  obtain ⟨b, -, rfl⟩ := hq
  exact isHomogeneousPair_singleton R a b

/-- …hence at every nonnegative tolerance. -/
theorem areHomogeneousPartitions_bot_of_nonneg (R : α → β → Prop) (hε : 0 ≤ ε) :
    AreHomogeneousPartitions R (⊥ : Finpartition A) (⊥ : Finpartition B) ε :=
  (areHomogeneousPartitions_bot R).mono hε

/-- **The indiscrete pair is the whole rectangle.** With one cell on each side, homogeneity of
the pair is exactly homogeneity of `A ×ˢ B`. -/
theorem areHomogeneousPartitions_indiscrete_iff {hA : A ≠ ∅} {hB : B ≠ ∅} :
    AreHomogeneousPartitions R (Finpartition.indiscrete hA) (Finpartition.indiscrete hB) ε
      ↔ IsHomogeneousPair R A B ε := by
  constructor
  · intro h
    exact h A (by rw [Finpartition.indiscrete_parts]; exact Finset.mem_singleton_self _)
      B (by rw [Finpartition.indiscrete_parts]; exact Finset.mem_singleton_self _)
  · intro h p hp q hq
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hp hq
    subst hp; subst hq
    exact h

/-! ### Tests -/

section Tests

-- **A single tolerance is genuinely one number**: the same `ε` bounds every cell pair, on
-- carriers of different sizes with independent partitions.
example (R : Fin 2 → Fin 3 → Prop) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) :
    AreHomogeneousPartitions R P Q (1 / 2) :=
  areHomogeneousPartitions_of_half_le R P Q le_rfl

-- The bottom pair is homogeneous at **zero**, not merely at a positive tolerance.
example (R : Fin 2 → Fin 3 → Prop) :
    AreHomogeneousPartitions R (⊥ : Finpartition (Finset.univ : Finset (Fin 2)))
      (⊥ : Finpartition (Finset.univ : Finset (Fin 3))) 0 :=
  areHomogeneousPartitions_bot R

-- Transpose and complement compose, and both directions are available.
example (R : Fin 2 → Fin 3 → Prop) (P : Finpartition (Finset.univ : Finset (Fin 2)))
    (Q : Finpartition (Finset.univ : Finset (Fin 3))) (ε : ℝ)
    (h : AreHomogeneousPartitions R P Q ε) :
    AreHomogeneousPartitions (fun b a => ¬ swapRel R b a) Q P ε :=
  areHomogeneousPartitions_not_iff.mpr (areHomogeneousPartitions_swapRel_iff.mpr h)

end Tests

end RegularityLemmata
