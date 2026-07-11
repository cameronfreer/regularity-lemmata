/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Polyad
import RegularityLemmata.Finite.Inequalities

/-!
# Polyad energy and refinement monotonicity

Phase 7 unit 3 (design freeze in `ARCHITECTURE.md`): the mass-weighted energy of a
cell assignment `κ : RSet j α → Fin K` against an observable —

`polyadEnergyNum κ obs = Σ_key density(block key)² · |block key|`

— the polyad-level analogue of the pair energy in `Partition/Energy.lean` and of the
*index* of a partition family in V. Rödl, M. Schacht, *Regular partitions of
hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007) (the mean-square
density driving their iteration); the mass-weighted normalization follows the
library's graph-ladder convention (A. Schrijver's CWI notes; Y. Zhao, *Graph Theory
and Additive Combinatorics*). All blocks are included — the empty/unrealized keys
contribute `0` under the guard-free conventions.

The load-bearing fact is **refinement monotonicity** (`polyadEnergyNum_comp_le`):
merging cells through any map `f : Fin K' → Fin K` can only lower the energy,
because a merged block is the disjoint union of its fibers' blocks
(`polyadBlock_comp`) and the Engel-form Cauchy–Schwarz (`titu_finset`,
`Finite/Inequalities.lean`) is exactly `(Σ r)²/(Σ b) ≤ Σ r²/b`. This is the
square-root-free energy bookkeeping the one-step repair (unit 4) will consume.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K K' : ℕ}

/-- Mass-weighted polyad energy (numerator form): `Σ_key d² · |block|`. -/
noncomputable def polyadEnergyNum (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] : ℝ :=
  ∑ key : Fin (j + 1) → Fin K,
    densityOn (polyadBlock κ key) obs ^ 2 * ((polyadBlock κ key).card : ℝ)

theorem polyadEnergyNum_nonneg (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    0 ≤ polyadEnergyNum κ obs :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- The energy is at most the total injective mass (densities are at most `1`). -/
theorem polyadEnergyNum_le_count (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    polyadEnergyNum κ obs ≤ (injectiveTupleCount α (j + 1) : ℝ) := by
  have hle : polyadEnergyNum κ obs
      ≤ ∑ key : Fin (j + 1) → Fin K, ((polyadBlock κ key).card : ℝ) := by
    refine Finset.sum_le_sum fun key _ => ?_
    have hd : densityOn (polyadBlock κ key) obs ^ 2 ≤ 1 := by
      have h0 := densityOn_nonneg (S := polyadBlock κ key) (p := obs)
      have h1 := densityOn_le_one (S := polyadBlock κ key) (p := obs)
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)) (by rw [one_mul])
  refine le_trans hle (le_of_eq ?_)
  rw [← Nat.cast_sum]
  exact_mod_cast sum_card_polyadBlock κ

/-- **Fiber decomposition of a merged block**: coloring through `f : Fin K' → Fin K`
makes each merged block the union of the blocks of the keys in its fiber. -/
theorem polyadBlock_comp (f : Fin K' → Fin K) (κ' : RSet j α → Fin K')
    (P : Fin (j + 1) → Fin K) :
    polyadBlock (fun e => f (κ' e)) P
      = (Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
          (fun i => f (P' i)) = P).biUnion (polyadBlock κ') := by
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · intro hv
    have hinj := injective_of_mem_polyadBlock hv
    refine ⟨fun i => κ' (lowerFaceRSet hinj i),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · funext i
      exact (mem_polyadBlock_iff_of_injective hinj).mp hv i
    · rw [mem_polyadBlock_iff_of_injective hinj]
      intro i
      rfl
  · rintro ⟨P', hP', hv⟩
    have hinj := injective_of_mem_polyadBlock hv
    rw [mem_polyadBlock_iff_of_injective hinj] at hv ⊢
    rw [Finset.mem_filter] at hP'
    intro i
    rw [← congrFun hP'.2 i]
    exact congrArg f (hv i)

/-- Filtered cardinality of a merged block: the sum over its fiber. -/
theorem card_filter_polyadBlock_comp (f : Fin K' → Fin K) (κ' : RSet j α → Fin K')
    (P : Fin (j + 1) → Fin K) (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    ((polyadBlock (fun e => f (κ' e)) P).filter obs).card
      = ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
          (fun i => f (P' i)) = P, ((polyadBlock κ' P').filter obs).card := by
  rw [polyadBlock_comp, Finset.filter_biUnion]
  exact Finset.card_biUnion fun P₁ _ P₂ _ h =>
    (polyadBlock_disjoint h).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Cardinality of a merged block: the sum over its fiber. -/
theorem card_polyadBlock_comp (f : Fin K' → Fin K) (κ' : RSet j α → Fin K')
    (P : Fin (j + 1) → Fin K) :
    (polyadBlock (fun e => f (κ' e)) P).card
      = ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
          (fun i => f (P' i)) = P, (polyadBlock κ' P').card := by
  rw [polyadBlock_comp]
  exact Finset.card_biUnion fun P₁ _ P₂ _ h => polyadBlock_disjoint h

/-- **Refinement monotonicity**: merging cells can only lower the energy. The heart
is the Engel-form Cauchy–Schwarz `(Σ r)²/(Σ b) ≤ Σ r²/b` applied on each fiber. -/
theorem polyadEnergyNum_comp_le (f : Fin K' → Fin K) (κ' : RSet j α → Fin K')
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    polyadEnergyNum (fun e => f (κ' e)) obs ≤ polyadEnergyNum κ' obs := by
  classical
  have hstep : ∀ P : Fin (j + 1) → Fin K,
      densityOn (polyadBlock (fun e => f (κ' e)) P) obs ^ 2
          * ((polyadBlock (fun e => f (κ' e)) P).card : ℝ)
        ≤ ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
            (fun i => f (P' i)) = P,
            densityOn (polyadBlock κ' P') obs ^ 2 * ((polyadBlock κ' P').card : ℝ) := by
    intro P
    rw [sq_densityOn_mul_card]
    have hr : (((polyadBlock (fun e => f (κ' e)) P).filter obs).card : ℝ)
        = ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
            (fun i => f (P' i)) = P, (((polyadBlock κ' P').filter obs).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast card_filter_polyadBlock_comp f κ' P obs
    have hb : ((polyadBlock (fun e => f (κ' e)) P).card : ℝ)
        = ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
            (fun i => f (P' i)) = P, ((polyadBlock κ' P').card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast card_polyadBlock_comp f κ' P
    rw [hr, hb]
    refine le_trans
      (titu_finset _ _ _ (fun P' _ => Nat.cast_nonneg _) fun P' _ hzero => ?_)
      (le_of_eq (Finset.sum_congr rfl fun P' _ => ?_))
    · have hcard : (polyadBlock κ' P').card = 0 := by exact_mod_cast hzero
      have hle := Finset.card_filter_le (polyadBlock κ' P') obs
      rw [hcard, Nat.le_zero] at hle
      exact_mod_cast hle
    · rw [sq_densityOn_mul_card]
  calc polyadEnergyNum (fun e => f (κ' e)) obs
      ≤ ∑ P : Fin (j + 1) → Fin K,
          ∑ P' ∈ Finset.univ.filter fun P' : Fin (j + 1) → Fin K' =>
            (fun i => f (P' i)) = P,
            densityOn (polyadBlock κ' P') obs ^ 2 * ((polyadBlock κ' P').card : ℝ) :=
        Finset.sum_le_sum fun P _ => hstep P
    _ = polyadEnergyNum κ' obs :=
        Finset.sum_fiberwise_of_maps_to (fun P' _ => Finset.mem_univ _) _

/-! ### Tests and adversarial examples -/

section Tests

-- The nowhere-true observable has zero energy.
example (κ : RSet 2 (Fin 4) → Fin 2) :
    polyadEnergyNum κ (fun _ : Fin 3 → Fin 4 => False) = 0 := by
  simp [polyadEnergyNum, densityOn]

-- Statement-level instances of the bounds and monotonicity at concrete types.
example (κ : RSet 2 (Fin 4) → Fin 3) (obs : (Fin 3 → Fin 4) → Prop)
    [DecidablePred obs] : 0 ≤ polyadEnergyNum κ obs :=
  polyadEnergyNum_nonneg κ obs

example (κ : RSet 2 (Fin 4) → Fin 3) (obs : (Fin 3 → Fin 4) → Prop)
    [DecidablePred obs] :
    polyadEnergyNum κ obs ≤ (injectiveTupleCount (Fin 4) 3 : ℝ) :=
  polyadEnergyNum_le_count κ obs

-- Merging the finer coloring's cells (here: collapsing Fin 2 to Fin 1) can only
-- lower the energy.
example (κ' : RSet 2 (Fin 4) → Fin 2) (obs : (Fin 3 → Fin 4) → Prop)
    [DecidablePred obs] :
    polyadEnergyNum (fun _ => (0 : Fin 1)) obs ≤ polyadEnergyNum κ' obs := by
  have h := polyadEnergyNum_comp_le (fun _ : Fin 2 => (0 : Fin 1)) κ' obs
  exact h

end Tests

end RegularityLemmata
