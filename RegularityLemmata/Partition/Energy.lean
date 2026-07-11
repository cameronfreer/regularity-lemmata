/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.BlockEnergy
import Mathlib.Algebra.BigOperators.Field

/-!
# Mass-weighted partition energy and refinement monotonicity

The partition energy of a relation `R` with respect to `P : Finpartition s` is the
mass-weighted mean of squared block densities,
`energy R P = Σ_{A,B ∈ parts} (|A||B| / |s|²) · d(A,B)²`, **including diagonal blocks**
(see `energy_eq_sum_weighted`). It is monotone under refinement (`energy_mono`) — the
quantity driving iterated-refinement (energy-increment) arguments.

**Design fact.** The *uniform* block-mean of `d²` (dividing by `#parts²` instead of
weighting by mass) is NOT refinement-monotone. Worked example over `s = {0,1,2}` with
`R a b ↔ (a = 0 ∧ b = 0)`: for the partition `{{0}, {1,2}}` the four block densities
are `1,0,0,0`, uniform mean `1/4`; refining to singletons gives nine densities
`1,0,…,0`, uniform mean `1/9 < 1/4`. The mass-weighted energy instead moves from
`1/9 ≤ 1/9` (it is `1·1·1/9 = 1/9` in both cases, consistent with monotonicity).
Mathlib's `Finpartition.energy` is the uniform, `ℚ`-valued, off-diagonal variant used
for equipartitions; it is deliberately not the primary notion here, and the comparison
belongs to the graph-ladder bridge where both sides speak `SimpleGraph`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R]

/-- Un-normalized partition energy: mass-weighted local energies over all ordered pairs
of parts, diagonal included. -/
noncomputable def energyNum (P : Finpartition s) : ℝ :=
  ∑ AB ∈ P.parts ×ˢ P.parts, blockEnergy R AB.1 AB.2

/-- Normalized partition energy, in `[0, 1]`; `0` on the empty ground set. -/
noncomputable def energy (P : Finpartition s) : ℝ :=
  energyNum R P / (s.card : ℝ) ^ 2

variable {P Q : Finpartition s}

theorem energyNum_nonneg : 0 ≤ energyNum R P :=
  Finset.sum_nonneg fun _ _ => blockEnergy_nonneg

theorem energyNum_le_sq : energyNum R P ≤ (s.card : ℝ) ^ 2 := by
  have hprod : ∑ uv ∈ P.parts ×ˢ P.parts, ((uv.1.card : ℝ) * (uv.2.card : ℝ))
      = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  calc energyNum R P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, ((uv.1.card : ℝ) * (uv.2.card : ℝ)) :=
        Finset.sum_le_sum fun uv _ => blockEnergy_le_mass
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := hprod
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

theorem energy_nonneg : 0 ≤ energy R P :=
  div_nonneg (energyNum_nonneg R) (by positivity)

/-- Holds for ALL `s`: on the empty ground set the energy is `0 / 0 = 0`. -/
theorem energy_le_one : energy R P ≤ 1 := by
  unfold energy
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact energyNum_le_sq R

/-- Reindexing the refined energy along the `P`-parent fibers. -/
theorem energyNum_eq_sum_refined (hQ : Q ≤ P) :
    (∑ C ∈ P.parts, ∑ D ∈ P.parts, ∑ C' ∈ Q.parts.filter (· ⊆ C),
      ∑ D' ∈ Q.parts.filter (· ⊆ D), blockEnergy R C' D') = energyNum R Q := by
  rw [Finset.sum_congr rfl fun C _ => Finset.sum_comm]
  rw [sum_over_parents hQ (fun C' => ∑ D ∈ P.parts, ∑ D' ∈ Q.parts.filter (· ⊆ D),
    blockEnergy R C' D')]
  rw [Finset.sum_congr rfl fun C' _ => sum_over_parents hQ (fun D' => blockEnergy R C' D')]
  unfold energyNum
  rw [Finset.sum_product]

/-- Refinement never decreases the un-normalized energy. -/
theorem energyNum_mono (hQ : Q ≤ P) : energyNum R P ≤ energyNum R Q := by
  have hstep : energyNum R P
      ≤ ∑ C ∈ P.parts, ∑ D ∈ P.parts, ∑ C' ∈ Q.parts.filter (· ⊆ C),
          ∑ D' ∈ Q.parts.filter (· ⊆ D), blockEnergy R C' D' := by
    unfold energyNum
    rw [Finset.sum_product]
    exact Finset.sum_le_sum fun C hC =>
      Finset.sum_le_sum fun D hD => blockEnergy_le_sum_refined hQ R hC hD
  rw [energyNum_eq_sum_refined R hQ] at hstep
  exact hstep

/-- **Energy monotonicity.** Refinement never decreases the partition energy. -/
theorem energy_mono (hQ : Q ≤ P) : energy R P ≤ energy R Q := by
  unfold energy
  gcongr
  exact energyNum_mono R hQ

/-- The energy as an explicitly mass-weighted mean of squared block densities
(diagonal blocks included). -/
theorem energy_eq_sum_weighted :
    energy R P = ∑ AB ∈ P.parts ×ˢ P.parts,
      ((AB.1.card : ℝ) * AB.2.card / (s.card : ℝ) ^ 2) * pairDensity R AB.1 AB.2 ^ 2 := by
  rw [energy, energyNum, Finset.sum_div]
  exact Finset.sum_congr rfl fun AB _ => by rw [blockEnergy]; ring

/-! ### Tests and adversarial examples -/

-- Exact identity for the indiscrete partition of a 3-element set with the strict order:
-- one block of density 3/9 = 1/3, so energy = (1/3)² · 3 · 3 / 3² = 1/9.
example :
    energy (fun a b : Fin 3 => a < b) (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      = 1 / 9 := by
  rw [energy, energyNum,
    show (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts = {{0, 1, 2}} from by decide]
  rw [Finset.singleton_product_singleton, Finset.sum_singleton,
    blockEnergy_eq_count_sq_div,
    show pairCount (fun a b : Fin 3 => a < b) {0, 1, 2} {0, 1, 2} = 3 from by decide,
    show (({0, 1, 2} : Finset (Fin 3)).card) = 3 from by decide]
  norm_num

-- Energy on the empty ground set is 0 (division convention).
example (P : Finpartition (∅ : Finset (Fin 3))) :
    energy (fun a b : Fin 3 => a < b) P = 0 := by
  rw [energy]
  simp

-- A concrete monotonicity instance: ⊤ vs ⊥ on {0, 1, 2}.
example :
    energy (fun a b : Fin 3 => a < b) (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      ≤ energy (fun a b : Fin 3 => a < b) (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))) :=
  energy_mono _ bot_le

end RegularityLemmata
