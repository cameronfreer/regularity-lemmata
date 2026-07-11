/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Uniformity
import RegularityLemmata.Partition.Energy

/-!
# Bad mass and weak regularity of a partition

An ordered pair of **distinct** parts is `ε`-bad when it fails `ε`-uniformity (diagonal
pairs are excluded here — they are charged or discarded only at the simple-graph
bridge, matching the energy convention of including them in `energy`).

`badMassNum` is the raw mass `Σ |C||D|` over bad ordered pairs; `badMass` its
normalization by `|s|²` under the library's zero-denominator convention. A partition is
**weakly `ε`-regular** when its normalized bad mass is at most `ε`.

Ordered off-diagonal pairs follow mathlib's `Finpartition.nonUniforms`
(`Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`). Mathlib *counts* bad pairs
because its argument runs on equipartitions, where all cell pairs carry comparable
mass; weighting by `|C||D|` is this library's generalization to arbitrary partitions
(a recorded design decision), consistent with the mass-weighted `energy`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

/-- An ordered pair of distinct parts failing `ε`-uniformity. -/
def IsBadPair (C D : Finset α) : Prop :=
  C ≠ D ∧ ¬ IsUniformPair R C D ε

open Classical in
/-- Raw bad mass: `Σ |C| · |D|` over the `ε`-bad ordered pairs of parts. -/
noncomputable def badMassNum (P : Finpartition s) : ℝ :=
  ∑ uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair R ε uv.1 uv.2),
    (uv.1.card : ℝ) * uv.2.card

/-- Normalized bad mass, in `[0, 1]`; `0` on the empty ground set. -/
noncomputable def badMass (P : Finpartition s) : ℝ :=
  badMassNum R ε P / (s.card : ℝ) ^ 2

/-- Weak `ε`-regularity: the normalized bad mass is at most `ε`. -/
def IsWeakRegular (P : Finpartition s) : Prop :=
  badMass R ε P ≤ ε

variable {P : Finpartition s}

theorem badMassNum_nonneg : 0 ≤ badMassNum R ε P :=
  Finset.sum_nonneg fun uv _ => by positivity

theorem badMass_nonneg : 0 ≤ badMass R ε P :=
  div_nonneg (badMassNum_nonneg R ε) (by positivity)

theorem badMassNum_le_sq : badMassNum R ε P ≤ (s.card : ℝ) ^ 2 := by
  classical
  calc badMassNum R ε P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, (uv.1.card : ℝ) * uv.2.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun uv _ _ => by positivity
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

theorem badMass_le_one : badMass R ε P ≤ 1 := by
  unfold badMass
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact badMassNum_le_sq R ε

/-- Bad mass is antitone in the tolerance: a pair bad at a larger `ε'` is bad at any
smaller `ε`. -/
theorem badMassNum_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassNum R ε' P ≤ badMassNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  refine ⟨huv.1, huv.2.1, fun hunif => huv.2.2 (hunif.mono hεε)⟩

theorem badMass_anti {ε ε' : ℝ} (hεε : ε ≤ ε') : badMass R ε' P ≤ badMass R ε P :=
  div_le_div_of_nonneg_right (badMassNum_anti R hεε) (by positivity) |>.trans_eq rfl

/-- Everything is weakly `1`-regular. -/
theorem isWeakRegular_one : IsWeakRegular R 1 P := badMass_le_one R 1

/-! ### Tests and adversarial examples -/

-- A concrete bad pair: `R a b ↔ a = 0` on `Fin 4`, cells {0,1} and {2,3}. The whole
-- block has density 1/2; the sub-block {0} × {2,3} has density 1 — deviation 1/2 > 1/4.
example : IsBadPair (fun a _ : Fin 4 => a = 0) (1 / 4) {0, 1} {2, 3} := by
  refine ⟨by decide, not_isUniformPair_of_witness
    ⟨{0}, {2, 3}, by decide, by decide, ?_, ?_, ?_⟩⟩
  · rw [show ({0} : Finset (Fin 4)).card = 1 from by decide,
      show ({0, 1} : Finset (Fin 4)).card = 2 from by decide]
    norm_num
  · norm_num
  · rw [pairDensity_eq_count_div, pairDensity_eq_count_div,
      show pairCount (fun a _ : Fin 4 => a = 0) {0} {2, 3} = 2 from by decide,
      show pairCount (fun a _ : Fin 4 => a = 0) {0, 1} {2, 3} = 2 from by decide,
      show ({0} : Finset (Fin 4)).card = 1 from by decide,
      show ({0, 1} : Finset (Fin 4)).card = 2 from by decide,
      show ({2, 3} : Finset (Fin 4)).card = 2 from by decide]
    norm_num

-- Diagonal pairs are never bad, by definition.
example : ¬ IsBadPair (fun a _ : Fin 4 => a = 0) (1 / 4) {0, 1} {0, 1} := fun h =>
  h.1 rfl

-- On the empty ground set the bad mass is 0 and every partition is weakly regular
-- at every nonnegative tolerance.
example (P : Finpartition (∅ : Finset (Fin 3))) {ε : ℝ} (hε : 0 ≤ ε) :
    IsWeakRegular (fun a b : Fin 3 => a < b) ε P := by
  have h0 : badMass (fun a b : Fin 3 => a < b) ε P = 0 := by
    rw [badMass]
    simp
  rw [IsWeakRegular, h0]
  exact hε

end RegularityLemmata
