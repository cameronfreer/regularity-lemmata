import RegularityLemmata.Finite.PairDensity
import RegularityLemmata.Finite.Inequalities
import RegularityLemmata.Partition.Basic

/-!
# Block energy and superadditivity

The mass-weighted local energy of an ordered block `(A, B)` is
`pairDensity R A B ² · |A| · |B|`. Its key property is superadditivity under disjoint
covers (an Engel-form/Cauchy–Schwarz consequence), specialized to refinement fibers in
`blockEnergy_le_sum_refined` — the engine behind energy monotonicity of the partition
energy (`Partition/Energy.lean`).
-/

namespace RegularityLemmata

variable {α : Type*} {s : Finset α}
variable {R : α → α → Prop} [DecidableRel R] {A B : Finset α}

/-- Mass-weighted local energy of the ordered block `(A, B)`. -/
noncomputable def blockEnergy (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℝ :=
  pairDensity R A B ^ 2 * (A.card : ℝ) * (B.card : ℝ)

theorem blockEnergy_nonneg : 0 ≤ blockEnergy R A B := by
  unfold blockEnergy
  have := pairDensity_nonneg (R := R) (A := A) (B := B)
  positivity

theorem blockEnergy_le_mass : blockEnergy R A B ≤ (A.card : ℝ) * B.card := by
  unfold blockEnergy
  have h1 := pairDensity_le_one (R := R) (A := A) (B := B)
  have h0 := pairDensity_nonneg (R := R) (A := A) (B := B)
  have hA : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hd2 : pairDensity R A B ^ 2 ≤ 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd2 hA) hB
  simpa using this

/-- Empty left side kills the pair count. -/
theorem pairCount_of_left_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (B : Finset α) (h : A.card = 0) : pairCount R A B = 0 := by
  rw [Finset.card_eq_zero.mp h]
  simp [pairCount]

/-- Empty right side kills the pair count. -/
theorem pairCount_of_right_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (A : Finset α) (h : B.card = 0) : pairCount R A B = 0 := by
  rw [Finset.card_eq_zero.mp h]
  simp [pairCount]

/-- Block energy as `(pair count)² / mass`, valid also for zero mass (both sides `0`). -/
theorem blockEnergy_eq_count_sq_div (R : α → α → Prop) [DecidableRel R] (X Y : Finset α) :
    blockEnergy R X Y = (pairCount R X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by
  unfold blockEnergy
  rw [pairDensity_eq_count_div]
  rcases eq_or_ne ((X.card : ℝ) * (Y.card : ℝ)) 0 with hm | hm
  · rcases mul_eq_zero.mp hm with h | h <;> rw [h] <;> simp
  · have hX : (X.card : ℝ) ≠ 0 := fun h => hm (by rw [h]; ring)
    have hY : (Y.card : ℝ) ≠ 0 := fun h => hm (by rw [h]; ring)
    field_simp

/-- **Superadditivity.** Refining `(C, D)` into the rectangles of disjoint covers never
decreases the total block energy (Engel form over the cover rectangles). -/
theorem blockEnergy_superadditive [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    {C D : Finset α} (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    blockEnergy R C D ≤ ∑ C' ∈ sC, ∑ D' ∈ sD, blockEnergy R C' D' := by
  have hcount : ∑ p ∈ sC ×ˢ sD, (pairCount R p.1 p.2 : ℝ) = (pairCount R C D : ℝ) := by
    rw [← Nat.cast_sum, ← pairCount_biUnion R sC sD hCdisj hCcover hDdisj hDcover]
  have hmass : ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * (p.2.card : ℝ))
      = (C.card : ℝ) * (D.card : ℝ) := by
    rw [Finset.sum_product, ← sum_card_biUnion_cast sC hCdisj hCcover,
      ← sum_card_biUnion_cast sD hDdisj hDcover, Finset.sum_mul_sum]
  have hgnn : ∀ p ∈ sC ×ˢ sD, 0 ≤ (p.1.card : ℝ) * (p.2.card : ℝ) := fun p _ => by
    positivity
  have hfg0 : ∀ p ∈ sC ×ˢ sD, (p.1.card : ℝ) * (p.2.card : ℝ) = 0 →
      (pairCount R p.1 p.2 : ℝ) = 0 := by
    intro p _ h
    rcases mul_eq_zero.mp h with h1 | h2
    · have hc : p.1.card = 0 := by exact_mod_cast h1
      simp [pairCount_of_left_card_eq_zero R p.2 hc]
    · have hc : p.2.card = 0 := by exact_mod_cast h2
      simp [pairCount_of_right_card_eq_zero R p.1 hc]
  have htitu := titu_finset (fun p => (pairCount R p.1 p.2 : ℝ))
    (fun p => (p.1.card : ℝ) * (p.2.card : ℝ)) (sC ×ˢ sD) hgnn hfg0
  rw [hcount, hmass, ← blockEnergy_eq_count_sq_div R C D] at htitu
  refine htitu.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun C' _ =>
    Finset.sum_congr rfl fun D' _ => (blockEnergy_eq_count_sq_div R C' D').symm

/-- Superadditivity along refinement fibers: the block energy of a `P`-block is at most
the summed block energies of its refined `Q`-sub-blocks. -/
theorem blockEnergy_le_sum_refined [DecidableEq α] {P Q : Finpartition s} (hQ : Q ≤ P)
    (R : α → α → Prop) [DecidableRel R] {C D : Finset α}
    (hC : C ∈ P.parts) (hD : D ∈ P.parts) :
    blockEnergy R C D ≤ ∑ C' ∈ Q.parts.filter (· ⊆ C), ∑ D' ∈ Q.parts.filter (· ⊆ D),
      blockEnergy R C' D' := by
  refine blockEnergy_superadditive R _ _ ?_ (biUnion_filter_subset_eq hQ hC) ?_
    (biUnion_filter_subset_eq hQ hD)
  · exact Q.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  · exact Q.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)

/-! ### Tests and adversarial examples -/

-- An empty side gives zero block energy.
example : blockEnergy (fun a b : Fin 3 => a < b) ∅ Finset.univ = 0 := by
  simp [blockEnergy]

-- Diagonal blocks are included and can be nonzero: for the equality relation on a
-- singleton, the block energy is 1² · 1 · 1 = 1.
example : blockEnergy (fun a b : Fin 3 => a = b) {0} {0} = 1 := by
  rw [blockEnergy_eq_count_sq_div,
    show pairCount (fun a b : Fin 3 => a = b) {0} {0} = 1 from by decide]
  norm_num

-- A concrete refined-superadditivity instance: ⊤ refined by ⊥ on {0, 1}.
example :
    blockEnergy (fun a b : Fin 2 => a < b) {0, 1} {0, 1}
      ≤ ∑ C' ∈ (⊥ : Finpartition ({0, 1} : Finset (Fin 2))).parts.filter (· ⊆ {0, 1}),
          ∑ D' ∈ (⊥ : Finpartition ({0, 1} : Finset (Fin 2))).parts.filter (· ⊆ {0, 1}),
            blockEnergy (fun a b : Fin 2 => a < b) C' D' :=
  blockEnergy_le_sum_refined (P := ⊤) (Q := ⊥) bot_le _ (by decide) (by decide)

end RegularityLemmata
