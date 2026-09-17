/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.SectionDefect
import RegularityLemmata.Partition.Basic

/-!
# The resampling defect of a partition

For a partition `P` of a finite set `s` and a Boolean section `p`, the **partition defect**
`partitionDefect P p := ∑_{l ∈ P.parts} sectionDisagreement l p / |l|` is the number of points
of `s` that a within-part resample flips, in expectation: each part contributes
`|l| · 2·d_l·(1 − d_l)` with `d_l` the density of `p` on `l`
(`partitionDefect_eq_sum_density`), so the defect is at most `|s|/2` and is `0` on the
singleton partition `⊥`. For a finite family of sections `p y`, `y ∈ Y`, the family defect is the
sum (`familyDefect`).

**The exact refinement variance identity** (`partitionDefect_eq_add_refinementVariance`).
For `Q ≤ P`,

`partitionDefect P p = partitionDefect Q p + 2 · sectionRefinementVariance Q P p`,

where the refinement variance `∑_{t ∈ P} ∑_{u ∈ Q, u ⊆ t} |u| · (d_u − d_t)²` is the
mass-weighted variance of the fine densities around their coarse density: the one-dimensional
Boolean analogue of the parallel-axis identities `refinementVarianceNum_eq`
(`RegularityLemmata/Graph/Strong.lean`) and `rectEnergyNum_eq_add_rectRefinementVarianceNum`
(`RegularityLemmata/Partition/RectKernelEnergy.lean`), stated in the same proof-free style: the
variance is defined for arbitrary pairs and `Q ≤ P` enters only the theorem. **Refinement
monotonicity** (`partitionDefect_mono`, `familyDefect_mono`) is the corollary
`partitionDefect Q p ≤ partitionDefect P p`.

Join cardinality is `card_parts_inf_le` / `card_parts_inf'_le` in
`RegularityLemmata/Partition/Basic.lean`; the majority-rounding bound at the join of arbitrary
coordinate partitions is `RegularityLemmata/Relational/CoordinatePartitionRounding.lean`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The resampling defect of `P` for the section `p`: `∑_{l ∈ P.parts} sectionDisagreement l p / |l|`. -/
noncomputable def partitionDefect (P : Finpartition s) (p : α → Prop) [DecidablePred p] : ℝ :=
  ∑ l ∈ P.parts, (sectionDisagreement l p : ℝ) / l.card

/-- The refinement variance of `Q` inside `P` for the section `p`: the fine parts' densities
around their coarse part's density, weighted by size. Proof-free: `Q ≤ P` is not required to
state it. -/
noncomputable def sectionRefinementVariance (Q P : Finpartition s) (p : α → Prop)
    [DecidablePred p] : ℝ :=
  ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (u.card : ℝ) * (densityOn u p - densityOn t p) ^ 2

/-- The defect of a finite family of sections. -/
noncomputable def familyDefect (P : Finpartition s) {ι : Type*} (Y : Finset ι) (p : ι → α → Prop)
    [∀ y, DecidablePred (p y)] : ℝ :=
  ∑ y ∈ Y, partitionDefect P (p y)

section Basic

variable (P : Finpartition s) (p : α → Prop) [DecidablePred p]

theorem partitionDefect_nonneg : 0 ≤ partitionDefect P p :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

/-- Each part contributes `|l| · 2·d_l·(1 − d_l)`. -/
theorem partitionDefect_eq_sum_density :
    partitionDefect P p
      = ∑ l ∈ P.parts, (l.card : ℝ) * (2 * densityOn l p * (1 - densityOn l p)) := by
  unfold partitionDefect
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hpos : (0 : ℝ) < l.card := by exact_mod_cast (P.nonempty_of_mem_parts hl).card_pos
  rw [← sectionDisagreement_div_sq]
  field_simp

/-- The defect never exceeds `|s| / 2`. -/
theorem partitionDefect_le_half : partitionDefect P p ≤ (s.card : ℝ) / 2 := by
  rw [partitionDefect_eq_sum_density]
  calc ∑ l ∈ P.parts, (l.card : ℝ) * (2 * densityOn l p * (1 - densityOn l p))
      ≤ ∑ l ∈ P.parts, (l.card : ℝ) * (1 / 2) :=
        Finset.sum_le_sum fun l _ ↦
          mul_le_mul_of_nonneg_left two_mul_mul_one_sub_le_half (Nat.cast_nonneg _)
    _ = (s.card : ℝ) / 2 := by rw [← Finset.sum_mul, sum_card_parts_cast]; ring

/-- Singleton parts never disagree: the defect of `⊥` is `0`. -/
theorem partitionDefect_bot : partitionDefect (⊥ : Finpartition s) p = 0 := by
  unfold partitionDefect
  refine Finset.sum_eq_zero fun l hl ↦ ?_
  rw [Finpartition.parts_bot, Finset.mem_map] at hl
  obtain ⟨x, _, rfl⟩ := hl
  have : sectionDisagreement ({x} : Finset α) p = 0 := by
    rw [sectionDisagreement_eq]
    by_cases hx : p x <;> simp [hx]
  simp [Function.Embedding.coeFn_mk, this]

theorem sectionRefinementVariance_nonneg (Q : Finpartition s) :
    0 ≤ sectionRefinementVariance Q P p :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity

theorem familyDefect_nonneg {ι : Type*} (Y : Finset ι) (q : ι → α → Prop)
    [∀ y, DecidablePred (q y)] : 0 ≤ familyDefect P Y q :=
  Finset.sum_nonneg fun _ _ ↦ partitionDefect_nonneg P _

end Basic

/-! ### The refinement variance identity -/

section Refinement

variable {P Q : Finpartition s} (p : α → Prop) [DecidablePred p]

/-- Inside a coarse part `t`, the fine parts' sizes add up to `|t|` and their `p`-counts add up
to the `p`-count of `t`. -/
private theorem sum_card_filter_subset (hQ : Q ≤ P) {t : Finset α} (ht : t ∈ P.parts) :
    ∑ u ∈ Q.parts.filter (· ⊆ t), (u.card : ℝ) = t.card ∧
      ∑ u ∈ Q.parts.filter (· ⊆ t), ((u.filter p).card : ℝ) = (t.filter p).card := by
  classical
  have hdisj : (↑(Q.parts.filter (· ⊆ t)) : Set (Finset α)).PairwiseDisjoint id :=
    Q.disjoint.subset (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  have hcover := biUnion_filter_subset_eq hQ ht
  constructor
  · rw [← Nat.cast_sum]; congr 1
    conv_rhs => rw [← hcover]
    exact (Finset.card_biUnion hdisj).symm
  · have hdisj' : (↑(Q.parts.filter (· ⊆ t)) : Set (Finset α)).PairwiseDisjoint
        fun u ↦ (id u).filter p := fun u hu v hv huv ↦
      (hdisj hu hv huv).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← Nat.cast_sum]; congr 1
    conv_rhs => rw [← hcover, Finset.filter_biUnion]
    exact (Finset.card_biUnion hdisj').symm

/-- **The refinement variance identity.** For `Q ≤ P`,
`partitionDefect P p = partitionDefect Q p + 2 · sectionRefinementVariance Q P p`. -/
theorem partitionDefect_eq_add_refinementVariance (hQ : Q ≤ P) :
    partitionDefect P p = partitionDefect Q p + 2 * sectionRefinementVariance Q P p := by
  classical
  rw [partitionDefect_eq_sum_density, partitionDefect_eq_sum_density,
    ← sum_over_parents hQ (fun u ↦ (u.card : ℝ) * (2 * densityOn u p * (1 - densityOn u p))),
    sectionRefinementVariance, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  obtain ⟨hcard, hcount⟩ := sum_card_filter_subset p hQ ht
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast (P.nonempty_of_mem_parts ht).card_pos
  -- per fine part, `|u| · d_u` is the `p`-count of `u`
  have hmass : ∀ u ∈ Q.parts.filter (· ⊆ t), (u.card : ℝ) * densityOn u p = (u.filter p).card := by
    intro u hu
    have hupos : (0 : ℝ) < u.card := by
      exact_mod_cast (Q.nonempty_of_mem_parts (Finset.mem_filter.mp hu).1).card_pos
    unfold densityOn; field_simp
  have htmass : (t.card : ℝ) * densityOn t p = (t.filter p).card := by
    unfold densityOn; field_simp
  set D := densityOn t p
  -- the summand rearranged so that only `∑ |u|` and `∑ |u| d_u` remain
  have hterm : ∀ u ∈ Q.parts.filter (· ⊆ t),
      (u.card : ℝ) * (2 * densityOn u p * (1 - densityOn u p))
          + 2 * ((u.card : ℝ) * (densityOn u p - D) ^ 2)
        = (2 - 4 * D) * ((u.card : ℝ) * densityOn u p) + 2 * D ^ 2 * (u.card : ℝ) := by
    intro u _; ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_congr rfl hmass, hcount, ← htmass, hcard]
  ring

/-- **Refinement monotonicity.** Refining the partition can only lower the defect. -/
theorem partitionDefect_mono (hQ : Q ≤ P) : partitionDefect Q p ≤ partitionDefect P p := by
  rw [partitionDefect_eq_add_refinementVariance p hQ]
  linarith [sectionRefinementVariance_nonneg P p Q]

theorem familyDefect_mono (hQ : Q ≤ P) {ι : Type*} (Y : Finset ι) (q : ι → α → Prop)
    [∀ y, DecidablePred (q y)] : familyDefect Q Y q ≤ familyDefect P Y q :=
  Finset.sum_le_sum fun y _ ↦ partitionDefect_mono (q y) hQ

/-- The identity lifted to a family of sections. -/
theorem familyDefect_eq_add_refinementVariance (hQ : Q ≤ P) {ι : Type*} (Y : Finset ι)
    (q : ι → α → Prop) [∀ y, DecidablePred (q y)] :
    familyDefect P Y q = familyDefect Q Y q + 2 * ∑ y ∈ Y, sectionRefinementVariance Q P (q y) := by
  unfold familyDefect
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ ↦ partitionDefect_eq_add_refinementVariance (q y) hQ

end Refinement

/-! ### Tests -/

section Tests

private def lab : Fin 4 → Fin 2 := ![0, 0, 1, 1]
private instance : DecidableRel (Setoid.ker lab).r := fun a b ↦
  inferInstanceAs (Decidable (lab a = lab b))
/-- `{{0, 1}, {2, 3}}`. -/
private def P₂ : Finpartition (Finset.univ : Finset (Fin 4)) :=
  Finpartition.ofSetSetoid (Setoid.ker lab) Finset.univ

-- The section `p = (· = 0)` on `{0,1,2,3}`: the indiscrete partition has defect
-- `2·1·3/4 = 3/2`; `P₂` has defect `2·1·1/2 + 0 = 1`; `⊥` has defect `0`.
example : partitionDefect (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) (fun a ↦ a = 0)
    = 3 / 2 := by
  have hparts : (⊤ : Finpartition (Finset.univ : Finset (Fin 4))).parts = {Finset.univ} := by
    decide
  unfold partitionDefect
  rw [hparts, Finset.sum_singleton,
    show sectionDisagreement (Finset.univ : Finset (Fin 4)) (fun a ↦ a = 0) = 6 by decide]
  norm_num
example : partitionDefect P₂ (fun a ↦ a = 0) = 1 := by
  have hparts : P₂.parts = {{0, 1}, {2, 3}} := by decide
  unfold partitionDefect
  rw [hparts, Finset.sum_pair (by decide)]
  rw [show sectionDisagreement ({0, 1} : Finset (Fin 4)) (fun a ↦ a = 0) = 2 by decide,
    show sectionDisagreement ({2, 3} : Finset (Fin 4)) (fun a ↦ a = 0) = 0 by decide]
  norm_num
example : partitionDefect (⊥ : Finpartition (Finset.univ : Finset (Fin 4))) (fun a ↦ a = 0) = 0 :=
  partitionDefect_bot _

-- **The variance term, numerically**: inside the single part `{0,1,2,3}` (density `1/4`) the fine
-- parts `{0,1}` (density `1/2`) and `{2,3}` (density `0`) contribute `2·(1/4)² + 2·(1/4)² = 1/4`.
example : sectionRefinementVariance P₂ (⊤ : Finpartition (Finset.univ : Finset (Fin 4)))
    (fun a ↦ a = 0) = 1 / 4 := by
  have htop : (⊤ : Finpartition (Finset.univ : Finset (Fin 4))).parts = {Finset.univ} := by
    decide
  have hfilt : P₂.parts.filter (· ⊆ (Finset.univ : Finset (Fin 4))) = {{0, 1}, {2, 3}} := by
    decide
  have d₀ : densityOn ({0, 1} : Finset (Fin 4)) (fun a ↦ a = 0) = 1 / 2 := by
    unfold densityOn
    rw [show (({0, 1} : Finset (Fin 4)).filter fun a ↦ a = 0).card = 1 by decide]; norm_num
  have d₁ : densityOn ({2, 3} : Finset (Fin 4)) (fun a ↦ a = 0) = 0 := by
    unfold densityOn
    rw [show (({2, 3} : Finset (Fin 4)).filter fun a ↦ a = 0).card = 0 by decide]; norm_num
  have dt : densityOn (Finset.univ : Finset (Fin 4)) (fun a ↦ a = 0) = 1 / 4 := by
    unfold densityOn
    rw [show ((Finset.univ : Finset (Fin 4)).filter fun a ↦ a = 0).card = 1 by decide]; norm_num
  unfold sectionRefinementVariance
  rw [htop, Finset.sum_singleton, hfilt, Finset.sum_pair (by decide), d₀, d₁, dt,
    Finset.card_pair (show (0 : Fin 4) ≠ 1 by decide), Finset.card_pair (show (2 : Fin 4) ≠ 3 by decide)]
  norm_num

-- **The exact identity on the instance**: `3/2 = 1 + 2 · (1/4)`, pinning the weighting and the
-- factor `2`.
example : partitionDefect (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) (fun a ↦ a = 0)
    = partitionDefect P₂ (fun a ↦ a = 0)
      + 2 * sectionRefinementVariance P₂ (⊤ : Finpartition (Finset.univ : Finset (Fin 4)))
          (fun a ↦ a = 0) :=
  partitionDefect_eq_add_refinementVariance _ le_top

-- **Monotonicity on the instance**: `P₂ ≤ ⊤`, and `1 ≤ 3/2`.
example : partitionDefect P₂ (fun a ↦ a = 0)
    ≤ partitionDefect (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) (fun a ↦ a = 0) :=
  partitionDefect_mono _ le_top

end Tests

end RegularityLemmata
