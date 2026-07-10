import RegularityLemmata.Finite.Density

/-!
# Pair counts and pair density

`pairCount R A B` counts the pairs of `A ×ˢ B` related by `R`; `pairDensity` is the
corresponding density (zero when a side is empty, by the division convention). The
additivity lemma `pairCount_biUnion` over two-dimensional disjoint covers is the
counting backbone of block-energy superadditivity.
-/

namespace RegularityLemmata

variable {α : Type*}
variable {R : α → α → Prop} [DecidableRel R] {A B : Finset α}

/-- Number of `R`-related pairs in `A ×ˢ B`. -/
def pairCount (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℕ :=
  ((A ×ˢ B).filter fun p => R p.1 p.2).card

/-- Density of `R` on `A ×ˢ B`; `0` if a side is empty. -/
noncomputable def pairDensity (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℝ :=
  densityOn (A ×ˢ B) fun p => R p.1 p.2

/-- Guard-free division form: agrees with `densityOn` since `x / 0 = 0`. -/
theorem pairDensity_eq_count_div :
    pairDensity R A B = (pairCount R A B : ℝ) / (((A.card) : ℝ) * B.card) := by
  rw [pairDensity, densityOn, pairCount, Finset.card_product, Nat.cast_mul]

theorem pairDensity_nonneg : 0 ≤ pairDensity R A B := densityOn_nonneg

theorem pairDensity_le_one : pairDensity R A B ≤ 1 := densityOn_le_one

/-- Raw count from a density: `#pairs = d·|A||B|` when both sides are nonempty. -/
theorem pairCount_eq_pairDensity_mul (hA : A.Nonempty) (hB : B.Nonempty) :
    (pairCount R A B : ℝ) = pairDensity R A B * (((A.card) : ℝ) * B.card) := by
  have hpos : (0 : ℝ) < ((A.card) : ℝ) * B.card := by
    have h1 : (0 : ℝ) < A.card := by exact_mod_cast A.card_pos.mpr hA
    have h2 : (0 : ℝ) < B.card := by exact_mod_cast B.card_pos.mpr hB
    exact mul_pos h1 h2
  rw [pairDensity_eq_count_div, div_mul_cancel₀]
  exact hpos.ne'

/-- Sum of part cardinalities over a disjoint cover of `C` equals `|C|` (real cast). -/
theorem sum_card_biUnion_cast [DecidableEq α] {C : Finset α} (sC : Finset (Finset α))
    (hdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hcover : sC.biUnion id = C) :
    (∑ C' ∈ sC, (C'.card : ℝ)) = (C.card : ℝ) := by
  have h : (sC.biUnion id).card = ∑ C' ∈ sC, (id C').card :=
    Finset.card_biUnion fun x hx y hy hne => hdisj hx hy hne
  rw [hcover] at h
  simp only [id_eq] at h
  rw [h, Nat.cast_sum]

/-- The pair count is additive over a two-dimensional disjoint cover:
`C = ⊔ sC`, `D = ⊔ sD`. -/
theorem pairCount_biUnion [DecidableEq α] (R : α → α → Prop) [DecidableRel R] {C D : Finset α}
    (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    pairCount R C D = ∑ p ∈ sC ×ˢ sD, pairCount R p.1 p.2 := by
  have hset : (C ×ˢ D).filter (fun q => R q.1 q.2)
      = (sC ×ˢ sD).biUnion (fun p => (p.1 ×ˢ p.2).filter (fun q => R q.1 q.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Prod.exists]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hR⟩
      rw [← hCcover, Finset.mem_biUnion] at hq1
      rw [← hDcover, Finset.mem_biUnion] at hq2
      obtain ⟨C', hC', hq1'⟩ := hq1
      obtain ⟨D', hD', hq2'⟩ := hq2
      simp only [id_eq] at hq1' hq2'
      exact ⟨C', D', ⟨hC', hD'⟩, ⟨hq1', hq2'⟩, hR⟩
    · rintro ⟨C', D', ⟨hC', hD'⟩, ⟨hq1, hq2⟩, hR⟩
      refine ⟨⟨?_, ?_⟩, hR⟩
      · rw [← hCcover, Finset.mem_biUnion]; exact ⟨C', hC', by simpa using hq1⟩
      · rw [← hDcover, Finset.mem_biUnion]; exact ⟨D', hD', by simpa using hq2⟩
  have hdisj : ∀ p ∈ sC ×ˢ sD, ∀ p' ∈ sC ×ˢ sD, p ≠ p' →
      Disjoint ((p.1 ×ˢ p.2).filter (fun q => R q.1 q.2))
        ((p'.1 ×ˢ p'.2).filter (fun q => R q.1 q.2)) := by
    intro p hp p' hp' hne
    rw [Finset.mem_product] at hp hp'
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    rw [Finset.mem_filter, Finset.mem_product] at hxy hxy'
    by_cases hC : p.1 = p'.1
    · have hD : p.2 ≠ p'.2 := fun h => hne (Prod.ext hC h)
      exact (Finset.disjoint_left.mp (hDdisj hp.2 hp'.2 hD)) hxy.1.2 hxy'.1.2
    · exact (Finset.disjoint_left.mp (hCdisj hp.1 hp'.1 hC)) hxy.1.1 hxy'.1.1
  unfold pairCount
  rw [hset, Finset.card_biUnion hdisj]

/-! ### Tests and adversarial examples -/

-- The strict-order relation on `Fin 3` relates 3 of the 9 pairs.
example : pairCount (fun a b : Fin 3 => a < b) Finset.univ Finset.univ = 3 := by decide

-- Empty sides give zero density (division convention).
example : pairDensity (fun _ _ : Fin 3 => True) ∅ Finset.univ = 0 := by
  rw [pairDensity_eq_count_div]
  simp

-- Additivity over the split {0} ∪ {1,2} of the C side (a concrete 2+1 cover).
example :
    pairCount (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
      = ∑ p ∈ ({({0} : Finset (Fin 3)), {1, 2}} : Finset (Finset (Fin 3)))
          ×ˢ ({Finset.univ} : Finset (Finset (Fin 3))), pairCount (· < ·) p.1 p.2 := by
  decide

end RegularityLemmata
