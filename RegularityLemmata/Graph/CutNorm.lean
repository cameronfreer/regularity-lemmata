/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Regularity

/-!
# Finite cut-norm approximation and Frieze–Kannan weak regularity

`steppedCount R P A B` is the count predicted by the partition-stepped relation:
each cell pair contributes its density times the trace masses `|A ∩ C| · |B ∩ D|`.
The **cut-deviation estimate** (`cut_deviation_le`): against an `ε`-regular
partition, the true count deviates from the stepped prediction, *uniformly over all
test sets* `A, B ⊆ s`, by at most `2ε·|s|² + Σ_C |C|²` — the diagonal term charged
explicitly, per the library's convention of postponing diagonal control to the
equitable bridge (for an equipartition with `k` parts it is `O(|s|²/k)`).

**The diagonal term is NOT controlled by this file's existential corollary**
(`exists_regular_partition_cut_deviation`): for `P = ⊤` it equals `|s|²` and the
conclusion is vacuous. The genuine finite Frieze–Kannan theorem — uniform `ε·|s|²`
cut approximation with a single-exponential part bound — is proved directly in
`Graph/FriezeKannan.lean`; the estimate here records how ordinary partition regularity
yields a cut bound once the diagonal mass `Σ|C|²` is separately controlled (e.g. by a
fine equipartition, where it is `O(|s|²/k)`).

`cutDiscrepancy` packages the maximum rectangle deviation as a finite supremum, with
the quantifier form as an elimination API (`cutDiscrepancy_le_iff`).

Everything here is finite: graphon (measure-theoretic) machinery is deliberately out of
scope. The analytic analogues — cut norm, step-function approximation — are formalized
in the author's graphon library (C. Freer, *Graphons in Lean 4*,
<https://github.com/cameronfreer/graphon>: `Graphon/CutNorm.lean`,
`Graphon/Approximation.lean`), whose development this file's finite statements
parallel; adapters may connect the two in a later release. Literature: A. Frieze and
R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19 (1999);
L. Lovász, *Large Networks and Graph Limits*, Part 2.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s A B : Finset α} {ε : ℝ}
variable (R : α → α → Prop) [DecidableRel R]

/-- The count predicted by the `P`-stepped relation on the test rectangle `(A, B)`. -/
noncomputable def steppedCount (P : Finpartition s) (A B : Finset α) : ℝ :=
  ∑ p ∈ P.parts ×ˢ P.parts,
    pairDensity R p.1 p.2 * ((A ∩ p.1).card : ℝ) * ((B ∩ p.2).card : ℝ)

/-- The pair count decomposes over cell traces. -/
theorem pairCount_eq_sum_inter (P : Finpartition s) (hA : A ⊆ s) (hB : B ⊆ s) :
    pairCount R A B = ∑ p ∈ P.parts ×ˢ P.parts, pairCount R (A ∩ p.1) (B ∩ p.2) := by
  classical
  have hset : (A ×ˢ B).filter (fun q => R q.1 q.2)
      = (P.parts ×ˢ P.parts).biUnion
          (fun p => ((A ∩ p.1) ×ˢ (B ∩ p.2)).filter (fun q => R q.1 q.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_inter,
      Prod.exists]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hR⟩
      obtain ⟨C, hC, hq1C⟩ := P.exists_mem (hA hq1)
      obtain ⟨D, hD, hq2D⟩ := P.exists_mem (hB hq2)
      exact ⟨C, D, ⟨hC, hD⟩, ⟨⟨hq1, hq1C⟩, hq2, hq2D⟩, hR⟩
    · rintro ⟨C, D, ⟨_, _⟩, ⟨⟨hq1, _⟩, hq2, _⟩, hR⟩
      exact ⟨⟨hq1, hq2⟩, hR⟩
  have hdisj : ∀ p ∈ P.parts ×ˢ P.parts, ∀ p' ∈ P.parts ×ˢ P.parts, p ≠ p' →
      Disjoint (((A ∩ p.1) ×ˢ (B ∩ p.2)).filter (fun q => R q.1 q.2))
        (((A ∩ p'.1) ×ˢ (B ∩ p'.2)).filter (fun q => R q.1 q.2)) := by
    intro p hp p' hp' hne
    rw [Finset.mem_product] at hp hp'
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_inter] at hxy hxy'
    refine hne (Prod.ext ?_ ?_)
    · exact P.eq_of_mem_parts hp.1 hp'.1 hxy.1.1.2 hxy'.1.1.2
    · exact P.eq_of_mem_parts hp.2 hp'.2 hxy.1.2.2 hxy'.1.2.2
  rw [pairCount, hset, Finset.card_biUnion hdisj]
  rfl

/-- **Cut-deviation estimate (Frieze–Kannan form).** Against an `ε`-regular
partition, the stepped prediction is uniformly cut-close to the true count: for all
test sets `A, B ⊆ s`,
`|count − predicted| ≤ 2ε·|s|² + Σ_C |C|²` (diagonal blocks charged explicitly). -/
theorem cut_deviation_le {P : Finpartition s} (hreg : IsRegularPartition R ε P) (hε : 0 ≤ ε)
    (hA : A ⊆ s) (hB : B ⊆ s) :
    |(pairCount R A B : ℝ) - steppedCount R P A B|
      ≤ 2 * ε * (s.card : ℝ) ^ 2 + ∑ C ∈ P.parts, (C.card : ℝ) ^ 2 := by
  classical
  have hdecomp : (pairCount R A B : ℝ) - steppedCount R P A B
      = ∑ p ∈ P.parts ×ˢ P.parts,
          ((pairCount R (A ∩ p.1) (B ∩ p.2) : ℝ)
            - pairDensity R p.1 p.2 * ((A ∩ p.1).card : ℝ) * ((B ∩ p.2).card : ℝ)) := by
    rw [steppedCount, pairCount_eq_sum_inter R P hA hB, Nat.cast_sum,
      Finset.sum_sub_distrib]
  rw [hdecomp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpair : ∀ p ∈ P.parts ×ˢ P.parts,
      |(pairCount R (A ∩ p.1) (B ∩ p.2) : ℝ)
          - pairDensity R p.1 p.2 * ((A ∩ p.1).card : ℝ) * ((B ∩ p.2).card : ℝ)|
        ≤ (if IsBadPair R ε p.1 p.2 ∨ p.1 = p.2 then ((p.1.card : ℝ) * p.2.card)
            else ε * ((p.1.card : ℝ) * p.2.card)) := by
    rintro ⟨C, D⟩ hp
    rw [Finset.mem_product] at hp
    set m : ℝ := ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ) with hm
    have hm0 : 0 ≤ m := by positivity
    have hmC : ((A ∩ C).card : ℝ) ≤ C.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
    have hmD : ((B ∩ D).card : ℝ) ≤ D.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
    have hmm : m ≤ (C.card : ℝ) * D.card :=
      mul_le_mul hmC hmD (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hcnt : (pairCount R (A ∩ C) (B ∩ D) : ℝ)
        = pairDensity R (A ∩ C) (B ∩ D) * m := pairCount_eq_pairDensity_mul
    have habs : |(pairCount R (A ∩ C) (B ∩ D) : ℝ)
        - pairDensity R C D * ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ)|
        = |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| * m := by
      rw [hcnt, show pairDensity R C D * ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ)
          = pairDensity R C D * m from by rw [hm]; ring,
        ← sub_mul, abs_mul, abs_of_nonneg hm0]
    rw [habs]
    have hdev1 : |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| ≤ 1 := by
      have h1 := pairDensity_le_one (R := R) (A := A ∩ C) (B := B ∩ D)
      have h2 := pairDensity_nonneg (R := R) (A := A ∩ C) (B := B ∩ D)
      have h3 := pairDensity_le_one (R := R) (A := C) (B := D)
      have h4 := pairDensity_nonneg (R := R) (A := C) (B := D)
      rw [abs_le]
      constructor <;> linarith
    by_cases hcase : IsBadPair R ε C D ∨ C = D
    · rw [if_pos hcase]
      calc |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| * m
          ≤ 1 * m := mul_le_mul_of_nonneg_right hdev1 hm0
        _ = m := one_mul m
        _ ≤ (C.card : ℝ) * D.card := hmm
    · rw [if_neg hcase]
      push Not at hcase
      have hunif : IsUniformPair R C D ε := by
        rcases hcase with ⟨hbad, hne⟩
        by_contra hn
        exact hbad ⟨hne, hn⟩
      by_cases hsmallA : ((A ∩ C).card : ℝ) < ε * C.card
      · calc |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| * m
            ≤ 1 * m := mul_le_mul_of_nonneg_right hdev1 hm0
          _ = ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ) := by rw [one_mul, hm]
          _ ≤ (ε * C.card) * D.card := by
              refine mul_le_mul hsmallA.le hmD (Nat.cast_nonneg _) ?_
              positivity
          _ = ε * ((C.card : ℝ) * D.card) := by ring
      · by_cases hsmallB : ((B ∩ D).card : ℝ) < ε * D.card
        · calc |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| * m
              ≤ 1 * m := mul_le_mul_of_nonneg_right hdev1 hm0
            _ = ((A ∩ C).card : ℝ) * ((B ∩ D).card : ℝ) := by rw [one_mul, hm]
            _ ≤ (C.card : ℝ) * (ε * D.card) := by
                refine mul_le_mul hmC hsmallB.le ?_ (Nat.cast_nonneg _)
                positivity
            _ = ε * ((C.card : ℝ) * D.card) := by ring
        · push Not at hsmallA hsmallB
          have hdev := hunif Finset.inter_subset_right
            Finset.inter_subset_right hsmallA hsmallB
          calc |pairDensity R (A ∩ C) (B ∩ D) - pairDensity R C D| * m
              ≤ ε * m := mul_le_mul_of_nonneg_right hdev hm0
            _ ≤ ε * ((C.card : ℝ) * D.card) := mul_le_mul_of_nonneg_left hmm hε
  refine (Finset.sum_le_sum hpair).trans ?_
  have hsplit : ∑ p ∈ P.parts ×ˢ P.parts,
      (if IsBadPair R ε p.1 p.2 ∨ p.1 = p.2 then ((p.1.card : ℝ) * p.2.card)
        else ε * ((p.1.card : ℝ) * p.2.card))
      ≤ (badMassNum R ε P + ∑ C ∈ P.parts, (C.card : ℝ) ^ 2)
        + ε * ∑ p ∈ P.parts ×ˢ P.parts, ((p.1.card : ℝ) * p.2.card) := by
    have hterm : ∀ p ∈ P.parts ×ˢ P.parts,
        (if IsBadPair R ε p.1 p.2 ∨ p.1 = p.2 then ((p.1.card : ℝ) * p.2.card)
          else ε * ((p.1.card : ℝ) * p.2.card))
        ≤ ((if IsBadPair R ε p.1 p.2 then ((p.1.card : ℝ) * p.2.card) else 0)
            + (if p.1 = p.2 then ((p.1.card : ℝ) * p.2.card) else 0))
          + ε * ((p.1.card : ℝ) * p.2.card) := by
      intro p _
      have hnn : (0 : ℝ) ≤ (p.1.card : ℝ) * p.2.card := by positivity
      have hεnn : (0 : ℝ) ≤ ε * ((p.1.card : ℝ) * p.2.card) := by positivity
      by_cases h1 : IsBadPair R ε p.1 p.2
      · rw [if_pos (Or.inl h1), if_pos h1]
        have : (0:ℝ) ≤ (if p.1 = p.2 then ((p.1.card : ℝ) * p.2.card) else 0) := by
          split_ifs <;> simp [hnn]
        linarith
      · by_cases h2 : p.1 = p.2
        · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
          linarith
        · rw [if_neg (by tauto), if_neg h1, if_neg h2]
          linarith
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ p ∈ P.parts ×ˢ P.parts,
        (if IsBadPair R ε p.1 p.2 then ((p.1.card : ℝ) * p.2.card) else 0)
        = badMassNum R ε P := by
      rw [badMassNum, Finset.sum_filter]
    have h2 : ∑ p ∈ P.parts ×ˢ P.parts,
        (if p.1 = p.2 then ((p.1.card : ℝ) * p.2.card) else 0)
        = ∑ C ∈ P.parts, (C.card : ℝ) ^ 2 := by
      rw [← Finset.sum_filter]
      have hdiag : (P.parts ×ˢ P.parts).filter (fun p => p.1 = p.2)
          = P.parts.diag := by
        ext p
        simp only [Finset.mem_diag, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2 ▸ h1⟩, h2⟩
      rw [hdiag, Finset.sum_diag]
      exact Finset.sum_congr rfl fun C _ => (sq ((C.card : ℝ))).symm
    have h3 : ∑ p ∈ P.parts ×ˢ P.parts, ε * ((p.1.card : ℝ) * p.2.card)
        = ε * ∑ p ∈ P.parts ×ˢ P.parts, ((p.1.card : ℝ) * p.2.card) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1, h2, h3]
  refine hsplit.trans ?_
  have hmass : ∑ p ∈ P.parts ×ˢ P.parts, ((p.1.card : ℝ) * p.2.card) = (s.card : ℝ) ^ 2 := by
    calc ∑ p ∈ P.parts ×ˢ P.parts, ((p.1.card : ℝ) * p.2.card)
        = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
          rw [Finset.sum_mul_sum, Finset.sum_product]
      _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]
  have hbm : badMassNum R ε P ≤ ε * (s.card : ℝ) ^ 2 :=
    badMassNum_le_of_isRegularPartition R ε hreg
  rw [hmass]
  linarith

/-- Cut deviation of a regular partition, **with an uncontrolled diagonal term**: this
is NOT a Frieze–Kannan approximation (take `P = ⊤`); see `Graph/FriezeKannan.lean` for
the genuine theorem. -/
theorem exists_regular_partition_cut_deviation (hε : 0 < ε) :
    ∃ P : Finpartition s, P.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ 1 ∧
      ∀ A ⊆ s, ∀ B ⊆ s,
        |(pairCount R A B : ℝ) - steppedCount R P A B|
          ≤ 2 * ε * (s.card : ℝ) ^ 2 + ∑ C ∈ P.parts, (C.card : ℝ) ^ 2 := by
  obtain ⟨P, _, hreg, hcard⟩ := exists_regular_refinement R ⊤ hε
  refine ⟨P, le_trans hcard (regularityBound_mono _ parts_top_card_le_one), ?_⟩
  intro A hA B hB
  exact cut_deviation_le R hreg hε.le hA hB

/-! ### Cut discrepancy as a finite supremum -/

/-- The cut discrepancy of `R` against the `P`-stepped approximation: the maximum
rectangle deviation over all test sets `A, B ⊆ s`. -/
noncomputable def cutDiscrepancy (P : Finpartition s) : ℝ :=
  (s.powerset ×ˢ s.powerset).sup'
    (Finset.Nonempty.product ⟨∅, Finset.empty_mem_powerset s⟩
      ⟨∅, Finset.empty_mem_powerset s⟩)
    fun p => |(pairCount R p.1 p.2 : ℝ) - steppedCount R P p.1 p.2|

/-- Elimination API: bounding the cut discrepancy is exactly the quantified rectangle
bound. -/
theorem cutDiscrepancy_le_iff {P : Finpartition s} {c : ℝ} :
    cutDiscrepancy R P ≤ c ↔ ∀ A ⊆ s, ∀ B ⊆ s,
      |(pairCount R A B : ℝ) - steppedCount R P A B| ≤ c := by
  rw [cutDiscrepancy, Finset.sup'_le_iff]
  constructor
  · intro h A hA B hB
    exact h (A, B) (Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hA, Finset.mem_powerset.mpr hB⟩)
  · rintro h ⟨A, B⟩ hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    exact h A hp.1 B hp.2

/-! ### Tests and adversarial examples -/

-- The stepped count against ⊥ (singletons) reproduces the count exactly:
-- deviation 0 on a concrete instance.
example :
    (pairCount (fun a b : Fin 2 => a < b) Finset.univ Finset.univ : ℝ)
      - steppedCount (fun a b : Fin 2 => a < b)
          (⊥ : Finpartition (Finset.univ : Finset (Fin 2))) Finset.univ Finset.univ
      = 0 := by
  rw [steppedCount,
    show (⊥ : Finpartition (Finset.univ : Finset (Fin 2))).parts = {{0}, {1}} from by decide]
  have h2 : ({0} : Finset (Fin 2)) ≠ {1} := by decide
  rw [Finset.sum_product, Finset.sum_pair h2, Finset.sum_pair h2, Finset.sum_pair h2]
  norm_num [pairDensity_eq_count_div,
    show pairCount (fun a b : Fin 2 => a < b) Finset.univ Finset.univ = 1 from by decide,
    show pairCount (fun a b : Fin 2 => a < b) {0} {0} = 0 from by decide,
    show pairCount (fun a b : Fin 2 => a < b) {0} {1} = 1 from by decide,
    show pairCount (fun a b : Fin 2 => a < b) {1} {0} = 0 from by decide,
    show pairCount (fun a b : Fin 2 => a < b) {1} {1} = 0 from by decide,
    show (Finset.univ ∩ ({0} : Finset (Fin 2))).card = 1 from by decide,
    show (Finset.univ ∩ ({1} : Finset (Fin 2))).card = 1 from by decide]

-- NONTRIVIAL: against ⊤ the stepped approximation has POSITIVE discrepancy — for
-- `R a b ↔ a = 0 ∧ b = 0` on `Fin 2`, the rectangle ({0}, {0}) has count 1 but
-- predicted mass 1/4 (whole-box density 1/4 times trace masses 1·1).
example :
    |(pairCount (fun a b : Fin 2 => a = 0 ∧ b = 0) {0} {0} : ℝ)
      - steppedCount (fun a b : Fin 2 => a = 0 ∧ b = 0)
          (⊤ : Finpartition (Finset.univ : Finset (Fin 2))) {0} {0}| = 3 / 4 := by
  rw [steppedCount,
    show (⊤ : Finpartition (Finset.univ : Finset (Fin 2))).parts = {Finset.univ} from by
      decide,
    Finset.singleton_product_singleton, Finset.sum_singleton, pairDensity_eq_count_div,
    show pairCount (fun a b : Fin 2 => a = 0 ∧ b = 0) {0} {0} = 1 from by decide,
    show pairCount (fun a b : Fin 2 => a = 0 ∧ b = 0) Finset.univ Finset.univ = 1 from by
      decide,
    show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
    show (({0} : Finset (Fin 2)) ∩ Finset.univ).card = 1 from by decide]
  norm_num

end RegularityLemmata
