/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Uniformity
import Mathlib.Algebra.BigOperators.Field

/-!
# Directed regular-degree calculus

Phase 10 unit 3 (design freeze in `ARCHITECTURE.md`): the exceptional-degree bound for
a directed relation on a uniform pair, the prerequisite for path and triangle counting.

`degreeDensity R x B = pairDensity R {x} B` is the normalized out-degree of `x` into
`B`. The averaging identity `∑_{x ∈ A} degreeDensity R x B = pairDensity R A B · |A|`
(guard-free) expresses the pair density as an average of one-vertex degrees. The
**strict** exceptional tails
(`lowerDegreeExceptional`/`upperDegreeExceptional`, `ε < |degreeDensity − pairDensity|`
— equality at `ε` is *not* exceptional, matching the `≤ ε` uniformity convention) are
each bounded by `ε·|A|` (`card_lowerDegreeExceptional_le`,
`card_upperDegreeExceptional_le`), so their union — the absolute-deviation set — has
the safe bound **`2·ε·|A|`** (`card_degreeExceptional_le`), not `ε·|A|`: the two tails
are disjoint (`disjoint_lower_upper`) and can be simultaneously populated, so the union
mass genuinely reaches their sum (see the factor-two adversarial test), while uniformity
only bounds each tail on its own.

This is an independently authored directed, two-sided generalization; the lower-tail,
positive-density proof architecture is the private `badVertices` /
`card_badVertices_le` argument of `Mathlib.Combinatorics.SimpleGraph.Triangle.Counting`
(Y. Dillies, B. Mehta). `swapRel` and the transpose transport lemmas provide the
incoming-degree surface that path counting needs.
-/

namespace RegularityLemmata

variable {α : Type*} (R : α → α → Prop) [DecidableRel R] {A B T : Finset α} {ε : ℝ}

/-! ### One-vertex degrees and the averaging identity -/

/-- The normalized out-degree of `x` into `B` (guard-free: `0` on empty `B`). -/
noncomputable def degreeDensity (x : α) (B : Finset α) : ℝ := pairDensity R {x} B

/-- The out-degree of `x` counts the neighbours of `x` in `B`. -/
theorem pairCount_singleton_left (x : α) (B : Finset α) :
    pairCount R {x} B = (B.filter (R x ·)).card := by
  rw [pairCount]
  refine Finset.card_bij' (fun p _ => p.2) (fun b _ => (x, b)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
    exact Finset.mem_filter.mpr ⟨hp.1.2, hp.1.1 ▸ hp.2⟩
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hb.1⟩, hb.2⟩
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
    exact Prod.ext hp.1.1.symm rfl
  · intro b _
    rfl

theorem degreeDensity_eq (x : α) (B : Finset α) :
    degreeDensity R x B = ((B.filter (R x ·)).card : ℝ) / B.card := by
  rw [degreeDensity, pairDensity_eq_count_div, pairCount_singleton_left, Finset.card_singleton]
  norm_num

theorem degreeDensity_nonneg (x : α) (B : Finset α) : 0 ≤ degreeDensity R x B := by
  rw [degreeDensity_eq]; positivity

/-- Fiberwise degree sum for `pairCount`. -/
theorem pairCount_eq_sum_degree (A B : Finset α) :
    pairCount R A B = ∑ x ∈ A, (B.filter (R x ·)).card := by
  rw [pairCount, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm

/-- **The averaging identity** (guard-free): the pair density is the average of the
one-vertex degrees. -/
theorem sum_degreeDensity (A B : Finset α) :
    ∑ x ∈ A, degreeDensity R x B = pairDensity R A B * A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [degreeDensity_eq, pairDensity_eq_count_div]
  · have hAcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
    have hBcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hB).ne'
    have hcount : (∑ x ∈ A, ((B.filter (R x ·)).card : ℝ)) = (pairCount R A B : ℝ) := by
      rw [pairCount_eq_sum_degree, Nat.cast_sum]
    rw [Finset.sum_congr rfl fun x _ => degreeDensity_eq R x B, ← Finset.sum_div, hcount,
      pairDensity_eq_count_div]
    field_simp

/-- If every out-degree on a nonempty set is below `c`, so is the pair density. -/
theorem pairDensity_lt_of_forall_lt (hT : T.Nonempty) {c : ℝ}
    (h : ∀ x ∈ T, degreeDensity R x B < c) : pairDensity R T B < c := by
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hsum : ∑ x ∈ T, degreeDensity R x B < c * T.card := by
    calc ∑ x ∈ T, degreeDensity R x B < ∑ _x ∈ T, c := Finset.sum_lt_sum_of_nonempty hT h
      _ = c * T.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_degreeDensity] at hsum
  exact lt_of_mul_lt_mul_right hsum hcard.le

/-- If every out-degree on a nonempty set is above `c`, so is the pair density. -/
theorem lt_pairDensity_of_forall_lt (hT : T.Nonempty) {c : ℝ}
    (h : ∀ x ∈ T, c < degreeDensity R x B) : c < pairDensity R T B := by
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hsum : c * T.card < ∑ x ∈ T, degreeDensity R x B := by
    calc c * T.card = ∑ _x ∈ T, c := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ < ∑ x ∈ T, degreeDensity R x B := Finset.sum_lt_sum_of_nonempty hT h
  rw [sum_degreeDensity] at hsum
  exact lt_of_mul_lt_mul_right hsum hcard.le

/-! ### Transpose transport -/

/-- The transposed (incoming) relation. -/
def swapRel (R : α → α → Prop) : α → α → Prop := fun a b => R b a

instance (R : α → α → Prop) [DecidableRel R] : DecidableRel (swapRel R) :=
  fun a b => inferInstanceAs (Decidable (R b a))

theorem pairCount_swapRel (A B : Finset α) :
    pairCount (swapRel R) B A = pairCount R A B := by
  rw [pairCount, pairCount]
  refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1))
    (fun p hp => ?_) (fun p hp => ?_) (fun p _ => rfl) (fun p _ => rfl)
  · rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩

theorem pairDensity_swapRel (A B : Finset α) :
    pairDensity (swapRel R) B A = pairDensity R A B := by
  rw [pairDensity_eq_count_div, pairDensity_eq_count_div, pairCount_swapRel]; ring

/-- Uniformity transports to the transpose. -/
theorem isUniformPair_swapRel (hunif : IsUniformPair R A B ε) :
    IsUniformPair (swapRel R) B A ε := by
  intro B' hB' A' hA' hBc hAc
  rw [pairDensity_swapRel, pairDensity_swapRel]
  exact hunif hA' hB' hAc hBc

/-! ### The exceptional degree sets -/

/-- Left vertices whose out-degree strictly *undershoots* the pair density by `> ε`. -/
noncomputable def lowerDegreeExceptional (A B : Finset α) (ε : ℝ) : Finset α :=
  A.filter fun x => degreeDensity R x B < pairDensity R A B - ε

/-- Left vertices whose out-degree strictly *overshoots* the pair density by `> ε`. -/
noncomputable def upperDegreeExceptional (A B : Finset α) (ε : ℝ) : Finset α :=
  A.filter fun x => pairDensity R A B + ε < degreeDensity R x B

/-- The absolute-deviation exceptional set. -/
noncomputable def degreeExceptional [DecidableEq α] (A B : Finset α) (ε : ℝ) : Finset α :=
  lowerDegreeExceptional R A B ε ∪ upperDegreeExceptional R A B ε

/-- The two tails are disjoint once `0 ≤ ε`: no vertex both under- and overshoots. -/
theorem disjoint_lower_upper (hε : 0 ≤ ε) :
    Disjoint (lowerDegreeExceptional R A B ε) (upperDegreeExceptional R A B ε) := by
  rw [Finset.disjoint_left]
  intro x hxl hxu
  rw [lowerDegreeExceptional, Finset.mem_filter] at hxl
  rw [upperDegreeExceptional, Finset.mem_filter] at hxu
  linarith [hxl.2, hxu.2]

/-- **Lower-tail bound.** -/
theorem card_lowerDegreeExceptional_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((lowerDegreeExceptional R A B ε).card : ℝ) ≤ ε * A.card := by
  by_contra hcon
  push Not at hcon
  have hTA : lowerDegreeExceptional R A B ε ⊆ A := Finset.filter_subset _ _
  have hTne : (lowerDegreeExceptional R A B ε).Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (lowerDegreeExceptional R A B ε).card :=
      lt_of_le_of_lt (mul_nonneg hε0 (Nat.cast_nonneg _)) hcon
    exact_mod_cast h0
  have hBB : ε * (B.card : ℝ) ≤ (B.card : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hdev := hunif hTA (Finset.Subset.refl B) hcon.le hBB
  have hlt : pairDensity R (lowerDegreeExceptional R A B ε) B < pairDensity R A B - ε :=
    pairDensity_lt_of_forall_lt R hTne fun x hx => (Finset.mem_filter.mp hx).2
  rw [abs_le] at hdev
  linarith [hdev.1]

/-- **Upper-tail bound.** -/
theorem card_upperDegreeExceptional_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((upperDegreeExceptional R A B ε).card : ℝ) ≤ ε * A.card := by
  by_contra hcon
  push Not at hcon
  have hTA : upperDegreeExceptional R A B ε ⊆ A := Finset.filter_subset _ _
  have hTne : (upperDegreeExceptional R A B ε).Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (upperDegreeExceptional R A B ε).card :=
      lt_of_le_of_lt (mul_nonneg hε0 (Nat.cast_nonneg _)) hcon
    exact_mod_cast h0
  have hBB : ε * (B.card : ℝ) ≤ (B.card : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
  have hdev := hunif hTA (Finset.Subset.refl B) hcon.le hBB
  have hgt : pairDensity R A B + ε < pairDensity R (upperDegreeExceptional R A B ε) B :=
    lt_pairDensity_of_forall_lt R hTne fun x hx => (Finset.mem_filter.mp hx).2
  rw [abs_le] at hdev
  linarith [hdev.2]

/-- **The two-sided exceptional bound**: the absolute-deviation set has the *safe*
bound `2·ε·|A|`, because the two one-sided tails are bounded separately (uniformity
cannot be applied to the absolute set directly — see the factor-two test). -/
theorem card_degreeExceptional_le [DecidableEq α] (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hunif : IsUniformPair R A B ε) :
    ((degreeExceptional R A B ε).card : ℝ) ≤ 2 * ε * A.card := by
  have hl := card_lowerDegreeExceptional_le R hε0 hε1 hunif
  have hu := card_upperDegreeExceptional_le R hε0 hε1 hunif
  have hcard : ((degreeExceptional R A B ε).card : ℝ)
      ≤ (lowerDegreeExceptional R A B ε).card + (upperDegreeExceptional R A B ε).card := by
    rw [degreeExceptional]
    exact_mod_cast Finset.card_union_le _ _
  linarith

/-! ### Tests and adversarial examples -/

section Tests

-- Empty target: every out-degree is `0`, and (for `0 ≤ ε`) neither tail can be
-- exceptional, so the guard-free empty side is inert.
example (A : Finset (Fin 3)) (ε : ℝ) (hε : 0 ≤ ε) (x : Fin 3) :
    degreeDensity (fun a b : Fin 3 => a = b) x ∅ = 0
      ∧ lowerDegreeExceptional (fun a b : Fin 3 => a = b) A ∅ ε = ∅
      ∧ upperDegreeExceptional (fun a b : Fin 3 => a = b) A ∅ ε = ∅ := by
  have hd : pairDensity (fun a b : Fin 3 => a = b) A ∅ = 0 := by
    rw [pairDensity_eq_count_div]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [degreeDensity_eq]; simp
  · rw [lowerDegreeExceptional]
    refine Finset.filter_false_of_mem fun y _ => ?_
    rw [degreeDensity_eq, hd]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
    intro hlt; linarith
  · rw [upperDegreeExceptional]
    refine Finset.filter_false_of_mem fun y _ => ?_
    rw [degreeDensity_eq, hd]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
    intro hlt; linarith

-- A directed relation whose forward and transposed out-degrees differ: from vertex `0`,
-- the relation `a < b` reaches all of `{1, 2}` (forward degree `1`) while its transpose
-- reaches nothing (transposed degree `0`).
example :
    degreeDensity (fun a b : Fin 3 => (a : ℕ) < b) 0 {1, 2} = 1
      ∧ degreeDensity (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) 0 {1, 2} = 0 := by
  refine ⟨?_, ?_⟩
  · show pairDensity (fun a b : Fin 3 => (a : ℕ) < b) {0} {1, 2} = 1
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 3 => (a : ℕ) < b) {0} {1, 2} = 2 from by decide,
      show ({0} : Finset (Fin 3)).card = 1 from by decide,
      show ({1, 2} : Finset (Fin 3)).card = 2 from by decide]
    norm_num
  · show pairDensity (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) {0} {1, 2} = 0
    rw [pairDensity_eq_count_div,
      show pairCount (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) {0} {1, 2} = 0 from by decide]
    simp

-- **Factor-two adversarial test.** With `B = {2}` a single vertex, the pair density on
-- `A = {0, 1}` is `1/2`; vertex `0` has degree `0` (a *lower* deviant) and vertex `1`
-- has degree `1` (an *upper* deviant). At `ε = 1/4` both tails are simultaneously
-- populated and disjoint, so the absolute-deviation set has cardinality `2 = |lower| +
-- |upper|` — the union genuinely reaches the sum of the two `ε`-bounds, which is why the
-- union bound is `2·ε·|A|` and not `ε·|A|`.
example :
    (0 : Fin 3) ∈ lowerDegreeExceptional (fun a _ : Fin 3 => a = 1) {0, 1} {2} (1 / 4)
      ∧ (1 : Fin 3) ∈ upperDegreeExceptional (fun a _ : Fin 3 => a = 1) {0, 1} {2} (1 / 4)
      ∧ Disjoint (lowerDegreeExceptional (fun a _ : Fin 3 => a = 1) {0, 1} {2} (1 / 4))
          (upperDegreeExceptional (fun a _ : Fin 3 => a = 1) {0, 1} {2} (1 / 4)) := by
  have hpd : pairDensity (fun a _ : Fin 3 => a = 1) {0, 1} {2} = 1 / 2 := by
    rw [pairDensity_eq_count_div,
      show pairCount (fun a _ : Fin 3 => a = 1) {0, 1} {2} = 1 from by decide,
      show ({0, 1} : Finset (Fin 3)).card = 2 from by decide,
      show ({2} : Finset (Fin 3)).card = 1 from by decide]
    norm_num
  have hd0 : degreeDensity (fun a _ : Fin 3 => a = 1) 0 {2} = 0 := by
    show pairDensity (fun a _ : Fin 3 => a = 1) {0} {2} = 0
    rw [pairDensity_eq_count_div,
      show pairCount (fun a _ : Fin 3 => a = 1) {0} {2} = 0 from by decide]
    simp
  have hd1 : degreeDensity (fun a _ : Fin 3 => a = 1) 1 {2} = 1 := by
    show pairDensity (fun a _ : Fin 3 => a = 1) {1} {2} = 1
    rw [pairDensity_eq_count_div,
      show pairCount (fun a _ : Fin 3 => a = 1) {1} {2} = 1 from by decide,
      show ({1} : Finset (Fin 3)).card = 1 from by decide,
      show ({2} : Finset (Fin 3)).card = 1 from by decide]
    norm_num
  refine ⟨?_, ?_, disjoint_lower_upper _ (by norm_num)⟩
  · rw [lowerDegreeExceptional, Finset.mem_filter]
    exact ⟨by decide, by rw [hd0, hpd]; norm_num⟩
  · rw [upperDegreeExceptional, Finset.mem_filter]
    exact ⟨by decide, by rw [hd1, hpd]; norm_num⟩

-- The two-sided bound feeds any relation (statement-level).
example (R : Fin 4 → Fin 4 → Prop) [DecidableRel R] (A B : Finset (Fin 4)) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hunif : IsUniformPair R A B ε) :
    ((degreeExceptional R A B ε).card : ℝ) ≤ 2 * ε * A.card :=
  card_degreeExceptional_le R hε0 hε1 hunif

end Tests

end RegularityLemmata
