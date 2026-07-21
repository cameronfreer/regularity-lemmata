/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.UniformSlicing

/-!
# Route (b) step 1: the equal-cardinality union theorem

`ARCHITECTURE.md` route (b) ladder, step 1, first commit (design freeze 2026-07-20;
reviewer-specified statement 2026-07-21): a union of `s` pairwise-disjoint pieces of
COMMON positive cardinality, with every ordered pair of distinct pieces `α`-uniform
and all those densities within `α` of a common `d ∈ [0, 1]`, is close to `d` on every
pair of `ε`-large test sets, with the exact four-term error

    |density(X, Y) − density(U, U)| ≤ 3α + 2α/ε + 1/(s·ε) + 1/s

whose terms have stable meanings: `3α` — pair regularity, density-class width, and
comparison of `density(U, U)` with the class center; `2α/ε` — pieces on which `X` or
`Y` is too small to invoke pair regularity; `1/(s·ε)` — the uncontrolled within-piece
contribution inside `X × Y`; `1/s` — the within-piece contribution to
`density(U, U)`. The diagonal bound is the equal-size estimate
`Σᵢ |X∩Aᵢ|·|Y∩Aᵢ| ≤ m·min(|X|,|Y|)`, which after division by `|X||Y| ≥ (ε·s·m)²`
costs `1/(s·ε)` — NOT `1/(s·ε²)`; this is what makes `α = (ε/3)²`, `s ≥ 2/α` viable
(`isUniformPair_self_union`, displayed error at most `2ε/3`).

Equal cardinality is a genuine hypothesis: comparable-but-unequal pieces incur a
comparability factor `Λ` in both within-piece terms (adversarial test below), and the
frozen design trims comparable pieces to equal size FIRST via
`Graph/UniformSlicing.lean`. The `α·m ≤ |X∩Aᵢ|` cutoff is inclusive: equality enters
the regularity-controlled case (pinned by a permanent test), matching the inclusive
largeness of `IsUniformPair`.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {R : V → V → Prop} [DecidableRel R]

/-! ### Exact decompositions over an indexed disjoint family -/

/-- A subset of an indexed disjoint union decomposes exactly over the pieces. This is
the indexed form (pieces may coincide as SETS only when empty, but the index keeps
them apart — the set-indexed `pairCount_biUnion` cannot be reused). -/
theorem card_eq_sum_card_inter {s : ℕ} (A : Fin s → Finset V)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    {X : Finset V} (hX : X ⊆ Finset.univ.biUnion A) :
    X.card = ∑ i : Fin s, (X ∩ A i).card := by
  classical
  have hcover : X = Finset.univ.biUnion (fun i => X ∩ A i) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hX hx)
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, -⟩
      exact hx
  conv_lhs => rw [hcover]
  exact Finset.card_biUnion fun i _ j _ hij =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj i j hij))

/-- **Exact pair-count decomposition** of test sets over an indexed disjoint family
(the `Fin`-indexed sibling of `Graph/CutNorm.lean`'s Finpartition-indexed
`pairCount_eq_sum_inter`: an INDEXED family keeps coinciding intersection pieces
apart, which a set-indexed cover cannot). -/
theorem pairCount_eq_sum_inter_fin {s : ℕ} (R : V → V → Prop) [DecidableRel R]
    (A : Fin s → Finset V) (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    {X Y : Finset V} (hX : X ⊆ Finset.univ.biUnion A)
    (hY : Y ⊆ Finset.univ.biUnion A) :
    pairCount R X Y
      = ∑ i : Fin s, ∑ j : Fin s, pairCount R (X ∩ A i) (Y ∩ A j) := by
  classical
  unfold pairCount
  have hset : (X ×ˢ Y).filter (fun q => R q.1 q.2)
      = (Finset.univ : Finset (Fin s × Fin s)).biUnion
          (fun p => ((X ∩ A p.1) ×ˢ (Y ∩ A p.2)).filter (fun q => R q.1 q.2)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_inter, Prod.exists]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hR⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hX hq1)
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (hY hq2)
      exact ⟨i, j, ⟨⟨hq1, hi⟩, hq2, hj⟩, hR⟩
    · rintro ⟨i, j, ⟨⟨hq1, -⟩, hq2, -⟩, hR⟩
      exact ⟨⟨hq1, hq2⟩, hR⟩
  have hd : ∀ p ∈ (Finset.univ : Finset (Fin s × Fin s)),
      ∀ p' ∈ (Finset.univ : Finset (Fin s × Fin s)), p ≠ p' →
      Disjoint (((X ∩ A p.1) ×ˢ (Y ∩ A p.2)).filter (fun q => R q.1 q.2))
        (((X ∩ A p'.1) ×ˢ (Y ∩ A p'.2)).filter (fun q => R q.1 q.2)) := by
    intro p _ p' _ hne
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_inter]
      at hxy hxy'
    by_cases hfst : p.1 = p'.1
    · have hsnd : p.2 ≠ p'.2 := fun h => hne (Prod.ext hfst h)
      exact (Finset.disjoint_left.mp (hdisj p.2 p'.2 hsnd)) hxy.1.2.2 hxy'.1.2.2
    · exact (Finset.disjoint_left.mp (hdisj p.1 p'.1 hfst)) hxy.1.1.2 hxy'.1.1.2
  rw [hset, Finset.card_biUnion hd, ← Fintype.sum_prod_type']

omit [DecidableEq V] in
/-- The trivial pair-count bound by the rectangle. -/
theorem pairCount_le_mul (R : V → V → Prop) [DecidableRel R] (A B : Finset V) :
    pairCount R A B ≤ A.card * B.card :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product _ _))

/-! ### The union estimates -/

section Union

variable {s m : ℕ} {A : Fin s → Finset V} {α d ε : ℝ} {U X Y : Finset V}

/-- The disjoint union of `s` pieces of common cardinality `m` has `s·m` vertices. -/
theorem card_biUnion_const
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m) :
    (Finset.univ.biUnion A).card = s * m := by
  rw [Finset.card_biUnion fun i _ j _ hij => hdisj i j hij,
    Finset.sum_congr rfl fun i _ => hcard i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Test sets against the class center.** On `ε`-large `X, Y ⊆ U` the density is
within `2α + 2α/ε + 1/(s·ε)` of the common off-diagonal density `d`: `2α` from pair
regularity plus class width on the regularity-controlled blocks, `2α/ε` from pieces
where `X` or `Y` is below the (inclusive) `α·m` cutoff, and `1/(s·ε)` from the
equal-size diagonal bound `Σᵢ |X∩Aᵢ|·|Y∩Aᵢ| ≤ m·|Y|`. -/
theorem pairDensity_union_close_center (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hα : 0 < α) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) α)
    (hclose : ∀ i j : Fin s, i ≠ j → |pairDensity R (A i) (A j) - d| ≤ α)
    (hU : U = Finset.univ.biUnion A) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hε : 0 < ε) (hXl : ε * (U.card : ℝ) ≤ (X.card : ℝ))
    (hYl : ε * (U.card : ℝ) ≤ (Y.card : ℝ)) :
    |pairDensity R X Y - d| ≤ 2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) := by
  classical
  subst hU
  set xi : Fin s → ℝ := fun i => ((X ∩ A i).card : ℝ) with hxi
  set yj : Fin s → ℝ := fun j => ((Y ∩ A j).card : ℝ) with hyj
  set cij : Fin s → Fin s → ℝ :=
    fun i j => ((pairCount R (X ∩ A i) (Y ∩ A j)) : ℝ) with hcij
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxi_nn : ∀ i, 0 ≤ xi i := fun i => Nat.cast_nonneg _
  have hyj_nn : ∀ j, 0 ≤ yj j := fun j => Nat.cast_nonneg _
  have hxi_le : ∀ i, xi i ≤ (m : ℝ) := fun i => by
    have h := Finset.card_le_card (Finset.inter_subset_right (s₁ := X) (s₂ := A i))
    rw [hcard i] at h
    show ((X ∩ A i).card : ℝ) ≤ (m : ℝ)
    exact_mod_cast h
  have hyj_le : ∀ j, yj j ≤ (m : ℝ) := fun j => by
    have h := Finset.card_le_card (Finset.inter_subset_right (s₁ := Y) (s₂ := A j))
    rw [hcard j] at h
    show ((Y ∩ A j).card : ℝ) ≤ (m : ℝ)
    exact_mod_cast h
  have hXC : (X.card : ℝ) = ∑ i, xi i := by
    rw [card_eq_sum_card_inter A hdisj hX]
    push_cast
    rfl
  have hYC : (Y.card : ℝ) = ∑ j, yj j := by
    rw [card_eq_sum_card_inter A hdisj hY]
    push_cast
    rfl
  have hUc : ((Finset.univ.biUnion A).card : ℝ) = (s : ℝ) * m := by
    exact_mod_cast card_biUnion_const hdisj hcard
  have hXlb : ε * ((s : ℝ) * m) ≤ (X.card : ℝ) := by rwa [hUc] at hXl
  have hYlb : ε * ((s : ℝ) * m) ≤ (Y.card : ℝ) := by rwa [hUc] at hYl
  have hXpos : 0 < (X.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hε (mul_pos hsR hmR)) hXlb
  have hYpos : 0 < (Y.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hε (mul_pos hsR hmR)) hYlb
  -- The regularity-controlled per-block density bound.
  have hgood : ∀ i j : Fin s, i ≠ j → α * m ≤ xi i → α * m ≤ yj j →
      |pairDensity R (X ∩ A i) (Y ∩ A j) - d| ≤ 2 * α := by
    intro i j hij hxlarge hylarge
    have hAi : α * ((A i).card : ℝ) ≤ ((X ∩ A i).card : ℝ) := by
      rw [show ((A i).card : ℝ) = (m : ℝ) by exact_mod_cast hcard i]
      exact hxlarge
    have hAj : α * ((A j).card : ℝ) ≤ ((Y ∩ A j).card : ℝ) := by
      rw [show ((A j).card : ℝ) = (m : ℝ) by exact_mod_cast hcard j]
      exact hylarge
    have h1 := hunif i j hij Finset.inter_subset_right Finset.inter_subset_right hAi hAj
    have h2 := hclose i j hij
    calc |pairDensity R (X ∩ A i) (Y ∩ A j) - d|
        ≤ |pairDensity R (X ∩ A i) (Y ∩ A j) - pairDensity R (A i) (A j)|
          + |pairDensity R (A i) (A j) - d| := abs_sub_le _ _ _
      _ ≤ α + α := add_le_add h1 h2
      _ = 2 * α := by ring
  -- Per-block count bounds, in the four-case shape summed below.
  have hkey_up : ∀ i j : Fin s, cij i j
      ≤ (d + 2 * α) * (xi i * yj j)
        + ((if i = j then xi i * yj j else 0)
          + ((if xi i < α * m then xi i * yj j else 0)
            + (if yj j < α * m then xi i * yj j else 0))) := by
    intro i j
    have hcle : cij i j ≤ xi i * yj j := by
      show ((pairCount R (X ∩ A i) (Y ∩ A j) : ℝ))
          ≤ ((X ∩ A i).card : ℝ) * ((Y ∩ A j).card : ℝ)
      exact_mod_cast pairCount_le_mul R (X ∩ A i) (Y ∩ A j)
    have hxynn : 0 ≤ xi i * yj j := mul_nonneg (hxi_nn i) (hyj_nn j)
    have hdxy : 0 ≤ (d + 2 * α) * (xi i * yj j) :=
      mul_nonneg (by linarith) hxynn
    by_cases hij : i = j
    · simp only [if_pos hij]
      have h1 : (0 : ℝ) ≤ if xi i < α * m then xi i * yj j else 0 := by positivity
      have h2 : (0 : ℝ) ≤ if yj j < α * m then xi i * yj j else 0 := by positivity
      linarith
    by_cases hx : xi i < α * m
    · simp only [if_neg hij, if_pos hx]
      have h2 : (0 : ℝ) ≤ if yj j < α * m then xi i * yj j else 0 := by positivity
      linarith
    by_cases hy : yj j < α * m
    · simp only [if_neg hij, if_neg hx, if_pos hy]
      linarith
    · simp only [if_neg hij, if_neg hx, if_neg hy, add_zero]
      have h2α := (abs_le.mp (hgood i j hij (le_of_not_gt hx) (le_of_not_gt hy))).2
      have hcount : cij i j
          = pairDensity R (X ∩ A i) (Y ∩ A j) * (xi i * yj j) := by
        show ((pairCount R (X ∩ A i) (Y ∩ A j) : ℝ))
            = pairDensity R (X ∩ A i) (Y ∩ A j)
              * (((X ∩ A i).card : ℝ) * ((Y ∩ A j).card : ℝ))
        exact pairCount_eq_pairDensity_mul
      rw [hcount]
      exact mul_le_mul_of_nonneg_right (by linarith) hxynn
  have hkey_lo : ∀ i j : Fin s,
      (d - 2 * α) * (xi i * yj j)
        - ((if i = j then xi i * yj j else 0)
          + ((if xi i < α * m then xi i * yj j else 0)
            + (if yj j < α * m then xi i * yj j else 0))) ≤ cij i j := by
    intro i j
    have hcnn : (0 : ℝ) ≤ cij i j := Nat.cast_nonneg _
    have hxynn : 0 ≤ xi i * yj j := mul_nonneg (hxi_nn i) (hyj_nn j)
    have hd2 : (d - 2 * α) * (xi i * yj j) ≤ xi i * yj j :=
      mul_le_of_le_one_left hxynn (by linarith)
    by_cases hij : i = j
    · simp only [if_pos hij]
      have h1 : (0 : ℝ) ≤ if xi i < α * m then xi i * yj j else 0 := by positivity
      have h2 : (0 : ℝ) ≤ if yj j < α * m then xi i * yj j else 0 := by positivity
      linarith
    by_cases hx : xi i < α * m
    · simp only [if_neg hij, if_pos hx]
      have h2 : (0 : ℝ) ≤ if yj j < α * m then xi i * yj j else 0 := by positivity
      linarith
    by_cases hy : yj j < α * m
    · simp only [if_neg hij, if_neg hx, if_pos hy]
      linarith
    · simp only [if_neg hij, if_neg hx, if_neg hy, add_zero]
      have h2α := (abs_le.mp (hgood i j hij (le_of_not_gt hx) (le_of_not_gt hy))).1
      have hcount : cij i j
          = pairDensity R (X ∩ A i) (Y ∩ A j) * (xi i * yj j) := by
        show ((pairCount R (X ∩ A i) (Y ∩ A j) : ℝ))
            = pairDensity R (X ∩ A i) (Y ∩ A j)
              * (((X ∩ A i).card : ℝ) * ((Y ∩ A j).card : ℝ))
        exact pairCount_eq_pairDensity_mul
      rw [hcount]
      have := mul_le_mul_of_nonneg_right (show d - 2 * α
          ≤ pairDensity R (X ∩ A i) (Y ∩ A j) by linarith) hxynn
      linarith
  -- The exact decomposition, cast to `ℝ`.
  have hsum : (pairCount R X Y : ℝ) = ∑ i, ∑ j, cij i j := by
    rw [pairCount_eq_sum_inter_fin R A hdisj hX hY]
    push_cast
    rfl
  -- The three structural sums.
  have hprod_sum : ∑ i, ∑ j, xi i * yj j = (X.card : ℝ) * (Y.card : ℝ) := by
    rw [hXC, hYC, Finset.sum_mul_sum]
  have hmain_sum : ∑ i, ∑ j, (d + 2 * α) * (xi i * yj j)
      = (d + 2 * α) * ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [← hprod_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hmain_sum' : ∑ i, ∑ j, (d - 2 * α) * (xi i * yj j)
      = (d - 2 * α) * ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [← hprod_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hdiag_sum : ∑ i, ∑ j, (if i = j then xi i * yj j else 0)
      = ∑ i, xi i * yj i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.sum_ite_eq]
  have hsx_sum : ∑ i, ∑ j, (if xi i < α * m then xi i * yj j else 0)
      = (∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : xi i < α * m
    · simp only [if_pos hc]
      rw [← Finset.mul_sum, ← hYC]
    · simp only [if_neg hc, Finset.sum_const_zero, zero_mul]
  have hsy_sum : ∑ i, ∑ j, (if yj j < α * m then xi i * yj j else 0)
      = (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0) := by
    rw [hXC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : yj j < α * m
    · simp only [if_pos hc]
    · simp only [if_neg hc, mul_zero]
  -- Bounds on the structural sums.
  have hS1 : ∑ i, xi i * yj i ≤ (m : ℝ) * (Y.card : ℝ) := by
    calc ∑ i, xi i * yj i
        ≤ ∑ i, (m : ℝ) * yj i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hxi_le i) (hyj_nn i)
      _ = (m : ℝ) * ∑ i, yj i := (Finset.mul_sum _ _ _).symm
      _ = (m : ℝ) * (Y.card : ℝ) := by rw [← hYC]
  have hS2 : (∑ i, if xi i < α * m then xi i else 0) ≤ α * ((s : ℝ) * m) := by
    calc (∑ i, if xi i < α * m then xi i else 0)
        ≤ ∑ _i : Fin s, α * (m : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hc : xi i < α * m
          · simp only [if_pos hc]
            linarith
          · simp only [if_neg hc]
            positivity
      _ = α * ((s : ℝ) * m) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hS3 : (∑ j, if yj j < α * m then yj j else 0) ≤ α * ((s : ℝ) * m) := by
    calc (∑ j, if yj j < α * m then yj j else 0)
        ≤ ∑ _j : Fin s, α * (m : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hc : yj j < α * m
          · simp only [if_pos hc]
            linarith
          · simp only [if_neg hc]
            positivity
      _ = α * ((s : ℝ) * m) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Conversion of the structural bounds into `|X||Y|` units.
  have hd1' : (m : ℝ) * (Y.card : ℝ)
      ≤ 1 / ((s : ℝ) * ε) * ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hsR hε)]
    calc (m : ℝ) * (Y.card : ℝ) * ((s : ℝ) * ε)
        = (ε * ((s : ℝ) * m)) * (Y.card : ℝ) := by ring
      _ ≤ (X.card : ℝ) * (Y.card : ℝ) :=
          mul_le_mul_of_nonneg_right hXlb (Nat.cast_nonneg _)
      _ = 1 * ((X.card : ℝ) * (Y.card : ℝ)) := (one_mul _).symm
  have hd2' : α * ((s : ℝ) * m) * (Y.card : ℝ)
      ≤ α / ε * ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    calc α * ((s : ℝ) * m) * (Y.card : ℝ) * ε
        = α * ((ε * ((s : ℝ) * m)) * (Y.card : ℝ)) := by ring
      _ ≤ α * ((X.card : ℝ) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hXlb (Nat.cast_nonneg _)) hα.le
  have hd3' : (X.card : ℝ) * (α * ((s : ℝ) * m))
      ≤ α / ε * ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    calc (X.card : ℝ) * (α * ((s : ℝ) * m)) * ε
        = α * ((ε * ((s : ℝ) * m)) * (X.card : ℝ)) := by ring
      _ ≤ α * ((Y.card : ℝ) * (X.card : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hYlb (Nat.cast_nonneg _)) hα.le
      _ = α * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
  -- The two count bounds.
  have hup : (pairCount R X Y : ℝ)
      ≤ (d + 2 * α + (2 * α / ε + 1 / ((s : ℝ) * ε)))
        * ((X.card : ℝ) * (Y.card : ℝ)) := by
    have h1 : (pairCount R X Y : ℝ)
        ≤ (d + 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          + ((∑ i, xi i * yj i)
            + ((∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
              + (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0))) := by
      rw [hsum, ← hmain_sum, ← hdiag_sum, ← hsx_sum, ← hsy_sum]
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey_up i j
    have h2 : (∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
        ≤ α * ((s : ℝ) * m) * (Y.card : ℝ) :=
      mul_le_mul_of_nonneg_right hS2 (Nat.cast_nonneg _)
    have h3 : (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0)
        ≤ (X.card : ℝ) * (α * ((s : ℝ) * m)) :=
      mul_le_mul_of_nonneg_left hS3 (Nat.cast_nonneg _)
    have e1 := le_trans hS1 hd1'
    have e2 := le_trans h2 hd2'
    have e3 := le_trans h3 hd3'
    calc (pairCount R X Y : ℝ)
        ≤ (d + 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          + ((∑ i, xi i * yj i)
            + ((∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
              + (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0))) := h1
      _ ≤ (d + 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          + (1 / ((s : ℝ) * ε) * ((X.card : ℝ) * (Y.card : ℝ))
            + (α / ε * ((X.card : ℝ) * (Y.card : ℝ))
              + α / ε * ((X.card : ℝ) * (Y.card : ℝ)))) := by linarith
      _ = (d + 2 * α + (2 * α / ε + 1 / ((s : ℝ) * ε)))
          * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
  have hlo : (d - 2 * α - (2 * α / ε + 1 / ((s : ℝ) * ε)))
        * ((X.card : ℝ) * (Y.card : ℝ))
      ≤ (pairCount R X Y : ℝ) := by
    have h1 : (d - 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          - ((∑ i, xi i * yj i)
            + ((∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
              + (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0)))
        ≤ (pairCount R X Y : ℝ) := by
      rw [hsum, ← hmain_sum', ← hdiag_sum, ← hsx_sum, ← hsy_sum]
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey_lo i j
    have h2 : (∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
        ≤ α * ((s : ℝ) * m) * (Y.card : ℝ) :=
      mul_le_mul_of_nonneg_right hS2 (Nat.cast_nonneg _)
    have h3 : (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0)
        ≤ (X.card : ℝ) * (α * ((s : ℝ) * m)) :=
      mul_le_mul_of_nonneg_left hS3 (Nat.cast_nonneg _)
    have e1 := le_trans hS1 hd1'
    have e2 := le_trans h2 hd2'
    have e3 := le_trans h3 hd3'
    calc (d - 2 * α - (2 * α / ε + 1 / ((s : ℝ) * ε)))
          * ((X.card : ℝ) * (Y.card : ℝ))
        = (d - 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          - (1 / ((s : ℝ) * ε) * ((X.card : ℝ) * (Y.card : ℝ))
            + (α / ε * ((X.card : ℝ) * (Y.card : ℝ))
              + α / ε * ((X.card : ℝ) * (Y.card : ℝ)))) := by ring
      _ ≤ (d - 2 * α) * ((X.card : ℝ) * (Y.card : ℝ))
          - ((∑ i, xi i * yj i)
            + ((∑ i, if xi i < α * m then xi i else 0) * (Y.card : ℝ)
              + (X.card : ℝ) * (∑ j, if yj j < α * m then yj j else 0))) := by
          linarith
      _ ≤ (pairCount R X Y : ℝ) := h1
  -- Divide.
  have hXY : 0 < (X.card : ℝ) * (Y.card : ℝ) := mul_pos hXpos hYpos
  rw [pairDensity_eq_count_div, abs_le]
  constructor
  · have h1 : d - (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε))
        ≤ (pairCount R X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ)) := by
      rw [le_div_iff₀ hXY]
      calc (d - (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)))
            * ((X.card : ℝ) * (Y.card : ℝ))
          = (d - 2 * α - (2 * α / ε + 1 / ((s : ℝ) * ε)))
            * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
        _ ≤ (pairCount R X Y : ℝ) := hlo
    linarith
  · have h1 : (pairCount R X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))
        ≤ d + (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)) := by
      rw [div_le_iff₀ hXY]
      calc (pairCount R X Y : ℝ)
          ≤ (d + 2 * α + (2 * α / ε + 1 / ((s : ℝ) * ε)))
            * ((X.card : ℝ) * (Y.card : ℝ)) := hup
        _ = (d + (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)))
            * ((X.card : ℝ) * (Y.card : ℝ)) := by ring
    linarith

/-- **The union against the class center on itself**: `|density(U,U) − d| ≤ α + 1/s`
— `α` from the class width on off-diagonal blocks, `1/s` from the diagonal blocks. -/
theorem pairDensity_union_self_close_center (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hα : 0 < α) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hclose : ∀ i j : Fin s, i ≠ j → |pairDensity R (A i) (A j) - d| ≤ α)
    (hU : U = Finset.univ.biUnion A) :
    |pairDensity R U U - d| ≤ α + 1 / (s : ℝ) := by
  classical
  subst hU
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hUA : ∀ i, Finset.univ.biUnion A ∩ A i = A i := fun i =>
    Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem A (Finset.mem_univ i))
  have hdecomp : pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)
      = ∑ i : Fin s, ∑ j : Fin s, pairCount R (A i) (A j) := by
    rw [pairCount_eq_sum_inter_fin R A hdisj subset_rfl subset_rfl]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hUA i, hUA j]
  have hkey_up : ∀ i j : Fin s, ((pairCount R (A i) (A j)) : ℝ)
      ≤ (d + α) * ((m : ℝ) * m) + (if i = j then (m : ℝ) * m else 0) := by
    intro i j
    have hle : ((pairCount R (A i) (A j)) : ℝ) ≤ (m : ℝ) * m := by
      have h := pairCount_le_mul R (A i) (A j)
      rw [hcard i, hcard j] at h
      exact_mod_cast h
    by_cases hij : i = j
    · simp only [if_pos hij]
      have h0 : 0 ≤ (d + α) * ((m : ℝ) * m) :=
        mul_nonneg (by linarith) (by positivity)
      linarith
    · simp only [if_neg hij, add_zero]
      have h1 := (abs_le.mp (hclose i j hij)).2
      have hcount : ((pairCount R (A i) (A j)) : ℝ)
          = pairDensity R (A i) (A j) * ((m : ℝ) * m) := by
        have h := pairCount_eq_pairDensity_mul (R := R) (A := A i) (B := A j)
        rw [hcard i, hcard j] at h
        exact h
      rw [hcount]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hkey_lo : ∀ i j : Fin s,
      (d - α) * ((m : ℝ) * m) - (if i = j then (m : ℝ) * m else 0)
        ≤ ((pairCount R (A i) (A j)) : ℝ) := by
    intro i j
    have hnn : (0 : ℝ) ≤ ((pairCount R (A i) (A j)) : ℝ) := Nat.cast_nonneg _
    by_cases hij : i = j
    · simp only [if_pos hij]
      have h0 : (d - α) * ((m : ℝ) * m) ≤ (m : ℝ) * m :=
        mul_le_of_le_one_left (by positivity) (by linarith)
      linarith
    · simp only [if_neg hij, sub_zero]
      have h1 := (abs_le.mp (hclose i j hij)).1
      have hcount : ((pairCount R (A i) (A j)) : ℝ)
          = pairDensity R (A i) (A j) * ((m : ℝ) * m) := by
        have h := pairCount_eq_pairDensity_mul (R := R) (A := A i) (B := A j)
        rw [hcard i, hcard j] at h
        exact h
      rw [hcount]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdiag_const : ∑ i : Fin s, ∑ j : Fin s, (if i = j then (m : ℝ) * m else 0)
      = (s : ℝ) * ((m : ℝ) * m) := by
    have h1 : ∀ i : Fin s, ∑ j : Fin s, (if i = j then (m : ℝ) * m else 0)
        = (m : ℝ) * m := fun i => by simp [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hconst_up : ∑ i : Fin s, ∑ j : Fin s,
        ((d + α) * ((m : ℝ) * m) + (if i = j then (m : ℝ) * m else 0))
      = (d + α) * (((s : ℝ) * m) * ((s : ℝ) * m)) + (s : ℝ) * ((m : ℝ) * m) := by
    simp only [Finset.sum_add_distrib]
    rw [hdiag_const]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hconst_lo : ∑ i : Fin s, ∑ j : Fin s,
        ((d - α) * ((m : ℝ) * m) - (if i = j then (m : ℝ) * m else 0))
      = (d - α) * (((s : ℝ) * m) * ((s : ℝ) * m)) - (s : ℝ) * ((m : ℝ) * m) := by
    simp only [Finset.sum_sub_distrib]
    rw [hdiag_const]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum : ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
      = ∑ i : Fin s, ∑ j : Fin s, ((pairCount R (A i) (A j)) : ℝ) := by
    rw [hdecomp]
    push_cast
    rfl
  have hup : ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
      ≤ (d + α + 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m)) := by
    calc ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
        = ∑ i : Fin s, ∑ j : Fin s, ((pairCount R (A i) (A j)) : ℝ) := hsum
      _ ≤ ∑ i : Fin s, ∑ j : Fin s,
            ((d + α) * ((m : ℝ) * m) + (if i = j then (m : ℝ) * m else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey_up i j
      _ = (d + α) * (((s : ℝ) * m) * ((s : ℝ) * m)) + (s : ℝ) * ((m : ℝ) * m) :=
          hconst_up
      _ = (d + α + 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m)) := by
          field_simp
  have hlo : (d - α - 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m))
      ≤ ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ) := by
    calc (d - α - 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m))
        = (d - α) * (((s : ℝ) * m) * ((s : ℝ) * m)) - (s : ℝ) * ((m : ℝ) * m) := by
          field_simp
      _ = ∑ i : Fin s, ∑ j : Fin s,
            ((d - α) * ((m : ℝ) * m) - (if i = j then (m : ℝ) * m else 0)) :=
          hconst_lo.symm
      _ ≤ ∑ i : Fin s, ∑ j : Fin s, ((pairCount R (A i) (A j)) : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hkey_lo i j
      _ = ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ) :=
          hsum.symm
  have hUc : (((Finset.univ.biUnion A).card) : ℝ) = (s : ℝ) * m := by
    exact_mod_cast card_biUnion_const hdisj hcard
  have hUU : (0 : ℝ) < ((s : ℝ) * m) * ((s : ℝ) * m) := by positivity
  rw [pairDensity_eq_count_div, hUc, abs_le]
  constructor
  · have h1 : d - (α + 1 / (s : ℝ))
        ≤ ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
          / (((s : ℝ) * m) * ((s : ℝ) * m)) := by
      rw [le_div_iff₀ hUU]
      calc (d - (α + 1 / (s : ℝ))) * (((s : ℝ) * m) * ((s : ℝ) * m))
          = (d - α - 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m)) := by ring
        _ ≤ _ := hlo
    linarith
  · have h1 : ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
          / (((s : ℝ) * m) * ((s : ℝ) * m)) ≤ d + (α + 1 / (s : ℝ)) := by
      rw [div_le_iff₀ hUU]
      calc ((pairCount R (Finset.univ.biUnion A) (Finset.univ.biUnion A)) : ℝ)
          ≤ (d + α + 1 / (s : ℝ)) * (((s : ℝ) * m) * ((s : ℝ) * m)) := hup
        _ = (d + (α + 1 / (s : ℝ))) * (((s : ℝ) * m) * ((s : ℝ) * m)) := by ring
    linarith

/-- **The generic union estimate**, with the exact four-term error. -/
theorem pairDensity_union_sub_self_le (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hα : 0 < α) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) α)
    (hclose : ∀ i j : Fin s, i ≠ j → |pairDensity R (A i) (A j) - d| ≤ α)
    (hU : U = Finset.univ.biUnion A) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hε : 0 < ε) (hXl : ε * (U.card : ℝ) ≤ (X.card : ℝ))
    (hYl : ε * (U.card : ℝ) ≤ (Y.card : ℝ)) :
    |pairDensity R X Y - pairDensity R U U|
      ≤ 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by
  have h1 := pairDensity_union_close_center hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX hY hε hXl hYl
  have h2 := pairDensity_union_self_close_center hm hs hdisj hcard hα hd0 hd1
    hclose hU
  calc |pairDensity R X Y - pairDensity R U U|
      ≤ |pairDensity R X Y - d| + |d - pairDensity R U U| := abs_sub_le _ _ _
    _ ≤ (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)) + (α + 1 / (s : ℝ)) := by
        refine add_le_add h1 ?_
        rw [abs_sub_comm]
        exact h2
    _ = 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by ring

/-- **The self-uniformity corollary at the frozen constants**: with `α = (ε/3)²` and
`2 ≤ α·s`, the union is `ε`-uniform with itself — the displayed error is at most
`2ε/3`, leaving slack for later slicing and palette bookkeeping. -/
theorem isUniformPair_self_union (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) ((ε / 3) ^ 2))
    (hclose : ∀ i j : Fin s, i ≠ j →
      |pairDensity R (A i) (A j) - d| ≤ (ε / 3) ^ 2)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hU : U = Finset.univ.biUnion A)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsα : 2 ≤ (ε / 3) ^ 2 * (s : ℝ)) :
    IsUniformPair R U U ε := by
  intro X' hX' Y' hY' hXc hYc
  have hα : (0 : ℝ) < (ε / 3) ^ 2 := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htri := pairDensity_union_sub_self_le hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX' hY' hε hXc hYc
  refine le_trans htri ?_
  have e1 : 2 * (ε / 3) ^ 2 / ε = 2 * ε / 9 := by
    field_simp
    ring
  have e2 : 1 / ((s : ℝ) * ε) ≤ ε / 18 := by
    rw [div_le_iff₀ (mul_pos hsR hε)]
    nlinarith [hsα]
  have e3 : 1 / (s : ℝ) ≤ ε ^ 2 / 18 := by
    rw [div_le_iff₀ hsR]
    nlinarith [hsα]
  have e4 : ε ^ 2 ≤ ε := by nlinarith
  linarith [e1, e2, e3, e4]

end Union

/-! ### Tests and adversarial examples -/

section Tests

-- G-U1a: the two ordered singleton pieces of the equality relation are perfectly
-- uniform at ANY nonnegative tolerance — every subrectangle has density zero.
example (α : ℝ) (hα : 0 ≤ α) :
    IsUniformPair (fun a b : Fin 2 => a = b) {0} {1} α := by
  have hzero : ∀ X' Y' : Finset (Fin 2), X' ⊆ {0} → Y' ⊆ {1} →
      pairDensity (fun a b : Fin 2 => a = b) X' Y' = 0 := by
    intro X' Y' hX' hY'
    have hcount : pairCount (fun a b : Fin 2 => a = b) X' Y' = 0 := by
      rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq
      rw [Finset.mem_product] at hq
      have hx := Finset.mem_singleton.mp (hX' hq.1)
      have hy := Finset.mem_singleton.mp (hY' hq.2)
      rw [hx, hy]
      decide
    rw [pairDensity_eq_count_div, hcount]
    norm_num
  intro X' hX' Y' hY' _ _
  rw [hzero X' Y' hX' hY', hzero {0} {1} subset_rfl subset_rfl]
  simpa using hα

-- G-U1b: yet their union is NOT `1/4`-uniform with itself (witness `X' = Y' = {0}`:
-- density `1` against `1/2`) — with `s` below the `2/α` threshold, the `1/(s·ε)`
-- diagonal term is REAL and the union lemma's size demand cannot be waived.
example : ¬ IsUniformPair (fun a b : Fin 2 => a = b)
    (Finset.univ : Finset (Fin 2)) Finset.univ (1 / 4 : ℝ) := by
  intro h
  have h3 := h (X' := {0}) (by simp) (Y' := {0}) (by simp)
    (by norm_num [Finset.card_univ]) (by norm_num [Finset.card_univ])
  rw [pairDensity_eq_count_div, pairDensity_eq_count_div] at h3
  norm_num [show pairCount (fun a b : Fin 2 => a = b) {0} {0} = 1 from by decide,
    show pairCount (fun a b : Fin 2 => a = b)
      (Finset.univ : Finset (Fin 2)) Finset.univ = 2 from by decide,
    Finset.card_univ] at h3

-- G-U2: WITHOUT equal cardinality the `1/s` self-term is FALSE. Pieces `{0}` and
-- `{1,2,3}` with `R x y := x ≠ 0 ∧ y ≠ 0`: all ordered piece pairs have density `0`
-- (with perfect uniformity), yet `density(U,U) = 9/16` exceeds `α + 1/2` for
-- `α = 1/32` — a comparability factor is unavoidable if pieces are not trimmed.
example : ¬ (|pairDensity (fun a b : Fin 4 => a ≠ 0 ∧ b ≠ 0)
      Finset.univ Finset.univ - 0| ≤ 1 / 32 + 1 / 2) := by
  rw [pairDensity_eq_count_div]
  norm_num [show pairCount (fun a b : Fin 4 => a ≠ 0 ∧ b ≠ 0)
      Finset.univ Finset.univ = 9 from by decide, Finset.card_univ]

-- G-U3: directed densities are NOT reversal-invariant — the extraction color of the
-- density-bucket unit must record BOTH orientations of each piece pair.
example : pairCount (fun a b : Fin 2 => a = 0 ∧ b = 1) {0} {1} = 1 := by decide

example : pairCount (fun a b : Fin 2 => a = 0 ∧ b = 1) {1} {0} = 0 := by decide

-- G-U4: the largeness cutoff is INCLUSIVE — a test set of size exactly `ε·|A|`
-- enters the regularity-controlled case (matching `IsUniformPair`'s inclusive
-- largeness); only strictly smaller test sets are exceptional.
example {V : Type*} [DecidableEq V] {R : V → V → Prop} [DecidableRel R]
    {A B X' Y' : Finset V} {ε : ℝ} (h : IsUniformPair R A B ε)
    (hX' : X' ⊆ A) (hY' : Y' ⊆ B)
    (hx : (X'.card : ℝ) = ε * A.card) (hy : (Y'.card : ℝ) = ε * B.card) :
    |pairDensity R X' Y' - pairDensity R A B| ≤ ε :=
  h hX' hY' (le_of_eq hx.symm) (le_of_eq hy.symm)

end Tests

end RegularityLemmata
