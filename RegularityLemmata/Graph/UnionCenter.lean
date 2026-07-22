/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.UniformSlicing

/-!
# Route (b) step 1 substrate: indexed decompositions and center estimates

The substrate of the equal-cardinality union theorem (`Graph/UniformUnion.lean`),
split out per the repository's file-size convention: the indexed exact
decompositions over a disjoint family, and the two center estimates — test sets
against the common off-diagonal density `d` (`pairDensity_union_close_center`,
error `2α + 2α/ε + 1/(s·ε)`) and the union against `d` on itself
(`pairDensity_union_self_close_center`, error `α + 1/s`). The union summit and its
adversarial gates consume these.

Provenance: this adapts the Lemma 3.6 self-regular-subset construction of
D. Conlon and J. Fox, *Graph removal lemmas* (arXiv:1211.3487, §3.2) — equal-sized
pairwise-regular pieces, Ramsey extraction with close densities, self-regular
union — to directed finite binary palettes; the full cylinder lemma and their
quantitative bounds are NOT formalized (see `PROVENANCE.md`).
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

end Union

end RegularityLemmata
