/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import RegularityLemmata.Partition.FiniteProbabilisticMethod

/-!
# Equal-block partitions encoded through permutations

Step 1 of the equal-block sampling route: encode equal-block partitions through permutations.
The sample space is the equivalence type `Fin n ≃ α` (of cardinality `n!`); each sample `e`
induces the consecutive-window equal-block decomposition whose `j`-th block is the image under
`e` of the position window `[j*s, (j+1)*s)`.

Everything here is exact finite counting — no probability, expectation, or distributions appear.
The payload is the fiber-constancy theorem `card_filter_sampleBlock_eq`: for every `s`-subset
`S`, exactly `s! * (n-s)!` equivalences send a fixed in-range window onto `S`.  The counting
transfer `card_filter_sampleBlock_mem` converts subset-family counts into permutation-space
counts, and the bridge `exists_equiv_avoids_all` feeds them into
`RegularityLemmata.exists_avoids_all_of_sum_card_lt`.

Later steps of the route (without-replacement concentration; trace-family bounds) instantiate
the family `fam` of the bridge with deviation events.
-/

open Finset

namespace RegularityLemmata

/-! ### Position windows in `Fin n` -/

/-- The `j`-th consecutive position window of width `s`: the positions `x : Fin n` with
`j*s ≤ x.val < (j+1)*s`.  Out-of-range windows are (partially or totally) truncated. -/
def blockWindow (n s j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x ↦ j * s ≤ x.val ∧ x.val < (j + 1) * s

/-- Membership in a position window is the defining pair of value inequalities. -/
theorem mem_blockWindow {n s j : ℕ} {x : Fin n} :
    x ∈ blockWindow n s j ↔ j * s ≤ x.val ∧ x.val < (j + 1) * s := by
  simp [blockWindow]

/-- An in-range window has exactly `s` positions. -/
theorem card_blockWindow {n s j : ℕ} (hj : (j + 1) * s ≤ n) :
    (blockWindow n s j).card = s := by
  have hmap : (blockWindow n s j).map Fin.valEmbedding = Finset.Ico (j * s) ((j + 1) * s) := by
    ext m
    simp only [Finset.mem_map, mem_blockWindow, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, lt_of_lt_of_le h2 hj⟩, ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map (f := Fin.valEmbedding), hmap, Nat.card_Ico, add_one_mul,
    Nat.add_sub_cancel_left]

/-- Distinct windows are disjoint, with no range hypotheses: the underlying value-intervals
`[j*s, (j+1)*s)` and `[k*s, (k+1)*s)` are disjoint whenever `j ≠ k`. -/
theorem blockWindow_disjoint {n s j k : ℕ} (hjk : j ≠ k) :
    Disjoint (blockWindow n s j) (blockWindow n s k) := by
  rw [Finset.disjoint_left]
  intro x hxj hxk
  rw [mem_blockWindow] at hxj hxk
  rcases Nat.lt_or_ge j k with h | h
  · have hle : (j + 1) * s ≤ k * s := Nat.mul_le_mul_right s h
    exact absurd ((hxj.2.trans_le hle).trans_le hxk.1) (lt_irrefl _)
  · have h' : k < j := lt_of_le_of_ne h (Ne.symm hjk)
    have hle : (k + 1) * s ≤ j * s := Nat.mul_le_mul_right s h'
    exact absurd ((hxk.2.trans_le hle).trans_le hxj.1) (lt_irrefl _)

/-- When `n = m * s`, the `m` windows of width `s` tile all positions. -/
theorem biUnion_blockWindow {n s m : ℕ} (h : n = m * s) :
    (Finset.range m).biUnion (blockWindow n s) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x ↦ ?_
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · exact absurd x.isLt (by simp [h, hs])
    · exact hs
  refine Finset.mem_biUnion.mpr
    ⟨x.val / s, Finset.mem_range.mpr ?_, mem_blockWindow.mpr ⟨?_, ?_⟩⟩
  · exact (Nat.div_lt_iff_lt_mul hs).mpr (h ▸ x.isLt)
  · exact Nat.div_mul_le_self _ _
  · have hmod : x.val % s < s := Nat.mod_lt _ hs
    have hdiv : x.val / s * s + x.val % s = x.val := Nat.div_add_mod' _ _
    calc x.val = x.val / s * s + x.val % s := hdiv.symm
      _ < x.val / s * s + s := Nat.add_lt_add_left hmod _
      _ = (x.val / s + 1) * s := (add_one_mul _ _).symm

/-! ### Sample blocks: images of windows under an equivalence -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `j`-th block of the equal-block decomposition sampled by `e : Fin n ≃ α`: the image of
the `j`-th position window under `e`. -/
def sampleBlock {n : ℕ} (e : Fin n ≃ α) (s j : ℕ) : Finset α :=
  (blockWindow n s j).image e

omit [Fintype α] in
/-- An in-range sample block has exactly `s` elements. -/
theorem card_sampleBlock {n s j : ℕ} (e : Fin n ≃ α) (hj : (j + 1) * s ≤ n) :
    (sampleBlock e s j).card = s :=
  (Finset.card_image_of_injective _ e.injective).trans (card_blockWindow hj)

omit [Fintype α] in
/-- Distinct sample blocks are disjoint, with no range hypotheses. -/
theorem sampleBlock_disjoint {n s j k : ℕ} (e : Fin n ≃ α) (hjk : j ≠ k) :
    Disjoint (sampleBlock e s j) (sampleBlock e s k) :=
  (Finset.disjoint_image e.injective).mpr (blockWindow_disjoint hjk)

/-- When `n = m * s`, the `m` sample blocks tile the carrier. -/
theorem biUnion_sampleBlock {n s m : ℕ} (e : Fin n ≃ α) (h : n = m * s) :
    (Finset.range m).biUnion (fun j ↦ sampleBlock e s j) = Finset.univ := by
  unfold sampleBlock
  rw [← Finset.biUnion_image, biUnion_blockWindow h, Finset.image_univ_equiv]

/-! ### Splitting an equivalence along a window

An equivalence that carries a predicate `p` on the source exactly onto a predicate `q` on the
target decomposes into an equivalence of the `p`/`q` subtypes and an equivalence of their
complements — and conversely.  This is the exact structure behind fiber constancy. -/

/-- Split an equivalence respecting a predicate pair into its subtype restriction and its
complement restriction.  The inverse glues the two pieces along `Equiv.sumCompl`. -/
def predicateSplitEquiv {β γ : Type*} (p : β → Prop) (q : γ → Prop)
    [DecidablePred p] [DecidablePred q] :
    {e : β ≃ γ // ∀ x, p x ↔ q (e x)} ≃
      ({x // p x} ≃ {y // q y}) × ({x // ¬p x} ≃ {y // ¬q y}) where
  toFun e := ⟨e.1.subtypeEquiv e.2, e.1.subtypeEquiv fun x ↦ not_congr (e.2 x)⟩
  invFun fg :=
    ⟨(Equiv.sumCompl p).symm.trans ((fg.1.sumCongr fg.2).trans (Equiv.sumCompl q)), by
      intro x
      by_cases hx : p x
      · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx,
          Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
        exact iff_of_true hx (fg.1 ⟨x, hx⟩).2
      · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx,
          Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
        exact iff_of_false hx (fg.2 ⟨x, hx⟩).2⟩
  left_inv e := by
    refine Subtype.ext (Equiv.ext fun x ↦ ?_)
    by_cases hx : p x
    · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl, Equiv.subtypeEquiv_apply]
    · simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr, Equiv.subtypeEquiv_apply]
  right_inv fg := by
    refine Prod.ext (Equiv.ext fun x ↦ Subtype.ext ?_) (Equiv.ext fun x ↦ Subtype.ext ?_)
    · simp only [Equiv.subtypeEquiv_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_pos x.2, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.sumCompl_apply_inl]
    · simp only [Equiv.subtypeEquiv_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg x.2, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.sumCompl_apply_inr]

/-- An equivalence maps a finite set exactly onto another iff it carries the membership
predicates onto each other pointwise. -/
theorem image_eq_iff_forall_mem {β γ : Type*} [DecidableEq γ] (e : β ≃ γ) (W : Finset β)
    (S : Finset γ) : W.image e = S ↔ ∀ x, x ∈ W ↔ e x ∈ S := by
  constructor
  · rintro rfl x
    constructor
    · exact fun hx ↦ Finset.mem_image_of_mem _ hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      exact e.injective hyx ▸ hy
  · intro h
    ext a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).mp hx
    · intro ha
      exact ⟨e.symm a, (h _).mpr (by simpa using ha), e.apply_symm_apply a⟩

/-! ### Fiber constancy -/

/-- **Fiber constancy.**  For an in-range window and any `s`-subset `S` of the carrier, exactly
`s! * (n-s)!` equivalences `e : Fin n ≃ α` sample `S` as their `j`-th block.  This is the exact
count that makes the uniform equal-block decomposition exchangeable over `s`-subsets. -/
theorem card_filter_sampleBlock_eq {n s j : ℕ} (hn : Fintype.card α = n)
    (hj : (j + 1) * s ≤ n) (S : Finset α) (hS : S.card = s) :
    (Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s j = S).card
      = s.factorial * (n - s).factorial := by
  classical
  have hsplit : {e : Fin n ≃ α // sampleBlock e s j = S} ≃
      ({x // x ∈ blockWindow n s j} ≃ {a // a ∈ S}) ×
        ({x // ¬x ∈ blockWindow n s j} ≃ {a // ¬a ∈ S}) :=
    (Equiv.subtypeEquivRight fun e ↦ image_eq_iff_forall_mem e (blockWindow n s j) S).trans
      (predicateSplitEquiv _ _)
  have c1 : Fintype.card {x // x ∈ blockWindow n s j} = s := by
    simpa using card_blockWindow hj
  have c2 : Fintype.card {a // a ∈ S} = s := by simpa using hS
  have d1 : Fintype.card {x // ¬x ∈ blockWindow n s j} = n - s := by
    rw [Fintype.card_subtype_compl, c1, Fintype.card_fin]
  have d2 : Fintype.card {a // ¬a ∈ S} = n - s := by
    rw [Fintype.card_subtype_compl, c2, hn]
  rw [← Fintype.card_subtype, Fintype.card_congr hsplit, Fintype.card_prod,
    Fintype.card_equiv (Fintype.equivOfCardEq (c1.trans c2.symm)),
    Fintype.card_equiv (Fintype.equivOfCardEq (d1.trans d2.symm)), c1, d1]

/-! ### Counting transfer -/

/-- **Counting transfer.**  For a family `𝒮` of `s`-subsets and an in-range window `j`, the
number of equivalences whose `j`-th sample block lands in `𝒮` is exactly `𝒮.card` times the
constant fiber size `s! * (n-s)!`.  This converts subset-family counts into permutation-space
counts. -/
theorem card_filter_sampleBlock_mem {n s j : ℕ} (hn : Fintype.card α = n)
    (hj : (j + 1) * s ≤ n) (𝒮 : Finset (Finset α)) (h𝒮 : ∀ S ∈ 𝒮, S.card = s) :
    (Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s j ∈ 𝒮).card
      = 𝒮.card * (s.factorial * (n - s).factorial) := by
  classical
  have hunion : (Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s j ∈ 𝒮)
      = 𝒮.biUnion fun S ↦
          Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s j = S := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · exact fun h ↦ ⟨sampleBlock e s j, h, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact hS
  rw [hunion, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun S hS ↦ card_filter_sampleBlock_eq hn hj S (h𝒮 S hS),
      Finset.sum_const, smul_eq_mul]
  · intro S hS T hT hST
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e heS heT
    obtain ⟨-, hS'⟩ := Finset.mem_filter.mp heS
    obtain ⟨-, hT'⟩ := Finset.mem_filter.mp heT
    exact hST (hS' ▸ hT')

/-! ### Bridge to the finite union bound -/

/-- **Union-bound bridge.**  Bad events are indexed by `i : I`, each specified by an in-range
block index `blk i` and a family `fam i` of `s`-subsets.  If the total family count is strictly
below `n.choose s`, some equivalence `e : Fin n ≃ α` avoids every bad event: no sampled block
`sampleBlock e s (blk i)` lies in the corresponding family.  Exact counting only: the strict
inequality is multiplied by the positive constant fiber size and compared against `n!`. -/
theorem exists_equiv_avoids_all {n s : ℕ} {I : Type*} [Fintype I]
    (hn : Fintype.card α = n) (hs : s ≤ n) (blk : I → ℕ) (fam : I → Finset (Finset α))
    (hblk : ∀ i, (blk i + 1) * s ≤ n) (hfam : ∀ i, ∀ S ∈ fam i, S.card = s)
    (hsum : ∑ i, (fam i).card < n.choose s) :
    ∃ e : Fin n ≃ α, ∀ i, sampleBlock e s (blk i) ∉ fam i := by
  classical
  have hcardΩ : Fintype.card (Fin n ≃ α) = n.factorial := by
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hn).symm, Fintype.card_fin]
  have hpos : 0 < s.factorial * (n - s).factorial :=
    Nat.mul_pos s.factorial_pos (n - s).factorial_pos
  have key : ∑ i, (Finset.univ.filter
        fun e : Fin n ≃ α ↦ sampleBlock e s (blk i) ∈ fam i).card
      < Fintype.card (Fin n ≃ α) := by
    calc
      ∑ i, (Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s (blk i) ∈ fam i).card
          = ∑ i, (fam i).card * (s.factorial * (n - s).factorial) :=
        Finset.sum_congr rfl fun i _ ↦
          card_filter_sampleBlock_mem hn (hblk i) (fam i) (hfam i)
      _ = (∑ i, (fam i).card) * (s.factorial * (n - s).factorial) := by
        rw [Finset.sum_mul]
      _ < n.choose s * (s.factorial * (n - s).factorial) := by
        exact Nat.mul_lt_mul_of_lt_of_le hsum le_rfl hpos
      _ = n.factorial := by
        rw [← mul_assoc]
        exact Nat.choose_mul_factorial_mul_factorial hs
      _ = Fintype.card (Fin n ≃ α) := hcardΩ.symm
  obtain ⟨e, he⟩ := exists_avoids_all_of_sum_card_lt
    (fun i ↦ Finset.univ.filter fun e : Fin n ≃ α ↦ sampleBlock e s (blk i) ∈ fam i) key
  exact ⟨e, fun i ↦ by simpa using he i⟩

/-! ### Tests and adversarial examples

Exact-count sanity checks: width-zero windows, the last block, exact tiling, and a tiny
concrete fiber count certified by kernel `decide`. -/

-- Width `s = 0`: every window is empty, every sample block is `∅`, the fiber over `∅` is the
-- whole sample space, and the stated count `0! * n!` is exactly `n!`.
example : (blockWindow 3 0 5) = ∅ := by decide

example : (Finset.univ.filter
      fun e : Fin 3 ≃ Fin 3 ↦ sampleBlock e 0 0 = (∅ : Finset (Fin 3))).card
    = Nat.factorial 0 * Nat.factorial 3 :=
  card_filter_sampleBlock_eq (by simp) (by norm_num) ∅ rfl

-- The last block `j = m - 1` of an exact tiling is still in range.
example : (Finset.univ.filter
      fun e : Fin 4 ≃ Fin 4 ↦ sampleBlock e 2 1 = ({2, 3} : Finset (Fin 4))).card
    = Nat.factorial 2 * Nat.factorial 2 :=
  card_filter_sampleBlock_eq (by simp) (by norm_num) _ (by decide)

-- Exact tiling `n = m * s` at the window and sample-block level.
example : (Finset.range 2).biUnion (blockWindow 4 2) = Finset.univ :=
  biUnion_blockWindow rfl

example (e : Fin 4 ≃ Fin 4) :
    (Finset.range 2).biUnion (fun j ↦ sampleBlock e 2 j) = Finset.univ :=
  biUnion_sampleBlock e rfl

-- Tiny concrete fiber count, certified by kernel `decide`: over `Fin 4` with `s = 2`, exactly
-- `2! * 2! = 4` of the `24` equivalences sample `{0, 1}` as block `0`.
example : (Finset.univ.filter
      fun e : Fin 4 ≃ Fin 4 ↦ sampleBlock e 2 0 = ({0, 1} : Finset (Fin 4))).card
    = 4 := by decide

end RegularityLemmata
