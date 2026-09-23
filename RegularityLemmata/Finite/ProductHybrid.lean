/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import RegularityLemmata.Finite.SectionDefect
import RegularityLemmata.Finite.Density

/-!
# The heterogeneous product hybrid and the coordinate-resampling bound

A relation `R` on the box `∏ᵢ A i` of `k` finite carriers `A i : Finset (V i)` over a family of
coordinate types `V : Fin k → Type*` (the tuple type is `∀ i, V i`; a common carrier is the
constant family). Two tuples `x, y` of the box are joined by the
**prefix hybrids** `z_j := (y_0, …, y_{j−1}, x_j, …, x_{k−1})`, `j = 0, …, k`, with `z_0 = x`
and `z_k = y`; consecutive hybrids differ in one coordinate only,
`z_{j+1} = Function.update z_j j (y j)` (`prefixHybrid_succ`).

**Coordinate-resampling disagreement.** `coordDisagreement R A j` counts the pairs `(w, a)`
with `w` in the box and `a ∈ A j` on which `R` changes when coordinate `j` of `w` is resampled
to `a`. The **prefix-swap identity** (`hybridEdgeDisagreement_eq`) says that the number of
ordered pairs `(x, y)` of the box whose `j`-th hybrid edge disagrees is exactly
`coordDisagreement R A j · ∏_{i ≠ j} |A i|`: the map `(x, y) ↦ (z_j, y j)` is onto
`box × A j` with every fiber of size `∏_{i ≠ j} |A i|` (the prefix of `x` and the suffix of `y`
are free, everything else is determined).

**The resampling bound** (`minorityCount_mul_card_le`). A pair with `R x ≠ R y` has a
disagreeing hybrid edge, so the ordered disagreeing pairs, `2·c·(|box| − c)` of them for
`c = tupleCount R A`, are at most the sum over `j` of the edge disagreements. Since the minority
`min (c, |box| − c)` satisfies `min · |box| ≤ 2·c·(|box| − c)`, this gives, in `ℕ` with no
division,

`minorityCount R A · |box| ≤ ∑ j, coordDisagreement R A j · ∏_{i ≠ j} |A i|.`

An empty factor makes every term `0`; for `k = 0` the box is a single point, the minority is
`0`, and the sum is empty. Neither case needs a separate hypothesis. The normalized form
`minorityCount_le_sum_coordDisagreement_div` divides by the factor sizes and is likewise
guard-free (an empty factor makes both sides `0`).
-/

namespace RegularityLemmata

variable {k : ℕ} {V : Fin k → Type*} [∀ i, DecidableEq (V i)]

/-! ### Prefix hybrids -/

/-- The prefix hybrid of `x` and `y` at level `j`: coordinates below `j` from `y`, the rest
from `x`. -/
def prefixHybrid (x y : ∀ i, V i) (j : ℕ) : ∀ i, V i :=
  fun i => if (i : ℕ) < j then y i else x i

omit [∀ i, DecidableEq (V i)] in
@[simp] theorem prefixHybrid_zero (x y : ∀ i, V i) : prefixHybrid x y 0 = x := by
  funext i; simp [prefixHybrid]

omit [∀ i, DecidableEq (V i)] in
theorem prefixHybrid_of_le (x y : ∀ i, V i) {j : ℕ} (h : k ≤ j) : prefixHybrid x y j = y := by
  funext i; simp [prefixHybrid, lt_of_lt_of_le i.2 h]

omit [∀ i, DecidableEq (V i)] in
/-- Consecutive hybrids differ in coordinate `j` only. -/
theorem prefixHybrid_succ (x y : ∀ i, V i) (j : Fin k) :
    prefixHybrid x y (j + 1) = Function.update (prefixHybrid x y j) j (y j) := by
  funext i
  by_cases hij : i = j
  · subst hij; simp [prefixHybrid]
  · rw [Function.update_of_ne hij]
    simp only [prefixHybrid]
    have : ((i : ℕ) < (j : ℕ) + 1) ↔ ((i : ℕ) < (j : ℕ)) := by
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · exact h
        · exact absurd (Fin.ext h) hij
      · exact fun h => Nat.lt_succ_of_lt h
    simp [this]

omit [∀ i, DecidableEq (V i)] in
theorem prefixHybrid_mem {A : ∀ i, Finset (V i)} {x y : ∀ i, V i}
    (hx : x ∈ Fintype.piFinset A) (hy : y ∈ Fintype.piFinset A) (j : ℕ) :
    prefixHybrid x y j ∈ Fintype.piFinset A := by
  rw [Fintype.mem_piFinset] at *
  intro i
  unfold prefixHybrid
  split_ifs
  · exact hy i
  · exact hx i

/-! ### Coordinate-resampling disagreement and the hybrid edges -/

variable (R : (∀ i, V i) → Prop) [DecidablePred R] (A : ∀ i, Finset (V i))

/-- The pairs `(w, a)`, `w` in the box and `a ∈ A j`, on which `R` changes when coordinate `j`
of `w` is resampled to `a`. -/
def coordDisagreement (j : Fin k) : ℕ :=
  ((Fintype.piFinset A ×ˢ A j).filter
    fun q => ¬ (R q.1 ↔ R (Function.update q.1 j q.2))).card

/-- The ordered pairs `(x, y)` of the box whose `j`-th hybrid edge `z_j → z_{j+1}` disagrees. -/
def hybridEdgeDisagreement (j : Fin k) : ℕ :=
  ((Fintype.piFinset A ×ˢ Fintype.piFinset A).filter
    fun p => ¬ (R (prefixHybrid p.1 p.2 j) ↔ R (prefixHybrid p.1 p.2 (j + 1)))).card

/-- The prefix box: coordinates below `j` free in `A`, the rest pinned to `w`. -/
private def prefixBox (w : ∀ i, V i) (j : Fin k) : ∀ i, Finset (V i) :=
  fun i => if (i : ℕ) < j then A i else {w i}

/-- The suffix box: coordinates below `j` pinned to `w`, coordinate `j` pinned to `a`, the rest
free in `A`. -/
private def suffixBox (w : ∀ i, V i) (j : Fin k) (a : V j) : ∀ i, Finset (V i) :=
  Function.update (fun i => if (i : ℕ) < j then {w i} else A i) j {a}

omit [∀ i, DecidableEq (V i)] in
private theorem suffixBox_apply_self (w : ∀ i, V i) (j : Fin k) (a : V j) :
    suffixBox A w j a j = {a} := by
  simp [suffixBox]

omit [∀ i, DecidableEq (V i)] in
private theorem suffixBox_apply_of_ne (w : ∀ i, V i) (j : Fin k) (a : V j) {i : Fin k}
    (hij : i ≠ j) : suffixBox A w j a i = if (i : ℕ) < j then {w i} else A i := by
  simp [suffixBox, Function.update_of_ne hij]

omit [∀ i, DecidableEq (V i)] in
private theorem card_prefixBox_mul_card_suffixBox (w : ∀ i, V i) (j : Fin k) (a : V j) :
    (Fintype.piFinset (prefixBox A w j)).card * (Fintype.piFinset (suffixBox A w j a)).card
      = ∏ i ∈ Finset.univ.erase j, (A i).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset, ← Finset.prod_mul_distrib]
  have h : ∀ i : Fin k, (prefixBox A w j i).card * (suffixBox A w j a i).card
      = if i = j then 1 else (A i).card := by
    intro i
    by_cases hij : i = j
    · subst hij; simp [prefixBox, suffixBox_apply_self]
    · rw [suffixBox_apply_of_ne A w j a hij]
      unfold prefixBox
      by_cases hlt : (i : ℕ) < j
      · simp [hlt, hij]
      · simp [hlt, hij]
  rw [Finset.prod_congr rfl (fun i _ => h i)]
  rw [← Finset.prod_erase (s := Finset.univ) (a := j) (f := fun i => if i = j then 1 else (A i).card)
    (by simp)]
  exact Finset.prod_congr rfl (fun i hi => by simp [Finset.ne_of_mem_erase hi])

/-- The fiber of `(x, y) ↦ (z_j, y j)` over `(w, a)`: the prefix of `x` and the suffix of `y` are
free, everything else is determined. -/
private theorem fiber_eq (w : ∀ i, V i) (j : Fin k) (a : V j) (hw : w ∈ Fintype.piFinset A)
    (ha : a ∈ A j) :
    (Fintype.piFinset A ×ˢ Fintype.piFinset A).filter
        (fun p => (prefixHybrid p.1 p.2 j, p.2 j) = (w, a))
      = Fintype.piFinset (prefixBox A w j) ×ˢ Fintype.piFinset (suffixBox A w j a) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Prod.mk.injEq]
  rw [Fintype.mem_piFinset] at hw
  constructor
  · rintro ⟨⟨hx, hy⟩, hz, hyj⟩
    have hz' : ∀ i : Fin k, prefixHybrid x y j i = w i := fun i => congrFun hz i
    refine ⟨fun i => ?_, fun i => ?_⟩
    · unfold prefixBox
      split_ifs with hlt
      · exact hx i
      · have := hz' i; simp [prefixHybrid, hlt] at this; simp [this]
    · by_cases hij : i = j
      · subst hij; rw [suffixBox_apply_self]; simp [hyj]
      · rw [suffixBox_apply_of_ne A w j a hij]
        split_ifs with hlt
        · have := hz' i; simp [prefixHybrid, hlt] at this; simp [this]
        · exact hy i
  · rintro ⟨hx, hy⟩
    have hx' : ∀ i : Fin k, (i : ℕ) < j → x i ∈ A i := fun i hlt => by
      have := hx i; simpa [prefixBox, hlt] using this
    have hxw : ∀ i : Fin k, ¬ (i : ℕ) < j → x i = w i := fun i hlt => by
      have := hx i; simpa [prefixBox, hlt] using this
    have hyw : ∀ i : Fin k, (i : ℕ) < j → y i = w i := fun i hlt => by
      have hij : i ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      have := hy i; rw [suffixBox_apply_of_ne A w j a hij] at this; simpa [hlt] using this
    have hyj : y j = a := by
      have := hy j; rw [suffixBox_apply_self] at this; simpa using this
    have hy' : ∀ i : Fin k, ¬ (i : ℕ) < j → i ≠ j → y i ∈ A i := fun i hlt hij => by
      have := hy i; rw [suffixBox_apply_of_ne A w j a hij] at this; simpa [hlt] using this
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_, hyj⟩
    · by_cases hlt : (i : ℕ) < j
      · exact hx' i hlt
      · rw [hxw i hlt]; exact hw i
    · by_cases hlt : (i : ℕ) < j
      · rw [hyw i hlt]; exact hw i
      · by_cases hij : i = j
        · subst hij; rw [hyj]; exact ha
        · exact hy' i hlt hij
    · funext i
      unfold prefixHybrid
      split_ifs with hlt
      · exact hyw i hlt
      · exact hxw i hlt

/-- **The prefix-swap identity.** The disagreeing `j`-th hybrid edges are counted exactly by the
coordinate-`j` resampling disagreement times the size of the off-coordinate box. -/
theorem hybridEdgeDisagreement_eq (j : Fin k) :
    hybridEdgeDisagreement R A j
      = coordDisagreement R A j * ∏ i ∈ Finset.univ.erase j, (A i).card := by
  classical
  unfold hybridEdgeDisagreement coordDisagreement
  set S := (Fintype.piFinset A ×ˢ Fintype.piFinset A).filter
    fun p => ¬ (R (prefixHybrid p.1 p.2 j) ↔ R (prefixHybrid p.1 p.2 (j + 1))) with hS
  set T := (Fintype.piFinset A ×ˢ A j).filter
    fun q => ¬ (R q.1 ↔ R (Function.update q.1 j q.2)) with hT
  set φ : (∀ i, V i) × (∀ i, V i) → (∀ i, V i) × V j :=
    fun p => (prefixHybrid p.1 p.2 j, p.2 j) with hφ
  have hmaps : ∀ p ∈ S, φ p ∈ T := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_product] at hp
    rw [hT, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨prefixHybrid_mem hp.1.1 hp.1.2 j, ?_⟩, ?_⟩
    · exact (Fintype.mem_piFinset.mp hp.1.2) j
    · rw [← prefixHybrid_succ]; exact hp.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ q ∈ T, (S.filter fun p => φ p = q).card
      = ∏ i ∈ Finset.univ.erase j, (A i).card := by
    intro q hq
    obtain ⟨w, a⟩ := q
    rw [hT, Finset.mem_filter, Finset.mem_product] at hq
    have : S.filter (fun p => φ p = (w, a))
        = (Fintype.piFinset A ×ˢ Fintype.piFinset A).filter
            (fun p => (prefixHybrid p.1 p.2 j, p.2 j) = (w, a)) := by
      ext p
      simp only [hS, hφ, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, h⟩; exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩
        refine ⟨⟨hp, ?_⟩, h⟩
        have h1 : prefixHybrid p.1 p.2 j = w := (Prod.mk.injEq _ _ _ _ ▸ h).1
        have h2 : p.2 j = a := (Prod.mk.injEq _ _ _ _ ▸ h).2
        rw [prefixHybrid_succ, h1, h2]
        exact hq.2
    rw [this, fiber_eq A w j a hq.1.1 hq.1.2, Finset.card_product,
      card_prefixBox_mul_card_suffixBox]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-! ### The resampling bound -/

/-- A disagreeing pair has a disagreeing hybrid edge: the union bound over the `k` edges. -/
theorem sectionDisagreement_piFinset_le_sum_hybridEdge :
    sectionDisagreement (Fintype.piFinset A) R ≤ ∑ j : Fin k, hybridEdgeDisagreement R A j := by
  classical
  unfold sectionDisagreement
  set box := Fintype.piFinset A
  have hsub : (box ×ˢ box).filter (fun q => ¬ (R q.1 ↔ R q.2))
      ⊆ Finset.univ.biUnion fun j : Fin k =>
          (box ×ˢ box).filter
            fun p => ¬ (R (prefixHybrid p.1 p.2 j) ↔ R (prefixHybrid p.1 p.2 (j + 1))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hne⟩ := hp
    rw [Finset.mem_biUnion]
    by_contra hall
    -- every edge agrees, so `R x ↔ R z_m` for every level `m ≤ k`, in particular `R x ↔ R y`.
    have hlevel : ∀ m : ℕ, m ≤ k → (R p.1 ↔ R (prefixHybrid p.1 p.2 m)) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have hmk : m < k := hm
        have hedge : p ∉ (box ×ˢ box).filter (fun p => ¬ (R (prefixHybrid p.1 p.2 (⟨m, hmk⟩ : Fin k))
            ↔ R (prefixHybrid p.1 p.2 ((⟨m, hmk⟩ : Fin k) + 1)))) :=
          fun h => hall ⟨⟨m, hmk⟩, Finset.mem_univ _, h⟩
        rw [Finset.mem_filter] at hedge
        have hiff : R (prefixHybrid p.1 p.2 m) ↔ R (prefixHybrid p.1 p.2 (m + 1)) := by
          by_contra hne
          exact hedge ⟨hp, hne⟩
        exact (ih (Nat.le_of_lt hmk)).trans hiff
    have := hlevel k le_rfl
    rw [prefixHybrid_of_le _ _ le_rfl] at this
    exact hne this
  calc ((box ×ˢ box).filter fun q => ¬ (R q.1 ↔ R q.2)).card
      ≤ (Finset.univ.biUnion fun j : Fin k => (box ×ˢ box).filter
          fun p => ¬ (R (prefixHybrid p.1 p.2 j) ↔ R (prefixHybrid p.1 p.2 (j + 1)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j : Fin k, hybridEdgeDisagreement R A j := Finset.card_biUnion_le

/-- The minority of `R` on the box: the smaller of the true and the false counts. -/
def minorityCount : ℕ :=
  min ((Fintype.piFinset A).filter R).card
    ((Fintype.piFinset A).card - ((Fintype.piFinset A).filter R).card)

omit [∀ i, DecidableEq (V i)] in
theorem minorityCount_le : minorityCount R A ≤ ((Fintype.piFinset A).filter R).card :=
  Nat.min_le_left _ _

omit [∀ i, DecidableEq (V i)] in
theorem minorityCount_le_sub :
    minorityCount R A ≤ (Fintype.piFinset A).card - ((Fintype.piFinset A).filter R).card :=
  Nat.min_le_right _ _

/-- Over a common carrier the true count is `tupleCount`. -/
theorem minorityCount_eq_min_tupleCount {α : Type*} [DecidableEq α] (R : (Fin k → α) → Prop)
    [DecidablePred R] (A : Fin k → Finset α) :
    minorityCount R A = min (tupleCount R A) ((Fintype.piFinset A).card - tupleCount R A) := rfl

/-- `min(c, n − c) · n ≤ 2·c·(n − c)` for `c ≤ n`. -/
theorem min_mul_le_two_mul {c n : ℕ} (hc : c ≤ n) :
    min c (n - c) * n ≤ 2 * c * (n - c) := by
  rcases le_or_gt c (n - c) with h | h
  · rw [min_eq_left h]
    have : n ≤ 2 * (n - c) := by omega
    calc c * n ≤ c * (2 * (n - c)) := Nat.mul_le_mul_left c this
      _ = 2 * c * (n - c) := by ring
  · rw [min_eq_right h.le]
    have : n ≤ 2 * c := by omega
    calc (n - c) * n ≤ (n - c) * (2 * c) := Nat.mul_le_mul_left _ this
      _ = 2 * c * (n - c) := by ring

/-- **The coordinate-resampling bound.** The minority of `R` on the box, times the box size, is
at most the sum over coordinates of the resampling disagreement weighted by the off-coordinate
box size. In `ℕ`, division-free; empty factors and `k = 0` need no hypothesis. -/
theorem minorityCount_mul_card_le :
    minorityCount R A * (Fintype.piFinset A).card
      ≤ ∑ j : Fin k, coordDisagreement R A j * ∏ i ∈ Finset.univ.erase j, (A i).card := by
  classical
  have hc : ((Fintype.piFinset A).filter R).card ≤ (Fintype.piFinset A).card :=
    Finset.card_filter_le _ _
  have hdis : sectionDisagreement (Fintype.piFinset A) R
      = 2 * ((Fintype.piFinset A).filter R).card
          * ((Fintype.piFinset A).card - ((Fintype.piFinset A).filter R).card) := by
    rw [sectionDisagreement_eq]
    congr 1
    have := Finset.card_filter_add_card_filter_not (s := Fintype.piFinset A) (p := R)
    omega
  calc minorityCount R A * (Fintype.piFinset A).card
      ≤ 2 * ((Fintype.piFinset A).filter R).card
          * ((Fintype.piFinset A).card - ((Fintype.piFinset A).filter R).card) :=
        min_mul_le_two_mul hc
    _ = sectionDisagreement (Fintype.piFinset A) R := hdis.symm
    _ ≤ ∑ j : Fin k, hybridEdgeDisagreement R A j :=
        sectionDisagreement_piFinset_le_sum_hybridEdge R A
    _ = ∑ j : Fin k, coordDisagreement R A j * ∏ i ∈ Finset.univ.erase j, (A i).card :=
        Finset.sum_congr rfl fun j _ => hybridEdgeDisagreement_eq R A j

/-! ### Endpoints -/

omit [∀ i, DecidableEq (V i)] in
/-- An empty factor empties the box: every count is `0`. -/
theorem coordDisagreement_of_eq_empty {i : Fin k} (hi : A i = ∅) (j : Fin k) :
    coordDisagreement R A j = 0 := by
  unfold coordDisagreement
  have : Fintype.piFinset A = ∅ := by
    rw [Fintype.piFinset_eq_empty]; exact ⟨i, hi⟩
  simp [this]

omit [∀ i, DecidableEq (V i)] in
theorem minorityCount_of_eq_empty {i : Fin k} (hi : A i = ∅) : minorityCount R A = 0 := by
  unfold minorityCount
  have : Fintype.piFinset A = ∅ := by
    rw [Fintype.piFinset_eq_empty]; exact ⟨i, hi⟩
  simp [this]

omit [∀ i, DecidableEq (V i)] in
/-- For `k = 0` the box is a single point and the minority is `0`. -/
theorem minorityCount_zero {V : Fin 0 → Type*} [∀ i, DecidableEq (V i)] (R : (∀ i, V i) → Prop)
    [DecidablePred R] (A : ∀ i, Finset (V i)) :
    minorityCount R A = 0 := by
  have hcard : (Fintype.piFinset A).card = 1 := by
    rw [Fintype.card_piFinset]; simp
  have hc : ((Fintype.piFinset A).filter R).card ≤ (Fintype.piFinset A).card :=
    Finset.card_filter_le _ _
  rw [hcard] at hc
  simp only [minorityCount, hcard]
  omega

/-! ### The normalized bound -/

/-- **The normalized resampling bound.** The minority is at most the sum over coordinates of
the resampling disagreement divided by the size of that factor: `minorityCount_mul_card_le`
divided by the box size. Guard-free: an empty factor makes both sides `0`. -/
theorem minorityCount_le_sum_coordDisagreement_div :
    (minorityCount R A : ℝ) ≤ ∑ j : Fin k, (coordDisagreement R A j : ℝ) / (A j).card := by
  classical
  by_cases hA : ∀ i, (A i).Nonempty
  · have hpos : ∀ i, (0 : ℝ) < (A i).card := fun i => by exact_mod_cast (hA i).card_pos
    have hbox : (0 : ℝ) < (Fintype.piFinset A).card := by
      rw [Fintype.card_piFinset]; push_cast
      exact Finset.prod_pos fun i _ => hpos i
    have hprod : ∀ j : Fin k, ((Fintype.piFinset A).card : ℝ)
        = (A j).card * ∏ i ∈ Finset.univ.erase j, ((A i).card : ℝ) := by
      intro j
      rw [Fintype.card_piFinset]; push_cast
      exact (Finset.mul_prod_erase Finset.univ (fun i => ((A i).card : ℝ))
        (Finset.mem_univ j)).symm
    have hterm : ∀ j : Fin k, (coordDisagreement R A j : ℝ) / (A j).card
        = ((coordDisagreement R A j : ℝ) * ∏ i ∈ Finset.univ.erase j, ((A i).card : ℝ))
            / (Fintype.piFinset A).card := by
      intro j
      have h2 : (0 : ℝ) < ∏ i ∈ Finset.univ.erase j, ((A i).card : ℝ) :=
        Finset.prod_pos fun i _ => hpos i
      rw [hprod j, mul_div_mul_right _ _ h2.ne']
    have hsum : ∑ j : Fin k, (coordDisagreement R A j : ℝ) / (A j).card
        = (∑ j : Fin k, (coordDisagreement R A j : ℝ)
            * ∏ i ∈ Finset.univ.erase j, ((A i).card : ℝ)) / (Fintype.piFinset A).card := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => hterm j
    rw [hsum, le_div_iff₀ hbox]
    exact_mod_cast minorityCount_mul_card_le R A
  · rw [not_forall] at hA
    obtain ⟨i, hi⟩ := hA
    rw [Finset.not_nonempty_iff_eq_empty] at hi
    rw [minorityCount_of_eq_empty R A hi]
    simp [coordDisagreement_of_eq_empty R A hi]

/-! ### Tests and adversarial examples -/

section Tests

-- A binary relation on `{0,1} × {0,1,2}`: `R x ↔ x 0 = 0`. Resampling coordinate `0` flips the
-- value whenever the new value differs, resampling coordinate `1` never does.
private def R₂ : (Fin 2 → Fin 3) → Prop := fun x => x 0 = 0
private instance : DecidablePred R₂ := fun x => inferInstanceAs (Decidable (x 0 = 0))
private def A₂ : Fin 2 → Finset (Fin 3) := ![{0, 1}, {0, 1, 2}]

example : coordDisagreement R₂ A₂ 1 = 0 := by decide
-- Coordinate `0`: `w ∈ box` (6 tuples), `a ∈ {0,1}`; the value flips iff exactly one of `w 0`, `a`
-- is `0`: `3·1 + 3·1 = 6` pairs.
example : coordDisagreement R₂ A₂ 0 = 6 := by decide
-- The prefix-swap identity, concretely: `6 · |A 1| = 18` disagreeing hybrid edges at `j = 0`.
example : hybridEdgeDisagreement R₂ A₂ 0 = 18 := by decide
example : hybridEdgeDisagreement R₂ A₂ 0
    = coordDisagreement R₂ A₂ 0 * ∏ i ∈ Finset.univ.erase (0 : Fin 2), (A₂ i).card :=
  hybridEdgeDisagreement_eq R₂ A₂ 0
-- The minority is `3` (three true, three false), and `3 · 6 = 18 ≤ 6·3 + 0·2`.
example : minorityCount R₂ A₂ = 3 := by decide
example : minorityCount R₂ A₂ * (Fintype.piFinset A₂).card ≤ 18 := by decide

-- **Empty factor** and **`k = 0`**.
example : minorityCount R₂ ![{0, 1}, ∅] = 0 := minorityCount_of_eq_empty R₂ _ (i := 1) rfl
example (R : (Fin 0 → Fin 3) → Prop) [DecidablePred R] : minorityCount R (fun i => i.elim0) = 0 :=
  minorityCount_zero R _

-- **Genuinely different coordinate types**: coordinate `0` is a `Bool`, coordinate `1` a `Fin 3`.
-- `R₃ x ↔ x 0 = true ∧ x 1 ≠ 0` on the box `{true, false} × {0, 1}` (four tuples, one true).
private abbrev T₃ : Fin 2 → Type := ![Bool, Fin 3]
private instance : ∀ i : Fin 2, DecidableEq (T₃ i)
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq Bool)
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (Fin 3))
private def fst₃ (x : ∀ i, T₃ i) : Bool := x 0
private def snd₃ (x : ∀ i, T₃ i) : Fin 3 := x 1
private def R₃ : (∀ i, T₃ i) → Prop := fun x => fst₃ x = true ∧ snd₃ x ≠ 0
private instance : DecidablePred R₃ :=
  fun x => inferInstanceAs (Decidable (fst₃ x = true ∧ snd₃ x ≠ 0))
private def A₃ : ∀ i : Fin 2, Finset (T₃ i)
  | ⟨0, _⟩ => ({true, false} : Finset Bool)
  | ⟨1, _⟩ => ({0, 1} : Finset (Fin 3))

-- Resampling the `Bool` coordinate flips `R₃` exactly on the two tuples with `x 1 = 1`, once each;
-- resampling the `Fin 3` coordinate flips it exactly on the two tuples with `x 0 = true`.
example : coordDisagreement R₃ A₃ 0 = 2 := by decide
example : coordDisagreement R₃ A₃ 1 = 2 := by decide
example : hybridEdgeDisagreement R₃ A₃ 0 = 4 := by decide
example : minorityCount R₃ A₃ = 1 := by decide
-- The bound, concretely: `1 · 4 ≤ 2 · 2 + 2 · 2`.
example : minorityCount R₃ A₃ * (Fintype.piFinset A₃).card
    ≤ ∑ j : Fin 2, coordDisagreement R₃ A₃ j * ∏ i ∈ Finset.univ.erase j, (A₃ i).card := by
  decide

-- **Prefix hybrids at the ends and one step.**
example (x y : Fin 2 → Fin 3) : prefixHybrid x y 0 = x := prefixHybrid_zero x y
example (x y : Fin 2 → Fin 3) : prefixHybrid x y 2 = y := prefixHybrid_of_le x y le_rfl
example : prefixHybrid ![(0 : Fin 3), 1] ![2, 2] 1 = ![2, 1] := by decide

end Tests

end RegularityLemmata
