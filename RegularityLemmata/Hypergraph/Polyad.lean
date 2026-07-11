/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Colored

/-!
# Polyads, polyad blocks, and disc regularity

The level-`(j+1)` objects of hypergraph regularity relative to a level-`j` cell
assignment `κ : RSet j α → Fin K` — a coloring of the **unordered** `j`-element
sets, so cell data carries no ordered junk and polyads are automatically invariant
under permuting the tuple (`comp_perm_mem_polyadBlock`). Ordered face structures, if
ever needed, would be exposed separately, never as this API. The **polyad block** of
a key `P` collects the injective `(j+1)`-tuples each of whose lower-face `j`-sets
lies in the cell prescribed by `P`; blocks partition the injective tuples
(`sum_card_polyadBlock`). A **disc atom** further restricts every lower face to a
prescribed set of `j`-sets.

Two regularity predicates are stated over these test surfaces, with densities the
guard-free `densityOn` and observables `Prop`-valued per house convention:

* `IsPolyadRegular` — the `(δ, d, r)` condition of V. Rödl, J. Skokan, *Regularity
  lemma for k-uniform hypergraphs*, Random Structures Algorithms 25 (2004), and
  B. Nagle, V. Rödl, M. Schacht, *The counting lemma for regular k-uniform
  hypergraphs*, Random Structures Algorithms 28 (2006): all tests stay inside ONE
  polyad block, quantify over at most `r` face-set families, and use a
  parent-relative threshold — the union of the corresponding disc atoms must hold at
  least a `δ` fraction of the parent block.
* `IsDiscRegular` — the single-family (`r = 1`) surface, exactly
  (`isPolyadRegular_one_iff`); a discrepancy condition in the tradition of
  quasirandomness via discrepancy (F. R. K. Chung, R. L. Graham, *Quasi-random
  hypergraphs*, Random Structures Algorithms 1 (1990)) and the relative/sub-cylinder
  test surfaces of W. T. Gowers, *Hypergraph regularity and the multidimensional
  Szemerédi theorem*, Ann. of Math. 166 (2007), and T. Tao, *A variant of the
  hypergraph removal lemma*, JCTA 113 (2006).
* `IsBlockUnionRegular` — a **repository-specific coarse test**, NOT the published
  `(δ, d, r)` condition: it unions whole blocks across different keys and its
  threshold `thr` bounds the TOTAL size of the union absolutely (not per selected
  block, and not relative to a parent).

Degeneracies are stated, not hidden: an unrealized key gives an empty parent block,
where the parent-relative threshold `δ·0 ≤ 0` is vacuous and disc regularity forces
`|d| ≤ δ`; likewise `thr = 0` admits the empty union in the block-union test. Both
are exercised adversarially in the test section.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### Lower-face sets -/

/-- The vertex set of the `i`-th lower face of a `(j+1)`-tuple: the range of the
tuple that drops coordinate `i`. -/
def lowerFaceSet (v : Fin (j + 1) → α) (i : Fin (j + 1)) : Finset α :=
  tupleRange (lowerFace v i)

omit [Fintype α] in
theorem lowerFaceSet_eq_image_erase (v : Fin (j + 1) → α) (i : Fin (j + 1)) :
    lowerFaceSet v i = (Finset.univ.erase i).image v := by
  rw [lowerFaceSet, tupleRange]
  have himg : Finset.univ.image (i.succAbove) = Finset.univ.erase i := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Fin.succAbove_ne i x, trivial⟩
    · rintro ⟨hk, -⟩
      obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hk
      exact ⟨x, rfl⟩
  rw [← himg, Finset.image_image]
  rfl

omit [Fintype α] in
theorem card_lowerFaceSet {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (i : Fin (j + 1)) : (lowerFaceSet v i).card = j :=
  card_tupleRange_of_injective (lowerFace_injective hv i)

/-- The `i`-th lower face of an injective tuple as an unordered `j`-set. -/
def lowerFaceRSet {v : Fin (j + 1) → α} (hv : Function.Injective v)
    (i : Fin (j + 1)) : RSet j α :=
  ⟨lowerFaceSet v i, card_lowerFaceSet hv i⟩

omit [Fintype α] in
/-- Permuting the tuple permutes its face sets. -/
theorem lowerFaceSet_comp_perm (v : Fin (j + 1) → α) (σ : Equiv.Perm (Fin (j + 1)))
    (i : Fin (j + 1)) : lowerFaceSet (v ∘ σ) i = lowerFaceSet v (σ i) := by
  rw [lowerFaceSet_eq_image_erase, lowerFaceSet_eq_image_erase]
  have : (Finset.univ.erase i).image σ = Finset.univ.erase (σ i) := by
    rw [Finset.image_erase σ.injective, Finset.image_univ_of_surjective σ.surjective]
  rw [← this, Finset.image_image]

/-! ### Polyad blocks -/

/-- The **polyad block** of a key `P`: the injective `(j+1)`-tuples whose every
lower-face `j`-set is colored by the corresponding key entry. The face-cardinality
hypothesis is redundant given injectivity, but phrasing it dependently keeps the
filter computable (cf. `ColoredHypergraph.copyCount`). -/
def polyadBlock (κ : RSet j α → Fin K) (P : Fin (j + 1) → Fin K) :
    Finset (Fin (j + 1) → α) :=
  Finset.univ.filter fun v => Function.Injective v ∧
    ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
      κ ⟨lowerFaceSet v i, h⟩ = P i

theorem mem_polyadBlock {κ : RSet j α → Fin K} {P : Fin (j + 1) → Fin K}
    {v : Fin (j + 1) → α} :
    v ∈ polyadBlock κ P ↔ Function.Injective v ∧
      ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
        κ ⟨lowerFaceSet v i, h⟩ = P i := by
  simp [polyadBlock]

theorem injective_of_mem_polyadBlock {κ : RSet j α → Fin K}
    {P : Fin (j + 1) → Fin K} {v : Fin (j + 1) → α} (hv : v ∈ polyadBlock κ P) :
    Function.Injective v :=
  (mem_polyadBlock.mp hv).1

/-- Clean membership for injective tuples: the polyad is the tuple of face colors. -/
theorem mem_polyadBlock_iff_of_injective {κ : RSet j α → Fin K}
    {P : Fin (j + 1) → Fin K} {v : Fin (j + 1) → α} (hv : Function.Injective v) :
    v ∈ polyadBlock κ P ↔ ∀ i, κ (lowerFaceRSet hv i) = P i := by
  rw [mem_polyadBlock]
  constructor
  · intro h i
    exact h.2 i (card_lowerFaceSet hv i)
  · intro h
    exact ⟨hv, fun i _ => h i⟩

theorem polyadBlock_disjoint {κ : RSet j α → Fin K} {P P' : Fin (j + 1) → Fin K}
    (h : P ≠ P') : Disjoint (polyadBlock κ P) (polyadBlock κ P') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_polyadBlock] at hv hv'
  refine h (funext fun i => ?_)
  rw [← hv.2 i (card_lowerFaceSet hv.1 i), hv'.2 i (card_lowerFaceSet hv.1 i)]

theorem biUnion_polyadBlock (κ : RSet j α → Fin K) :
    (Finset.univ : Finset (Fin (j + 1) → Fin K)).biUnion (polyadBlock κ)
      = injectiveTuples α (j + 1) := by
  ext v
  rw [Finset.mem_biUnion, mem_injectiveTuples]
  constructor
  · rintro ⟨P, -, hP⟩
    exact injective_of_mem_polyadBlock hP
  · intro hv
    refine ⟨fun i => κ (lowerFaceRSet hv i), Finset.mem_univ _, ?_⟩
    rw [mem_polyadBlock_iff_of_injective hv]
    intro i
    rfl

/-- **Partition of the injective tuples.** Every injective `(j+1)`-tuple lies in
exactly one polyad block, so the block cardinalities sum to the injective count. -/
theorem sum_card_polyadBlock (κ : RSet j α → Fin K) :
    ∑ P : Fin (j + 1) → Fin K, (polyadBlock κ P).card
      = injectiveTupleCount α (j + 1) := by
  classical
  rw [injectiveTupleCount, ← biUnion_polyadBlock κ]
  exact (Finset.card_biUnion fun P _ P' _ h => polyadBlock_disjoint h).symm

/-- **Permutation invariance**: reordering the tuple permutes the key. Unordered
cell data makes this automatic — the face sets themselves are permuted. -/
theorem comp_perm_mem_polyadBlock {κ : RSet j α → Fin K} {P : Fin (j + 1) → Fin K}
    {v : Fin (j + 1) → α} (σ : Equiv.Perm (Fin (j + 1))) :
    v ∘ σ ∈ polyadBlock κ P ↔ v ∈ polyadBlock κ (P ∘ ⇑σ⁻¹) := by
  constructor
  · intro h
    have hvσ : Function.Injective (v ∘ σ) := injective_of_mem_polyadBlock h
    have hv : Function.Injective v := (Equiv.injective_comp σ v).mp hvσ
    rw [mem_polyadBlock_iff_of_injective hv]
    intro i
    have hcol := (mem_polyadBlock_iff_of_injective hvσ).mp h (σ⁻¹ i)
    have hset : lowerFaceSet (v ∘ σ) (σ⁻¹ i) = lowerFaceSet v i := by
      rw [lowerFaceSet_comp_perm]
      exact congrArg (lowerFaceSet v) (σ.apply_symm_apply i)
    show κ (lowerFaceRSet hv i) = P (σ⁻¹ i)
    rw [← hcol]
    exact congrArg κ (Subtype.ext hset.symm)
  · intro h
    have hv : Function.Injective v := injective_of_mem_polyadBlock h
    have hvσ : Function.Injective (v ∘ σ) := (Equiv.injective_comp σ v).mpr hv
    rw [mem_polyadBlock_iff_of_injective hvσ]
    intro i
    have hcol := (mem_polyadBlock_iff_of_injective hv).mp h (σ i)
    have hset : lowerFaceSet (v ∘ σ) i = lowerFaceSet v (σ i) :=
      lowerFaceSet_comp_perm v σ i
    have hP : (P ∘ ⇑σ⁻¹) (σ i) = P i := congrArg P (σ.symm_apply_apply i)
    show κ (lowerFaceRSet hvσ i) = P i
    rw [← hP, ← hcol]
    exact congrArg κ (Subtype.ext hset)

/-! ### Disc atoms -/

/-- A **disc atom**: the tuples of the polyad block `key` whose every lower-face
`j`-set lies in the prescribed set family `P i`. Finer than any block or union of
blocks. -/
def discAtom (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K)
    (P : Fin (j + 1) → Finset (RSet j α)) : Finset (Fin (j + 1) → α) :=
  (polyadBlock κ key).filter fun v =>
    ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
      (⟨lowerFaceSet v i, h⟩ : RSet j α) ∈ P i

theorem mem_discAtom {κ : RSet j α → Fin K} {key : Fin (j + 1) → Fin K}
    {P : Fin (j + 1) → Finset (RSet j α)} {v : Fin (j + 1) → α} :
    v ∈ discAtom κ key P ↔ v ∈ polyadBlock κ key ∧
      ∀ (i : Fin (j + 1)) (h : (lowerFaceSet v i).card = j),
        (⟨lowerFaceSet v i, h⟩ : RSet j α) ∈ P i := by
  simp [discAtom]

/-- Clean membership for tuples of the parent block. -/
theorem mem_discAtom_iff_of_injective {κ : RSet j α → Fin K}
    {key : Fin (j + 1) → Fin K} {P : Fin (j + 1) → Finset (RSet j α)}
    {v : Fin (j + 1) → α} (hv : Function.Injective v) :
    v ∈ discAtom κ key P
      ↔ v ∈ polyadBlock κ key ∧ ∀ i, lowerFaceRSet hv i ∈ P i := by
  rw [mem_discAtom]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i
    exact h i (card_lowerFaceSet hv i)
  · intro h i _
    exact h i

theorem discAtom_subset_polyadBlock (κ : RSet j α → Fin K)
    (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (RSet j α)) :
    discAtom κ key P ⊆ polyadBlock κ key :=
  Finset.filter_subset _ _

/-- Unrestricted faces recover the whole block. -/
theorem discAtom_univ (κ : RSet j α → Fin K) (key : Fin (j + 1) → Fin K) :
    discAtom κ key (fun _ => Finset.univ) = polyadBlock κ key := by
  rw [discAtom]
  exact Finset.filter_true_of_mem fun v _ i h => Finset.mem_univ _

theorem discAtom_mono {κ : RSet j α → Fin K} {key : Fin (j + 1) → Fin K}
    {P P' : Fin (j + 1) → Finset (RSet j α)} (h : ∀ i, P i ⊆ P' i) :
    discAtom κ key P ⊆ discAtom κ key P' := by
  intro v hv
  rw [mem_discAtom] at hv ⊢
  exact ⟨hv.1, fun i hi => h i (hv.2 i hi)⟩

/-! ### Polyad regularity: the `(δ, d, r)` form -/

/-- **`(δ, d, r)` polyad regularity** (Rödl–Skokan; Nagle–Rödl–Schacht): for every
polyad key and every system of at most `r` face-set families within that key, if the
union of the corresponding disc atoms holds at least a `δ` fraction of the parent
block, then the `obs`-density on that union is within `δ` of `d`. All tests stay
inside one polyad and the threshold is parent-relative. For an unrealized key the
parent block is empty and the threshold is vacuous, so the predicate forces
`|d| ≤ δ` there (adversarial test below). -/
def IsPolyadRegular (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (d δ : ℝ) (r : ℕ) : Prop :=
  ∀ (key : Fin (j + 1) → Fin K) (F : Fin r → Fin (j + 1) → Finset (RSet j α)),
    δ * ((polyadBlock κ key).card : ℝ)
        ≤ (((Finset.univ : Finset (Fin r)).biUnion
              fun t => discAtom κ key (F t)).card : ℝ) →
    |densityOn ((Finset.univ : Finset (Fin r)).biUnion
        fun t => discAtom κ key (F t)) obs - d| ≤ δ

/-- **Disc regularity**: the single-family surface — within every polyad block, on
every face-set family whose disc atom holds at least a `δ` fraction of the parent,
the `obs`-density is within `δ` of `d`. Exactly the `r = 1` polyad regularity
(`isPolyadRegular_one_iff`). -/
def IsDiscRegular (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (d δ : ℝ) : Prop :=
  ∀ (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (RSet j α)),
    δ * ((polyadBlock κ key).card : ℝ) ≤ ((discAtom κ key P).card : ℝ) →
    |densityOn (discAtom κ key P) obs - d| ≤ δ

/-- **The exact `r = 1` bridge.** -/
theorem isPolyadRegular_one_iff {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} :
    IsPolyadRegular κ obs d δ 1 ↔ IsDiscRegular κ obs d δ := by
  constructor
  · intro h key P
    have h1 := h key fun _ => P
    rwa [Finset.univ_unique, Finset.singleton_biUnion] at h1
  · intro h key F
    have h1 := h key (F default)
    rwa [Finset.univ_unique, Finset.singleton_biUnion]

/-- Weakening the tolerance preserves polyad regularity: the premise threshold rises
and the conclusion loosens together. -/
theorem IsPolyadRegular.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ} {r : ℕ}
    (h : IsPolyadRegular κ obs d δ r) (hδ : δ ≤ δ') :
    IsPolyadRegular κ obs d δ' r := by
  intro key F hcard
  refine le_trans (h key F ?_) hδ
  exact le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) hcard

/-- Weakening the tolerance preserves disc regularity. -/
theorem IsDiscRegular.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ}
    (h : IsDiscRegular κ obs d δ) (hδ : δ ≤ δ') : IsDiscRegular κ obs d δ' := by
  intro key P hcard
  refine le_trans (h key P ?_) hδ
  exact le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) hcard

/-- Disc regularity controls every whole block (unrestricted faces pass the
parent-relative threshold once `δ ≤ 1`). -/
theorem IsDiscRegular.polyadBlock_density {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ}
    (h : IsDiscRegular κ obs d δ) (hδ : δ ≤ 1) (key : Fin (j + 1) → Fin K) :
    |densityOn (polyadBlock κ key) obs - d| ≤ δ := by
  have hd := h key (fun _ => Finset.univ) ?_
  · rwa [discAtom_univ] at hd
  · rw [discAtom_univ]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hδ

/-! ### Block-union regularity: a repository-specific coarse test -/

/-- **Block-union regularity** — a repository-specific coarse test, and NOT the
published `(δ, d, r)` polyad condition (that is `IsPolyadRegular`): here the union
ranges over whole blocks with possibly DIFFERENT keys, and the threshold `thr` is an
absolute bound on the TOTAL size of the union — not a per-block bound, and not
relative to a parent block. `thr = 0` admits the empty union, which forces `|d| ≤ δ`
(adversarial test below); callers should keep `thr` positive. -/
def IsBlockUnionRegular (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (d δ : ℝ) (r thr : ℕ) : Prop :=
  ∀ Q : Finset (Fin (j + 1) → Fin K), Q.card ≤ r →
    thr ≤ (Q.biUnion (polyadBlock κ)).card →
    |densityOn (Q.biUnion (polyadBlock κ)) obs - d| ≤ δ

/-- Weakening the tolerance preserves block-union regularity. -/
theorem IsBlockUnionRegular.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ} {r thr : ℕ}
    (h : IsBlockUnionRegular κ obs d δ r thr) (hδ : δ ≤ δ') :
    IsBlockUnionRegular κ obs d δ' r thr :=
  fun Q hr hthr => le_trans (h Q hr hthr) hδ

/-- Shrinking the union budget preserves block-union regularity (fewer tests). -/
theorem IsBlockUnionRegular.anti_r {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {r r' thr : ℕ}
    (h : IsBlockUnionRegular κ obs d δ r thr) (hr : r' ≤ r) :
    IsBlockUnionRegular κ obs d δ r' thr :=
  fun Q hQ hthr => h Q (hQ.trans hr) hthr

/-- Raising the negligibility threshold preserves block-union regularity. -/
theorem IsBlockUnionRegular.mono_thr {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {r thr thr' : ℕ}
    (h : IsBlockUnionRegular κ obs d δ r thr) (hthr : thr ≤ thr') :
    IsBlockUnionRegular κ obs d δ r thr' :=
  fun Q hQ hcard => h Q hQ (hthr.trans hcard)

/-- Disc regularity implies the `r = 1` block-union test at any positive absolute
threshold, provided `δ ≤ 1` (single whole blocks are the only nonempty unions). -/
theorem IsDiscRegular.isBlockUnionRegular_one {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {thr : ℕ}
    (h : IsDiscRegular κ obs d δ) (hδ : δ ≤ 1) (hthr : 0 < thr) :
    IsBlockUnionRegular κ obs d δ 1 thr := by
  intro Q hQ hcard
  rcases Finset.eq_empty_or_nonempty Q with rfl | hne
  · rw [Finset.biUnion_empty, Finset.card_empty] at hcard
    omega
  · obtain ⟨key, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hQ hne.card_pos)
    rw [Finset.singleton_biUnion] at hcard ⊢
    exact h.polyadBlock_density hδ key

/-! ### Tests and adversarial examples -/

section Tests

-- Level-1 cells over Fin 3: κ classifies singletons by whether they contain 2.
-- The block with both faces in cell 0 consists of the injective pairs valued in
-- {0, 1}: exactly 2 tuples.
example :
    (polyadBlock (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0)
      ![0, 0]).card = 2 := by decide

-- Mixed block ![0, 1]: face 0 = {v 1} in cell 0 and face 1 = {v 0} in cell 1, so
-- v 0 = 2 and v 1 ∈ {0, 1}: again 2 tuples.
example :
    (polyadBlock (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0)
      ![0, 1]).card = 2 := by decide

-- Partition of unity: block cards sum to the injective pair count (3)_2 = 6.
example :
    ∑ P : Fin 2 → Fin 2,
      (polyadBlock (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0)
        P).card = 6 := by
  rw [sum_card_polyadBlock]
  decide

-- Permutation invariance, concretely: the swapped key's block has the same card…
example :
    (polyadBlock (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0)
      ![1, 0]).card = 2 := by decide

-- …and the general theorem instance.
example (v : Fin 2 → Fin 3) (κ : RSet 1 (Fin 3) → Fin 2) (P : Fin 2 → Fin 2)
    (σ : Equiv.Perm (Fin 2)) :
    v ∘ σ ∈ polyadBlock κ P ↔ v ∈ polyadBlock κ (P ∘ ⇑σ⁻¹) :=
  comp_perm_mem_polyadBlock σ

-- Unrestricted disc atom = whole block (instance of the general theorem).
example :
    discAtom (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0) ![0, 0]
        (fun _ => Finset.univ)
      = polyadBlock (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0)
          ![0, 0] :=
  discAtom_univ _ _

-- Restricting one face genuinely shrinks the atom: pinning face 0 to the singleton
-- j-set {0} keeps only the pair (1, 0).
example :
    (discAtom (fun e : RSet 1 (Fin 3) => if (2 : Fin 3) ∈ e.1 then (1 : Fin 2) else 0) ![0, 0]
      ![{⟨{0}, rfl⟩}, Finset.univ]).card = 1 := by decide

-- The r = 1 bridge, as a statement-level test.
example (κ : RSet 1 (Fin 3) → Fin 2) (obs : (Fin 2 → Fin 3) → Prop)
    [DecidablePred obs] (d δ : ℝ) :
    IsPolyadRegular κ obs d δ 1 ↔ IsDiscRegular κ obs d δ :=
  isPolyadRegular_one_iff

-- Adversarial: an unrealized key has an empty parent block, where the
-- parent-relative threshold is vacuous — so disc regularity around d = 1 fails for
-- every observable.
example :
    ¬ IsDiscRegular (fun _ : RSet 1 (Fin 2) => (0 : Fin 2)) (fun _ => True)
      1 (1 / 2) := by
  intro h
  have hempty : polyadBlock (fun _ : RSet 1 (Fin 2) => (0 : Fin 2)) ![1, 1] = ∅ := by
    decide
  have h0 := h ![1, 1] (fun _ => Finset.univ) ?_
  · rw [discAtom_univ, hempty, densityOn_empty, abs_le] at h0
    linarith [h0.2]
  · rw [discAtom_univ, hempty]
    simp

-- Adversarial: with thr = 0 the empty union is a legal test of block-union
-- regularity, so no observable is block-union regular around d = 1.
example :
    ¬ IsBlockUnionRegular (fun _ : RSet 1 (Fin 3) => (0 : Fin 1)) (fun _ => True)
      1 (1 / 2) 1 0 := by
  intro h
  have h0 := h ∅ (by simp) (by simp)
  rw [Finset.biUnion_empty, densityOn_empty, abs_le] at h0
  linarith [h0.2]

end Tests

end RegularityLemmata
