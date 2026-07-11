/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Injective
import RegularityLemmata.Finite.Density

/-!
# Polyads, polyad blocks, and disc regularity

The level-`(j+1)` objects of hypergraph regularity relative to a level-`j` cell
assignment `κ`: the **polyad** of a `(j+1)`-tuple is the tuple of cells of its
`j`-element lower faces, a **polyad block** collects the injective tuples with a
prescribed polyad, and a **disc atom** further restricts every lower face to a
prescribed face set. Polyad blocks partition the injective tuples
(`sum_card_polyadBlock`) — the ordered analogue, one level up, of the colored
partition of unity.

Two regularity predicates are stated over these test surfaces, with densities the
guard-free `densityOn` and observables `Prop`-valued per house convention:

* `IsUnionRegular` — the `(δ, d, r)` form of V. Rödl, J. Skokan, *Regularity lemma
  for k-uniform hypergraphs*, Random Structures Algorithms 25 (2004) (also
  B. Nagle, V. Rödl, M. Schacht, *The counting lemma for regular k-uniform
  hypergraphs*, Random Structures Algorithms 28 (2006)): on every union of at most
  `r` polyad blocks of non-negligible size, the observable's density is within `δ`
  of the target `d`.
* `IsDiscRegular` — a discrepancy (DISC-style) condition within a single block
  against arbitrary lower-face-set families, in the tradition of quasirandomness via
  discrepancy (F. R. K. Chung, R. L. Graham, *Quasi-random hypergraphs*, Random
  Structures Algorithms 1 (1990)) and the relative/sub-cylinder test surfaces of
  W. T. Gowers, *Hypergraph regularity and the multidimensional Szemerédi theorem*,
  Ann. of Math. 166 (2007), and T. Tao, *A variant of the hypergraph removal lemma*,
  JCTA 113 (2006).

Disc regularity implies the single-block union test
(`IsDiscRegular.isUnionRegular_one`, for positive thresholds — the `thr = 0`
pathology is exercised in the test section); the union form does not control
within-block restrictions, which is why the finer disc surface is primary here.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### Polyads and polyad blocks -/

/-- The **polyad** of a `(j+1)`-tuple relative to a level-`j` cell assignment `κ`:
the tuple of the cells of its lower faces. Its `i`-th entry is the cell of the face
dropping coordinate `i`. -/
def polyad (κ : (Fin j → α) → Fin K) (v : Fin (j + 1) → α) : Fin (j + 1) → Fin K :=
  fun i => κ (lowerFace v i)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem polyad_apply (κ : (Fin j → α) → Fin K) (v : Fin (j + 1) → α)
    (i : Fin (j + 1)) : polyad κ v i = κ (lowerFace v i) := rfl

/-- The **polyad block** of `P`: the injective `(j+1)`-tuples whose polyad is `P`. -/
def polyadBlock (κ : (Fin j → α) → Fin K) (P : Fin (j + 1) → Fin K) :
    Finset (Fin (j + 1) → α) :=
  Finset.univ.filter fun v => Function.Injective v ∧ polyad κ v = P

theorem mem_polyadBlock {κ : (Fin j → α) → Fin K} {P : Fin (j + 1) → Fin K}
    {v : Fin (j + 1) → α} :
    v ∈ polyadBlock κ P ↔ Function.Injective v ∧ polyad κ v = P := by
  simp [polyadBlock]

theorem polyadBlock_eq_filter (κ : (Fin j → α) → Fin K) (P : Fin (j + 1) → Fin K) :
    polyadBlock κ P = (injectiveTuples α (j + 1)).filter fun v => polyad κ v = P := by
  ext v
  rw [mem_polyadBlock, Finset.mem_filter, mem_injectiveTuples]

/-- **Partition of the injective tuples.** Every injective `(j+1)`-tuple lies in
exactly one polyad block, so the block cardinalities sum to the injective count. -/
theorem sum_card_polyadBlock (κ : (Fin j → α) → Fin K) :
    ∑ P : Fin (j + 1) → Fin K, (polyadBlock κ P).card
      = injectiveTupleCount α (j + 1) := by
  classical
  rw [injectiveTupleCount,
    Finset.card_eq_sum_card_fiberwise
      (f := polyad κ) (t := Finset.univ) (fun v _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun P _ => congrArg Finset.card
    (polyadBlock_eq_filter κ P)

/-! ### Disc atoms -/

/-- A **disc atom**: the tuples of the polyad block `key` whose every lower face
lands in the prescribed face set `P i`. Finer than any block or union of blocks. -/
def discAtom (κ : (Fin j → α) → Fin K) (key : Fin (j + 1) → Fin K)
    (P : Fin (j + 1) → Finset (Fin j → α)) : Finset (Fin (j + 1) → α) :=
  (polyadBlock κ key).filter fun v => ∀ i, lowerFace v i ∈ P i

theorem mem_discAtom {κ : (Fin j → α) → Fin K} {key : Fin (j + 1) → Fin K}
    {P : Fin (j + 1) → Finset (Fin j → α)} {v : Fin (j + 1) → α} :
    v ∈ discAtom κ key P ↔ v ∈ polyadBlock κ key ∧ ∀ i, lowerFace v i ∈ P i := by
  simp [discAtom]

theorem discAtom_subset_polyadBlock (κ : (Fin j → α) → Fin K)
    (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (Fin j → α)) :
    discAtom κ key P ⊆ polyadBlock κ key :=
  Finset.filter_subset _ _

/-- Unrestricted faces recover the whole block. -/
theorem discAtom_univ (κ : (Fin j → α) → Fin K) (key : Fin (j + 1) → Fin K) :
    discAtom κ key (fun _ => Finset.univ) = polyadBlock κ key := by
  rw [discAtom]
  exact Finset.filter_true_of_mem fun v _ i => Finset.mem_univ _

theorem discAtom_mono {κ : (Fin j → α) → Fin K} {key : Fin (j + 1) → Fin K}
    {P P' : Fin (j + 1) → Finset (Fin j → α)} (h : ∀ i, P i ⊆ P' i) :
    discAtom κ key P ⊆ discAtom κ key P' := by
  intro v hv
  rw [mem_discAtom] at hv ⊢
  exact ⟨hv.1, fun i => h i (hv.2 i)⟩

/-! ### Union regularity: the `(δ, d, r)` form -/

/-- **`(δ, d, r)`-regularity of an observable** over unions of whole polyad blocks
(Rödl–Skokan form): on every union of at most `r` blocks of size at least `thr`, the
`obs`-density is within `δ` of `d`. `r = 1` tests single blocks; larger `r` tests
`r`-fold unions. `thr = 0` admits the empty union, which forces `|d| ≤ δ` — callers
should keep `thr` positive (see the adversarial test). -/
def IsUnionRegular (κ : (Fin j → α) → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (d δ : ℝ) (r thr : ℕ) : Prop :=
  ∀ Q : Finset (Fin (j + 1) → Fin K), Q.card ≤ r →
    thr ≤ (Q.biUnion (polyadBlock κ)).card →
    |densityOn (Q.biUnion (polyadBlock κ)) obs - d| ≤ δ

/-- Weakening the tolerance preserves union regularity. -/
theorem IsUnionRegular.mono_delta {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ} {r thr : ℕ}
    (h : IsUnionRegular κ obs d δ r thr) (hδ : δ ≤ δ') :
    IsUnionRegular κ obs d δ' r thr :=
  fun Q hr hthr => le_trans (h Q hr hthr) hδ

/-- Shrinking the union budget preserves union regularity (fewer tests). -/
theorem IsUnionRegular.anti_r {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {r r' thr : ℕ}
    (h : IsUnionRegular κ obs d δ r thr) (hr : r' ≤ r) :
    IsUnionRegular κ obs d δ r' thr :=
  fun Q hQ hthr => h Q (hQ.trans hr) hthr

/-- Raising the negligibility threshold preserves union regularity (fewer tests). -/
theorem IsUnionRegular.mono_thr {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {r thr thr' : ℕ}
    (h : IsUnionRegular κ obs d δ r thr) (hthr : thr ≤ thr') :
    IsUnionRegular κ obs d δ r thr' :=
  fun Q hQ hcard => h Q hQ (hthr.trans hcard)

/-! ### Disc regularity: the within-block surface -/

/-- **Disc regularity of an observable**: within every polyad block, on every
lower-face-set family whose disc atom is non-negligible, the `obs`-density is within
`δ` of `d`. The test surface is within-block sub-selections, strictly finer than
unions of whole blocks. -/
def IsDiscRegular (κ : (Fin j → α) → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (d δ : ℝ) (thr : ℕ) : Prop :=
  ∀ (key : Fin (j + 1) → Fin K) (P : Fin (j + 1) → Finset (Fin j → α)),
    thr ≤ (discAtom κ key P).card →
    |densityOn (discAtom κ key P) obs - d| ≤ δ

/-- Weakening the tolerance preserves disc regularity. -/
theorem IsDiscRegular.mono_delta {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ} {thr : ℕ}
    (h : IsDiscRegular κ obs d δ thr) (hδ : δ ≤ δ') :
    IsDiscRegular κ obs d δ' thr :=
  fun key P hthr => le_trans (h key P hthr) hδ

/-- Raising the negligibility threshold preserves disc regularity. -/
theorem IsDiscRegular.mono_thr {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {thr thr' : ℕ}
    (h : IsDiscRegular κ obs d δ thr) (hthr : thr ≤ thr') :
    IsDiscRegular κ obs d δ thr' :=
  fun key P hcard => h key P (hthr.trans hcard)

/-- Disc regularity controls whole single blocks (unrestricted faces). -/
theorem IsDiscRegular.polyadBlock_density {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {thr : ℕ}
    (h : IsDiscRegular κ obs d δ thr) (key : Fin (j + 1) → Fin K)
    (hcard : thr ≤ (polyadBlock κ key).card) :
    |densityOn (polyadBlock κ key) obs - d| ≤ δ := by
  rw [← discAtom_univ (κ := κ) (key := key)] at hcard ⊢
  exact h key _ hcard

/-- Disc regularity implies the `r = 1` union test, for positive thresholds (the
empty union is excluded exactly by `0 < thr`). -/
theorem IsDiscRegular.isUnionRegular_one {κ : (Fin j → α) → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {thr : ℕ}
    (h : IsDiscRegular κ obs d δ thr) (hthr : 0 < thr) :
    IsUnionRegular κ obs d δ 1 thr := by
  intro Q hQ hcard
  rcases Finset.eq_empty_or_nonempty Q with rfl | hne
  · rw [Finset.biUnion_empty, Finset.card_empty] at hcard
    omega
  · obtain ⟨key, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hQ hne.card_pos)
    rw [Finset.singleton_biUnion] at hcard ⊢
    exact h.polyadBlock_density key hcard

/-! ### Tests and adversarial examples -/

section Tests

-- Level-1 cells over Fin 3: κ classifies singletons by whether the entry is < 2.
-- The block with both faces in cell 0 consists of the injective pairs valued in
-- {0, 1}: exactly 2 tuples.
example :
    (polyadBlock (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1)
      ![0, 0]).card = 2 := by decide

-- Mixed block: one face in each cell. (v 0 ∈ {0,1} and v 1 = 2, or symmetric.)
example :
    (polyadBlock (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1)
      ![0, 1]).card = 2 := by decide

-- Partition of unity: block cards sum to the injective pair count (3)_2 = 6.
example :
    ∑ P : Fin 2 → Fin 2,
      (polyadBlock (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1) P).card
      = 6 := by
  rw [sum_card_polyadBlock]
  decide

-- Unrestricted disc atom = whole block (instance of the general theorem).
example :
    discAtom (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1) ![0, 0]
        (fun _ => Finset.univ)
      = polyadBlock (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1)
          ![0, 0] :=
  discAtom_univ _ _

-- Restricting one face genuinely shrinks the atom: pinning face 0 to the constant
-- tuple 0 keeps only the pairs with v 1 = 0.
example :
    (discAtom (fun v : Fin 1 → Fin 3 => if (v 0 : ℕ) < 2 then (0 : Fin 2) else 1) ![0, 0]
      ![{fun _ => 0}, Finset.univ]).card = 1 := by decide

-- Adversarial: with thr = 0 the empty union is a legal test of union regularity, so
-- no observable is union-regular around d = 1 — the empty union has density 0.
example :
    ¬ IsUnionRegular (fun _ : Fin 1 → Fin 3 => (0 : Fin 1)) (fun _ => True)
      1 (1/2) 1 0 := by
  intro h
  have h0 := h ∅ (by simp) (by simp)
  rw [Finset.biUnion_empty, densityOn_empty] at h0
  rw [abs_le] at h0
  linarith [h0.2]

end Tests

end RegularityLemmata
