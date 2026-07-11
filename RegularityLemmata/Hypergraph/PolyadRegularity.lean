/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Polyad

/-!
# Local polyad regularity

The regularity predicates over the polyad/disc test surfaces of
`Hypergraph/Polyad.lean`. The **primary predicates are local to one parent polyad**,
matching the published shape (B. Nagle, V. Rödl, M. Schacht, *The counting lemma for
regular k-uniform hypergraphs*, Random Structures Algorithms 28 (2006), Definition 9;
V. Rödl, J. Skokan, *Regularity lemma for k-uniform hypergraphs*, Random Structures
Algorithms 25 (2004)):

* `IsPolyadRegularAt κ obs key d δ r` — at the fixed key, every union of at most `r`
  disc atoms holding a `δ` fraction of the parent block has `obs`-density within `δ`
  of `d`;
* `IsDiscRegularAt κ obs key d δ` — the single-family surface, exactly the `r = 1`
  case (`isPolyadRegularAt_one_iff`);
* `IsLocalDiscRegular κ obs key δ` — the canonical Phase 7 predicate: disc
  regularity at the block's **own** density, so "bad key" is expressible, empty
  blocks are vacuously regular at their natural density `0`
  (`isLocalDiscRegular_of_empty_block`), and blocks of very different densities
  coexist.

Structural facts: tolerance monotonicity, antitonicity in `r` by padding unused
tests with empty families (`IsPolyadRegularAt.anti_r`), and permutation invariance
(`IsDiscRegularAt.comp_perm`, `IsPolyadRegularAt.comp_perm`,
`isLocalDiscRegular_comp_perm_iff`) for observables invariant under the permutation.

Global wrappers: `IsCommonDensityDiscRegular`/`IsCommonDensityPolyadRegular`
quantify the local predicates over ALL keys with one common target density — a
strictly stronger, repository-convenience form (the common-density pathology at
unrealized keys is tested adversarially). `IsBlockUnionRegular` is a
repository-specific coarse test unioning whole blocks across keys with an absolute
total-size threshold; it is NOT the published `(δ, d, r)` condition and is not used
by Phase 7.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### The local predicates -/

/-- **Local `(δ, d, r)` polyad regularity at a key** (the published, per-parent
form): for every system of at most `r` face-set families within this key, if the
union of the corresponding disc atoms holds at least a `δ` fraction of the parent
block, then the `obs`-density on that union is within `δ` of `d`. -/
def IsPolyadRegularAt (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (key : Fin (j + 1) → Fin K) (d δ : ℝ) (r : ℕ) : Prop :=
  ∀ F : Fin r → Fin (j + 1) → Finset (RSet j α),
    δ * ((polyadBlock κ key).card : ℝ)
        ≤ (((Finset.univ : Finset (Fin r)).biUnion
              fun t => discAtom κ key (F t)).card : ℝ) →
    |densityOn ((Finset.univ : Finset (Fin r)).biUnion
        fun t => discAtom κ key (F t)) obs - d| ≤ δ

/-- **Local disc regularity at a key**: the single-family surface. -/
def IsDiscRegularAt (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (key : Fin (j + 1) → Fin K) (d δ : ℝ) : Prop :=
  ∀ P : Fin (j + 1) → Finset (RSet j α),
    δ * ((polyadBlock κ key).card : ℝ) ≤ ((discAtom κ key P).card : ℝ) →
    |densityOn (discAtom κ key P) obs - d| ≤ δ

/-- **The exact `r = 1` bridge**, locally at each key. -/
theorem isPolyadRegularAt_one_iff {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ} :
    IsPolyadRegularAt κ obs key d δ 1 ↔ IsDiscRegularAt κ obs key d δ := by
  constructor
  · intro h P
    have h1 := h fun _ => P
    rwa [Finset.univ_unique, Finset.singleton_biUnion] at h1
  · intro h F
    have h1 := h (F default)
    rwa [Finset.univ_unique, Finset.singleton_biUnion]

/-- **The canonical local predicate**: disc regularity at the block's own density. -/
def IsLocalDiscRegular (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (key : Fin (j + 1) → Fin K) (δ : ℝ) : Prop :=
  IsDiscRegularAt κ obs key (densityOn (polyadBlock κ key) obs) δ

/-- **Empty parent**: at its natural density `0`, an unrealized key is vacuously
locally regular. -/
theorem isLocalDiscRegular_of_empty_block {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {δ : ℝ}
    (h : polyadBlock κ key = ∅) (hδ : 0 ≤ δ) : IsLocalDiscRegular κ obs key δ := by
  intro P _
  have hsub : discAtom κ key P = ∅ :=
    Finset.subset_empty.mp (h ▸ discAtom_subset_polyadBlock κ key P)
  rw [hsub, h, densityOn_empty, sub_zero, abs_zero]
  exact hδ

/-! ### Structural monotonicities -/

/-- Weakening the tolerance preserves local polyad regularity (the threshold rises
and the conclusion loosens together). -/
theorem IsPolyadRegularAt.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ δ' : ℝ} {r : ℕ}
    (h : IsPolyadRegularAt κ obs key d δ r) (hδ : δ ≤ δ') :
    IsPolyadRegularAt κ obs key d δ' r := by
  intro F hcard
  refine le_trans (h F ?_) hδ
  exact le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) hcard

/-- Weakening the tolerance preserves local disc regularity. -/
theorem IsDiscRegularAt.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ δ' : ℝ}
    (h : IsDiscRegularAt κ obs key d δ) (hδ : δ ≤ δ') :
    IsDiscRegularAt κ obs key d δ' := by
  intro P hcard
  refine le_trans (h P ?_) hδ
  exact le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) hcard

/-- **Antitonicity in `r`**: fewer simultaneous families are a weaker test — pad the
unused slots with empty families, which contribute empty atoms. -/
theorem IsPolyadRegularAt.anti_r {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ} {r r' : ℕ}
    (h : IsPolyadRegularAt κ obs key d δ r) (hr : r' ≤ r) :
    IsPolyadRegularAt κ obs key d δ r' := by
  classical
  intro F hthr
  set F' : Fin r → Fin (j + 1) → Finset (RSet j α) :=
    fun t => if ht : (t : ℕ) < r' then F ⟨t, ht⟩ else fun _ => ∅ with hF'
  have hunion : (Finset.univ : Finset (Fin r)).biUnion (fun t => discAtom κ key (F' t))
      = (Finset.univ : Finset (Fin r')).biUnion fun t => discAtom κ key (F t) := by
    ext v
    rw [Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨t, -, hv⟩
      by_cases ht : (t : ℕ) < r'
      · refine ⟨⟨t, ht⟩, Finset.mem_univ _, ?_⟩
        rw [hF'] at hv
        simp only [dif_pos ht] at hv
        exact hv
      · rw [hF'] at hv
        simp only [dif_neg ht] at hv
        rw [discAtom_empty_family] at hv
        exact absurd hv (Finset.notMem_empty v)
    · rintro ⟨t, -, hv⟩
      refine ⟨⟨t.1, lt_of_lt_of_le t.2 hr⟩, Finset.mem_univ _, ?_⟩
      rw [hF']
      simp only [dif_pos t.2]
      exact hv
  have h' := h F' ?_
  · rwa [hunion] at h'
  · rwa [hunion]

/-! ### Permutation invariance -/

/-- Permutation invariance of local disc regularity, for observables invariant
under `σ`. -/
theorem IsDiscRegularAt.comp_perm {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ}
    (h : IsDiscRegularAt κ obs key d δ) (σ : Equiv.Perm (Fin (j + 1)))
    (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    IsDiscRegularAt κ obs (key ∘ ⇑σ⁻¹) d δ := by
  intro P hthr
  -- Re-express `P` at `key ∘ σ⁻¹` as the transport of `fun i => P (σ i)` at `key`.
  have hfam : (fun i => P (σ (σ⁻¹ i))) = P :=
    funext fun i => congrArg P (σ.apply_symm_apply i)
  have hcard := card_discAtom_comp_perm κ key (fun i => P (σ i)) σ
  have hdens := densityOn_discAtom_comp_perm κ key (fun i => P (σ i)) obs σ hobs
  rw [show (fun i => (fun i' => P (σ i')) (σ⁻¹ i)) = P from hfam] at hcard hdens
  rw [hdens]
  refine h (fun i => P (σ i)) ?_
  rw [← hcard]
  rwa [← card_polyadBlock_comp_perm κ key σ]

/-- Permutation invariance of local disc regularity, as an equivalence. -/
theorem isDiscRegularAt_comp_perm_iff {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ} (σ : Equiv.Perm (Fin (j + 1)))
    (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    IsDiscRegularAt κ obs (key ∘ ⇑σ⁻¹) d δ ↔ IsDiscRegularAt κ obs key d δ := by
  have hobs' : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ⁻¹) ↔ obs w := by
    intro w
    have h1 := hobs (w ∘ ⇑σ⁻¹)
    have h2 : (w ∘ ⇑σ⁻¹) ∘ ⇑σ = w := funext fun x => congrArg w (σ.symm_apply_apply x)
    rw [h2] at h1
    exact h1.symm
  refine ⟨fun h => ?_, fun h => h.comp_perm σ hobs⟩
  have := h.comp_perm σ⁻¹ hobs'
  have hkey : (key ∘ ⇑σ⁻¹) ∘ ⇑σ⁻¹⁻¹ = key := by
    rw [inv_inv]
    exact funext fun i => congrArg key (σ.symm_apply_apply i)
  rwa [hkey] at this

/-- Permutation invariance of local `(δ, d, r)` polyad regularity. -/
theorem IsPolyadRegularAt.comp_perm {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ} {r : ℕ}
    (h : IsPolyadRegularAt κ obs key d δ r) (σ : Equiv.Perm (Fin (j + 1)))
    (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    IsPolyadRegularAt κ obs (key ∘ ⇑σ⁻¹) d δ r := by
  intro F hthr
  have hfam : ∀ t : Fin r, (fun i => F t (σ (σ⁻¹ i))) = F t :=
    fun t => funext fun i => congrArg (F t) (σ.apply_symm_apply i)
  -- The union at the transported key is the transport of the union at `key`.
  have hbij : ∀ (p : (Fin (j + 1) → α) → Prop), ∀ [DecidablePred p],
      (∀ w : Fin (j + 1) → α, p (w ∘ ⇑σ) ↔ p w) →
      (((Finset.univ : Finset (Fin r)).biUnion
          fun t => discAtom κ (key ∘ ⇑σ⁻¹) (F t)).filter p).card
        = (((Finset.univ : Finset (Fin r)).biUnion
            fun t => discAtom κ key fun i => F t (σ i)).filter p).card := by
    intro p _ hp
    refine Finset.card_bij' (fun v _ => v ∘ ⇑σ) (fun w _ => w ∘ ⇑σ⁻¹) (fun v hv => ?_)
      (fun w hw => ?_)
      (fun v _ => funext fun x => congrArg v (σ.apply_symm_apply x))
      (fun w _ => funext fun x => congrArg w (σ.symm_apply_apply x))
    · rw [Finset.mem_filter, Finset.mem_biUnion] at hv ⊢
      obtain ⟨⟨t, -, hv1⟩, hv2⟩ := hv
      refine ⟨⟨t, Finset.mem_univ _, ?_⟩, (hp v).mpr hv2⟩
      have := (comp_perm_mem_discAtom (κ := κ) (key := key)
        (P := fun i => F t (σ i)) (v := v) σ).mpr
      rw [show (fun i => (fun i' => F t (σ i')) (σ⁻¹ i)) = F t from hfam t] at this
      exact this hv1
    · rw [Finset.mem_filter, Finset.mem_biUnion] at hw ⊢
      obtain ⟨⟨t, -, hw1⟩, hw2⟩ := hw
      have hcomp : (w ∘ ⇑σ⁻¹) ∘ ⇑σ = w :=
        funext fun x => congrArg w (σ.symm_apply_apply x)
      constructor
      · refine ⟨t, Finset.mem_univ _, ?_⟩
        have := (comp_perm_mem_discAtom (κ := κ) (key := key)
          (P := fun i => F t (σ i)) (v := w ∘ ⇑σ⁻¹) σ).mp
        rw [show (fun i => (fun i' => F t (σ i')) (σ⁻¹ i)) = F t from hfam t] at this
        refine this ?_
        rwa [hcomp]
      · have := hp (w ∘ ⇑σ⁻¹)
        rw [hcomp] at this
        exact this.mp hw2
  have hcards := hbij (fun _ => True) (fun _ => Iff.rfl)
  rw [Finset.filter_true_of_mem fun _ _ => trivial,
    Finset.filter_true_of_mem fun _ _ => trivial] at hcards
  have hfilters := hbij obs hobs
  have hdens : densityOn ((Finset.univ : Finset (Fin r)).biUnion
        fun t => discAtom κ (key ∘ ⇑σ⁻¹) (F t)) obs
      = densityOn ((Finset.univ : Finset (Fin r)).biUnion
          fun t => discAtom κ key fun i => F t (σ i)) obs := by
    rw [densityOn, densityOn, hcards, hfilters]
  rw [hdens]
  refine h (fun t i => F t (σ i)) ?_
  rw [← hcards]
  rwa [← card_polyadBlock_comp_perm κ key σ]

/-- Permutation invariance of the canonical own-density predicate, as an
equivalence. -/
theorem isLocalDiscRegular_comp_perm_iff {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {δ : ℝ} (σ : Equiv.Perm (Fin (j + 1)))
    (hobs : ∀ w : Fin (j + 1) → α, obs (w ∘ ⇑σ) ↔ obs w) :
    IsLocalDiscRegular κ obs (key ∘ ⇑σ⁻¹) δ ↔ IsLocalDiscRegular κ obs key δ := by
  rw [IsLocalDiscRegular, IsLocalDiscRegular,
    densityOn_polyadBlock_comp_perm κ key obs σ hobs]
  exact isDiscRegularAt_comp_perm_iff σ hobs

/-! ### Whole-block control and common-density globalizations -/

/-- Local disc regularity controls the whole block once `δ ≤ 1`. -/
theorem IsDiscRegularAt.polyadBlock_density {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {d δ : ℝ}
    (h : IsDiscRegularAt κ obs key d δ) (hδ : δ ≤ 1) :
    |densityOn (polyadBlock κ key) obs - d| ≤ δ := by
  have hd := h (fun _ => Finset.univ) ?_
  · rwa [discAtom_univ] at hd
  · rw [discAtom_univ]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hδ

/-- The common-density globalization: one target density for ALL keys. Strictly
stronger than the local form — unrealized keys force `|d| ≤ δ` (adversarial test
below); Phase 7 uses the local own-density predicate instead. -/
def IsCommonDensityPolyadRegular (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (d δ : ℝ) (r : ℕ) : Prop :=
  ∀ key : Fin (j + 1) → Fin K, IsPolyadRegularAt κ obs key d δ r

/-- Common-density disc regularity over all keys. -/
def IsCommonDensityDiscRegular (κ : RSet j α → Fin K)
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] (d δ : ℝ) : Prop :=
  ∀ key : Fin (j + 1) → Fin K, IsDiscRegularAt κ obs key d δ

theorem isCommonDensityPolyadRegular_one_iff {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} :
    IsCommonDensityPolyadRegular κ obs d δ 1 ↔ IsCommonDensityDiscRegular κ obs d δ :=
  forall_congr' fun _ => isPolyadRegularAt_one_iff

theorem IsCommonDensityDiscRegular.mono_delta {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ δ' : ℝ}
    (h : IsCommonDensityDiscRegular κ obs d δ) (hδ : δ ≤ δ') :
    IsCommonDensityDiscRegular κ obs d δ' :=
  fun key => (h key).mono_delta hδ

/-! ### Block-union regularity: a repository-specific coarse test -/

/-- **Block-union regularity** — a repository-specific coarse test, and NOT the
published `(δ, d, r)` polyad condition (that is `IsPolyadRegularAt`): here the union
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

/-- Common-density disc regularity implies the `r = 1` block-union test at any
positive absolute threshold, provided `δ ≤ 1`. -/
theorem IsCommonDensityDiscRegular.isBlockUnionRegular_one {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs] {d δ : ℝ} {thr : ℕ}
    (h : IsCommonDensityDiscRegular κ obs d δ) (hδ : δ ≤ 1) (hthr : 0 < thr) :
    IsBlockUnionRegular κ obs d δ 1 thr := by
  intro Q hQ hcard
  rcases Finset.eq_empty_or_nonempty Q with rfl | hne
  · rw [Finset.biUnion_empty, Finset.card_empty] at hcard
    omega
  · obtain ⟨key, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hQ hne.card_pos)
    rw [Finset.singleton_biUnion] at hcard ⊢
    exact (h key).polyadBlock_density hδ

/-! ### Tests and adversarial examples -/

section Tests

-- The r = 1 bridge, locally, as a statement-level test.
example (κ : RSet 1 (Fin 3) → Fin 2) (obs : (Fin 2 → Fin 3) → Prop)
    [DecidablePred obs] (key : Fin 2 → Fin 2) (d δ : ℝ) :
    IsPolyadRegularAt κ obs key d δ 1 ↔ IsDiscRegularAt κ obs key d δ :=
  isPolyadRegularAt_one_iff

-- Empty parent, natural density: the unrealized key ![1, 1] of the constant-0
-- coloring is vacuously locally regular.
example :
    IsLocalDiscRegular (fun _ : RSet 1 (Fin 2) => (0 : Fin 2)) (fun _ => True)
      ![1, 1] (1 / 2) := by
  refine isLocalDiscRegular_of_empty_block ?_ (by norm_num)
  decide

-- Adversarial: the SAME unrealized key refutes the common-density globalization at
-- d = 1 — this is exactly why the canonical predicate is local.
example :
    ¬ IsCommonDensityDiscRegular (fun _ : RSet 1 (Fin 2) => (0 : Fin 2))
      (fun _ => True) 1 (1 / 2) := by
  intro h
  have hempty : polyadBlock (fun _ : RSet 1 (Fin 2) => (0 : Fin 2)) ![1, 1] = ∅ := by
    decide
  have h0 := h ![1, 1] (fun _ => Finset.univ) ?_
  · rw [discAtom_univ, hempty, densityOn_empty, abs_le] at h0
    linarith [h0.2]
  · rw [discAtom_univ, hempty]
    simp

-- Antitonicity in r via padding, as a statement-level test.
example (κ : RSet 1 (Fin 3) → Fin 2) (obs : (Fin 2 → Fin 3) → Prop)
    [DecidablePred obs] (key : Fin 2 → Fin 2) (d δ : ℝ)
    (h : IsPolyadRegularAt κ obs key d δ 3) :
    IsPolyadRegularAt κ obs key d δ 2 :=
  h.anti_r (by norm_num)

-- Permutation invariance, as a statement-level test.
example (κ : RSet 1 (Fin 3) → Fin 2) (key : Fin 2 → Fin 2) (δ : ℝ)
    (σ : Equiv.Perm (Fin 2))
    (h : IsLocalDiscRegular κ (fun _ => True) key δ) :
    IsLocalDiscRegular κ (fun _ => True) (key ∘ ⇑σ⁻¹) δ :=
  (isLocalDiscRegular_comp_perm_iff σ fun _ => Iff.rfl).mpr h

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
