/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.PolyadRegularity
import RegularityLemmata.Hypergraph.PolyadEnergy
import Mathlib.Algebra.BigOperators.Fin

/-!
# Disc witnesses and the simultaneous cut refinement

Phase 7 unit 4/5 infrastructure (design freeze in `ARCHITECTURE.md`): failure of
local disc regularity packaged **as data** (`DiscWitness` — face families, the
parent-relative largeness bound, and the *strict* density deviation that drives the
strict energy increment), and the **simultaneous** resolution of witnesses across all
keys. A one-key refinement cannot give a host-independent increment, so the cut
refinement indexes Boolean face tests by `(key, coordinate)` — at most
`K^(j+1) · (j+1)` cuts (for triads, `3K³`) — and refines every cell of `κ` at once.

The color encoding is **explicitly computable** (`cutRefine`), via mathlib's
computable equivalences `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` and
`finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`; the codomain is
`Fin (cutBound j K)` with `cutBound j K = K · 2^(K^(j+1)·(j+1))` — the color-count
recurrence is thereby **proved by construction**, not stated informally. The
computable projection `cutRefineProj` recovers the old color
(`cutRefineProj_comp`), so `κ` is literally a merge of `cutRefine κ W` and the
energy machinery of `Hypergraph/PolyadEnergy.lean` applies
(`polyadEnergyNum_le_cutRefine`); the bitmask is recovered by `cutRefineBit`
(`cutRefineBit_cutRefine`).

The structural theorem consumed by the increment step:
**every witness atom is a union of refined blocks**
(`discAtom_eq_biUnion_cutRefine`) — membership of a tuple in the atom of the
projected key depends only on its refined polyad key. The iteration itself follows
the index-increment strategy of V. Rödl, M. Schacht, *Regular partitions of
hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007), in the
simultaneous-witness form the graph ladder already uses (`Graph/FriezeKannan.lean`).
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {j K : ℕ}

/-! ### Failure as data -/

/-- The data of a failed local disc test at a key: a face-family system whose atom
is large relative to the parent block and whose density deviates **strictly** by
more than `δ` from the block's own density. -/
structure DiscWitness (κ : RSet j α → Fin K) (obs : (Fin (j + 1) → α) → Prop)
    [DecidablePred obs] (key : Fin (j + 1) → Fin K) (δ : ℝ) where
  /-- The prescribed face sets, one per coordinate. -/
  faces : Fin (j + 1) → Finset (RSet j α)
  /-- The disc atom holds at least a `δ` fraction of the parent block. -/
  large : δ * ((polyadBlock κ key).card : ℝ) ≤ ((discAtom κ key faces).card : ℝ)
  /-- The atom's density deviates strictly from the block's own density. -/
  deviates : δ < |densityOn (discAtom κ key faces) obs
      - densityOn (polyadBlock κ key) obs|

/-- Failure of the canonical local predicate yields a witness. -/
theorem exists_discWitness {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {δ : ℝ} (h : ¬ IsLocalDiscRegular κ obs key δ) :
    Nonempty (DiscWitness κ obs key δ) := by
  rw [IsLocalDiscRegular, IsDiscRegularAt] at h
  push Not at h
  obtain ⟨P, hthr, hdev⟩ := h
  exact ⟨⟨P, hthr, hdev⟩⟩

/-! ### The simultaneous cut refinement -/

/-- One round of simultaneous cutting takes `K` colors to at most
`K · 2^(K^(j+1)·(j+1))` colors — for triads (`j = 2`), `K · 2^(3K³)`. -/
abbrev cutBound (j K : ℕ) : ℕ := K * 2 ^ (K ^ (j + 1) * (j + 1))

/-- The simultaneous cut refinement: the old color paired with the membership
bitmask of the `j`-set in the prescribed face family of every `(key, coordinate)`
pair, encoded computably. -/
def cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α)) :
    RSet j α → Fin (cutBound j K) :=
  fun e => finProdFinEquiv
    (κ e,
     finFunctionFinEquiv fun p : Fin (K ^ (j + 1) * (j + 1)) =>
       if e ∈ W (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).1)
           (finProdFinEquiv.symm p).2 then (1 : Fin 2) else 0)

/-- The computable projection back to the old color. -/
def cutRefineProj : Fin (cutBound j K) → Fin K :=
  fun c => (finProdFinEquiv.symm c).1

/-- The cut bit of a refined color at a `(key, coordinate)` pair. -/
def cutRefineBit (c : Fin (cutBound j K)) (key : Fin (j + 1) → Fin K)
    (i : Fin (j + 1)) : Fin 2 :=
  finFunctionFinEquiv.symm ((finProdFinEquiv.symm c).2)
    (finProdFinEquiv (finFunctionFinEquiv key, i))

omit [Fintype α] in
/-- The old coloring is exactly the projection of the refined one: `κ` is a merge
of `cutRefine κ W`. -/
theorem cutRefineProj_comp (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α)) :
    (fun e => cutRefineProj (cutRefine κ W e)) = κ := by
  funext e
  rw [cutRefine, cutRefineProj, Equiv.symm_apply_apply]

omit [Fintype α] in
/-- The refined color records exactly the face-family memberships. -/
theorem cutRefineBit_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α)) (e : RSet j α)
    (key : Fin (j + 1) → Fin K) (i : Fin (j + 1)) :
    cutRefineBit (cutRefine κ W e) key i = if e ∈ W key i then 1 else 0 := by
  rw [cutRefine, cutRefineBit, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp

/-- Energy never decreases under a cut refinement (via the merge identity and
refinement monotonicity). -/
theorem polyadEnergyNum_le_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    polyadEnergyNum κ obs ≤ polyadEnergyNum (cutRefine κ W) obs := by
  have h := polyadEnergyNum_comp_le (cutRefineProj (j := j) (K := K))
    (cutRefine κ W) obs
  rwa [cutRefineProj_comp κ W] at h

/-! ### Witness atoms are unions of refined blocks -/

/-- Refined blocks sit inside the old blocks of their projected keys. -/
theorem polyadBlock_cutRefine_subset (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (Q : Fin (j + 1) → Fin (cutBound j K)) :
    polyadBlock (cutRefine κ W) Q
      ⊆ polyadBlock κ fun i => cutRefineProj (Q i) := by
  intro v hv
  have hinj := injective_of_mem_polyadBlock hv
  have hface := (mem_polyadBlock_iff_of_injective hinj).mp hv
  rw [mem_polyadBlock_iff_of_injective hinj]
  intro i
  have hproj := congrFun (cutRefineProj_comp κ W) (lowerFaceRSet hinj i)
  rw [← hproj, hface i]

-- The `κ`/`W` parameters tie the definition to its atom (`discAtom κ key (W key)`)
-- even though the resolving condition reads only `key` off the refined colors.
set_option linter.unusedVariables false in
/-- The refined keys that resolve the witness atom at `key`: keys projecting to
`key` whose cut bits at `(key, ·)` are all set. -/
def resolvingKeys (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) : Finset (Fin (j + 1) → Fin (cutBound j K)) :=
  Finset.univ.filter fun Q =>
    (∀ i, cutRefineProj (Q i) = key i) ∧ ∀ i, cutRefineBit (Q i) key i = 1

omit [Fintype α] [DecidableEq α] in
/-- Resolving keys lie in the projection fiber of `key`. -/
theorem resolvingKeys_subset_fiber (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) :
    resolvingKeys κ W key
      ⊆ Finset.univ.filter fun Q : Fin (j + 1) → Fin (cutBound j K) =>
          (fun i => cutRefineProj (Q i)) = key := by
  intro Q hQ
  rw [resolvingKeys, Finset.mem_filter] at hQ
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, funext hQ.2.1⟩

/-- **Witness atoms are unions of refined blocks**: the disc atom of `W key` at
`key` is exactly the union of the refined blocks over its resolving keys. -/
theorem discAtom_eq_biUnion_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) :
    discAtom κ key (W key)
      = (resolvingKeys κ W key).biUnion (polyadBlock (cutRefine κ W)) := by
  rw [resolvingKeys]
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · intro hv
    have hblock := (mem_discAtom.mp hv).1
    have hinj := injective_of_mem_polyadBlock hblock
    have hkey := (mem_polyadBlock_iff_of_injective hinj).mp hblock
    have hatom := (mem_discAtom_iff_of_injective hinj).mp hv
    refine ⟨fun i => cutRefine κ W (lowerFaceRSet hinj i),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, fun i => ?_⟩, ?_⟩
    · rw [congrFun (cutRefineProj_comp κ W) (lowerFaceRSet hinj i)]
      exact hkey i
    · rw [cutRefineBit_cutRefine, if_pos (hatom.2 i)]
    · rw [mem_polyadBlock_iff_of_injective hinj]
      intro i
      rfl
  · rintro ⟨Q, hQ, hv⟩
    rw [Finset.mem_filter] at hQ
    obtain ⟨-, hproj, hbit⟩ := hQ
    have hinj := injective_of_mem_polyadBlock hv
    have hface := (mem_polyadBlock_iff_of_injective hinj).mp hv
    rw [mem_discAtom_iff_of_injective hinj]
    constructor
    · rw [mem_polyadBlock_iff_of_injective hinj]
      intro i
      rw [← hproj i, ← hface i,
        congrFun (cutRefineProj_comp κ W) (lowerFaceRSet hinj i)]
    · intro i
      have hb := hbit i
      rw [← hface i, cutRefineBit_cutRefine] at hb
      by_contra hmem
      rw [if_neg hmem] at hb
      exact absurd hb (by decide)

/-- Cardinality of a witness atom: the sum over its resolving keys (the refined
blocks are pairwise disjoint). -/
theorem card_discAtom_eq_sum_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) :
    (discAtom κ key (W key)).card
      = ∑ Q ∈ resolvingKeys κ W key, (polyadBlock (cutRefine κ W) Q).card := by
  rw [discAtom_eq_biUnion_cutRefine κ W key]
  exact Finset.card_biUnion fun Q _ Q' _ h => polyadBlock_disjoint h

/-- Filtered cardinality of a witness atom: the sum over its resolving keys. -/
theorem card_filter_discAtom_eq_sum_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) (obs : (Fin (j + 1) → α) → Prop) [DecidablePred obs] :
    ((discAtom κ key (W key)).filter obs).card
      = ∑ Q ∈ resolvingKeys κ W key,
          ((polyadBlock (cutRefine κ W) Q).filter obs).card := by
  rw [discAtom_eq_biUnion_cutRefine κ W key, Finset.filter_biUnion]
  exact Finset.card_biUnion fun Q _ Q' _ h =>
    (polyadBlock_disjoint h).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-! ### The local increment -/

/-- **Local increment**: at a key carrying an actual witness in the family, the
refinement variance strictly exceeds `δ³ · |parent block|`. The strictness comes
from `DiscWitness.deviates`; the route is the restricted Engel-form Cauchy–Schwarz
over the atom's resolving keys. -/
theorem local_variance_gain {κ : RSet j α → Fin K}
    {obs : (Fin (j + 1) → α) → Prop} [DecidablePred obs]
    {key : Fin (j + 1) → Fin K} {δ : ℝ} (hδ : 0 < δ)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (w : DiscWitness κ obs key δ) (hW : W key = w.faces) :
    δ ^ 3 * ((polyadBlock κ key).card : ℝ)
      < ∑ Q ∈ Finset.univ.filter fun Q : Fin (j + 1) → Fin (cutBound j K) =>
          (fun i => cutRefineProj (Q i)) = key,
          ((polyadBlock (cutRefine κ W) Q).card : ℝ)
            * (densityOn (polyadBlock (cutRefine κ W) Q) obs
                - densityOn (polyadBlock κ key) obs) ^ 2 := by
  classical
  have hdev : δ < |densityOn (discAtom κ key (W key)) obs
      - densityOn (polyadBlock κ key) obs| := by
    rw [hW]
    exact w.deviates
  have hlarge : δ * ((polyadBlock κ key).card : ℝ)
      ≤ ((discAtom κ key (W key)).card : ℝ) := by
    rw [hW]
    exact w.large
  -- The parent block is realized: an empty block would force `δ < 0`.
  have hBpos : 0 < ((polyadBlock κ key).card : ℝ) := by
    rcases Finset.eq_empty_or_nonempty (polyadBlock κ key) with hBe | hne
    · exfalso
      have hAe : discAtom κ key (W key) = ∅ :=
        Finset.subset_empty.mp (hBe ▸ discAtom_subset_polyadBlock κ key (W key))
      rw [hAe, hBe, densityOn_empty, sub_zero, abs_zero] at hdev
      linarith
    · exact_mod_cast Finset.card_pos.mpr hne
  have hApos : 0 < ((discAtom κ key (W key)).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hlarge
  -- Cardinality decompositions over the resolving keys.
  have hcard : ((discAtom κ key (W key)).card : ℝ)
      = ∑ Q ∈ resolvingKeys κ W key,
          ((polyadBlock (cutRefine κ W) Q).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast card_discAtom_eq_sum_cutRefine κ W key
  have hfilter : (((discAtom κ key (W key)).filter obs).card : ℝ)
      = ∑ Q ∈ resolvingKeys κ W key,
          (((polyadBlock (cutRefine κ W) Q).filter obs).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast card_filter_discAtom_eq_sum_cutRefine κ W key obs
  -- The signed mass over resolving keys is the atom's total deviation.
  have hnum : ∑ Q ∈ resolvingKeys κ W key,
      ((polyadBlock (cutRefine κ W) Q).card : ℝ)
        * (densityOn (polyadBlock (cutRefine κ W) Q) obs
            - densityOn (polyadBlock κ key) obs)
      = ((discAtom κ key (W key)).card : ℝ)
        * (densityOn (discAtom κ key (W key)) obs
            - densityOn (polyadBlock κ key) obs) := by
    have hterm : ∀ Q, ((polyadBlock (cutRefine κ W) Q).card : ℝ)
        * (densityOn (polyadBlock (cutRefine κ W) Q) obs
            - densityOn (polyadBlock κ key) obs)
        = (((polyadBlock (cutRefine κ W) Q).filter obs).card : ℝ)
          - densityOn (polyadBlock κ key) obs
            * ((polyadBlock (cutRefine κ W) Q).card : ℝ) := by
      intro Q
      rw [← densityOn_mul_card (polyadBlock (cutRefine κ W) Q) obs]
      ring
    rw [Finset.sum_congr rfl fun Q _ => hterm Q, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← hfilter, ← hcard,
      ← densityOn_mul_card (discAtom κ key (W key)) obs]
    ring
  -- Restricted Engel-form Cauchy–Schwarz over the resolving keys.
  have hCS : ((discAtom κ key (W key)).card : ℝ)
      * (densityOn (discAtom κ key (W key)) obs
          - densityOn (polyadBlock κ key) obs) ^ 2
      ≤ ∑ Q ∈ resolvingKeys κ W key,
          ((polyadBlock (cutRefine κ W) Q).card : ℝ)
            * (densityOn (polyadBlock (cutRefine κ W) Q) obs
                - densityOn (polyadBlock κ key) obs) ^ 2 := by
    have htitu := titu_finset
      (fun Q => ((polyadBlock (cutRefine κ W) Q).card : ℝ)
        * (densityOn (polyadBlock (cutRefine κ W) Q) obs
            - densityOn (polyadBlock κ key) obs))
      (fun Q => ((polyadBlock (cutRefine κ W) Q).card : ℝ))
      (resolvingKeys κ W key)
      (fun Q _ => Nat.cast_nonneg _)
      (fun Q _ h0 => by rw [h0, zero_mul])
    rw [hnum, ← hcard] at htitu
    have hleft : (((discAtom κ key (W key)).card : ℝ)
        * (densityOn (discAtom κ key (W key)) obs
            - densityOn (polyadBlock κ key) obs)) ^ 2
          / ((discAtom κ key (W key)).card : ℝ)
        = ((discAtom κ key (W key)).card : ℝ)
          * (densityOn (discAtom κ key (W key)) obs
              - densityOn (polyadBlock κ key) obs) ^ 2 := by
      field_simp
    have hright : ∀ Q ∈ resolvingKeys κ W key,
        (((polyadBlock (cutRefine κ W) Q).card : ℝ)
          * (densityOn (polyadBlock (cutRefine κ W) Q) obs
              - densityOn (polyadBlock κ key) obs)) ^ 2
          / ((polyadBlock (cutRefine κ W) Q).card : ℝ)
        = ((polyadBlock (cutRefine κ W) Q).card : ℝ)
          * (densityOn (polyadBlock (cutRefine κ W) Q) obs
              - densityOn (polyadBlock κ key) obs) ^ 2 := by
      intro Q _
      rcases eq_or_ne (((polyadBlock (cutRefine κ W) Q).card : ℝ)) 0 with hb | hb
      · rw [hb, zero_mul]
        norm_num
      · field_simp
    rw [hleft] at htitu
    exact le_trans htitu (le_of_eq (Finset.sum_congr rfl hright))
  -- Strict middle: `δ² < (deviation)²`.
  have hsq : δ ^ 2 < (densityOn (discAtom κ key (W key)) obs
      - densityOn (polyadBlock κ key) obs) ^ 2 := by
    have h1 := mul_self_lt_mul_self hδ.le hdev
    rw [abs_mul_abs_self] at h1
    calc δ ^ 2 = δ * δ := sq δ
      _ < _ := h1
      _ = _ ^ 2 := (sq _).symm
  -- Chain the estimates, extending the sum to the whole fiber at the end.
  have hchain1 : δ ^ 3 * ((polyadBlock κ key).card : ℝ)
      ≤ δ ^ 2 * ((discAtom κ key (W key)).card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlarge
      (le_of_lt (by positivity : (0 : ℝ) < δ ^ 2))
    calc δ ^ 3 * ((polyadBlock κ key).card : ℝ)
        = δ ^ 2 * (δ * ((polyadBlock κ key).card : ℝ)) := by ring
      _ ≤ δ ^ 2 * ((discAtom κ key (W key)).card : ℝ) := h
  have hchain2 : δ ^ 2 * ((discAtom κ key (W key)).card : ℝ)
      < ((discAtom κ key (W key)).card : ℝ)
        * (densityOn (discAtom κ key (W key)) obs
            - densityOn (polyadBlock κ key) obs) ^ 2 := by
    have h := mul_lt_mul_of_pos_left hsq hApos
    calc δ ^ 2 * ((discAtom κ key (W key)).card : ℝ)
        = ((discAtom κ key (W key)).card : ℝ) * δ ^ 2 := by ring
      _ < _ := h
  have hmono : ∑ Q ∈ resolvingKeys κ W key,
      ((polyadBlock (cutRefine κ W) Q).card : ℝ)
        * (densityOn (polyadBlock (cutRefine κ W) Q) obs
            - densityOn (polyadBlock κ key) obs) ^ 2
      ≤ ∑ Q ∈ Finset.univ.filter fun Q : Fin (j + 1) → Fin (cutBound j K) =>
          (fun i => cutRefineProj (Q i)) = key,
          ((polyadBlock (cutRefine κ W) Q).card : ℝ)
            * (densityOn (polyadBlock (cutRefine κ W) Q) obs
                - densityOn (polyadBlock κ key) obs) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (resolvingKeys_subset_fiber κ W key)
      fun Q _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  calc δ ^ 3 * ((polyadBlock κ key).card : ℝ)
      ≤ δ ^ 2 * ((discAtom κ key (W key)).card : ℝ) := hchain1
    _ < ((discAtom κ key (W key)).card : ℝ)
        * (densityOn (discAtom κ key (W key)) obs
            - densityOn (polyadBlock κ key) obs) ^ 2 := hchain2
    _ ≤ ∑ Q ∈ resolvingKeys κ W key, _ := hCS
    _ ≤ _ := hmono

/-! ### Tests and adversarial examples -/

section Tests

-- The projection and bit decoders invert the computable encoding on a tiny host.
example :
    cutRefineProj (cutRefine (fun _ : RSet 0 (Fin 1) => (0 : Fin 1))
      (fun _ _ => {⟨∅, rfl⟩}) ⟨∅, rfl⟩) = 0 := by decide

example :
    cutRefineBit (cutRefine (fun _ : RSet 0 (Fin 1) => (0 : Fin 1))
        (fun _ _ => {⟨∅, rfl⟩}) ⟨∅, rfl⟩) (fun _ => 0) 0 = 1 := by decide

example :
    cutRefineBit (cutRefine (fun _ : RSet 0 (Fin 1) => (0 : Fin 1))
        (fun _ _ => (∅ : Finset (RSet 0 (Fin 1)))) ⟨∅, rfl⟩) (fun _ => 0) 0 = 0 := by
  decide

-- The recurrence, by construction, at triadic parameters: K = 2 pair colors refine
-- into at most 2 · 2^24 colors in one simultaneous round.
example : cutBound 2 2 = 2 * 2 ^ 24 := by norm_num

-- The structural theorem, numerically, on the smallest host: at j = 0, K = 1 the
-- atom of the all-in family is the whole (one-tuple) block, and its cardinality is
-- recovered as the sum over resolving keys.
example :
    (discAtom (fun _ : RSet 0 (Fin 1) => (0 : Fin 1)) (fun _ => 0)
        ((fun _ _ => {⟨∅, rfl⟩}) (fun _ : Fin 1 => (0 : Fin 1)))).card
      = ∑ Q ∈ resolvingKeys (fun _ : RSet 0 (Fin 1) => (0 : Fin 1))
          (fun _ _ => {⟨∅, rfl⟩}) (fun _ => 0),
          (polyadBlock (cutRefine (fun _ : RSet 0 (Fin 1) => (0 : Fin 1))
            (fun _ _ => {⟨∅, rfl⟩})) Q).card := by decide

-- Statement-level instance of the union theorem at triadic types.
example (κ : RSet 2 (Fin 4) → Fin 2)
    (W : (Fin 3 → Fin 2) → Fin 3 → Finset (RSet 2 (Fin 4))) (key : Fin 3 → Fin 2) :
    discAtom κ key (W key)
      = (resolvingKeys κ W key).biUnion (polyadBlock (cutRefine κ W)) :=
  discAtom_eq_biUnion_cutRefine κ W key

-- Statement-level: energy never decreases under a simultaneous cut refinement.
example (κ : RSet 2 (Fin 4) → Fin 2)
    (W : (Fin 3 → Fin 2) → Fin 3 → Finset (RSet 2 (Fin 4)))
    (obs : (Fin 3 → Fin 4) → Prop) [DecidablePred obs] :
    polyadEnergyNum κ obs ≤ polyadEnergyNum (cutRefine κ W) obs :=
  polyadEnergyNum_le_cutRefine κ W obs

end Tests

end RegularityLemmata
