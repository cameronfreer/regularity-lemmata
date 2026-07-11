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

/-- **Witness atoms are unions of refined blocks**: the disc atom of `W key` at
`key` is exactly the union of the refined blocks whose keys project to `key` and
whose cut bits at `(key, ·)` are all set. -/
theorem discAtom_eq_biUnion_cutRefine (κ : RSet j α → Fin K)
    (W : (Fin (j + 1) → Fin K) → Fin (j + 1) → Finset (RSet j α))
    (key : Fin (j + 1) → Fin K) :
    discAtom κ key (W key)
      = (Finset.univ.filter fun Q : Fin (j + 1) → Fin (cutBound j K) =>
          (∀ i, cutRefineProj (Q i) = key i)
            ∧ ∀ i, cutRefineBit (Q i) key i = 1).biUnion
          (polyadBlock (cutRefine κ W)) := by
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

-- Statement-level: energy never decreases under a simultaneous cut refinement.
example (κ : RSet 2 (Fin 4) → Fin 2)
    (W : (Fin 3 → Fin 2) → Fin 3 → Finset (RSet 2 (Fin 4)))
    (obs : (Fin 3 → Fin 4) → Prop) [DecidablePred obs] :
    polyadEnergyNum κ obs ≤ polyadEnergyNum (cutRefine κ W) obs :=
  polyadEnergyNum_le_cutRefine κ W obs

end Tests

end RegularityLemmata
