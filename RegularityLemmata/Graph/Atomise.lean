/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.BadMass
import RegularityLemmata.Partition.Equitable

/-!
# Simultaneous witness atomisation

For every bad ordered pair of parts, fix a nonuniformity witness. Each part `C`
receives at most `2k` cutting sets (`k = #P.parts`): the left witness of each pair
`(C, D)` and the right witness of each pair `(D, C)`. Refining **each cell by its own
cuts** (`Finpartition.bind` of per-cell `Finpartition.atomise`) yields a refinement in
which every chosen witness side is a part union, with the part count multiplying by at
most `2^(2k)` — total bound `k · 2^(2k)` (`witnessRefinement_parts_card_le`), far
sharper than a global atomisation's `2^(k + 2k²)`.

`k · 2^(2k) = k · 4^k` is exactly mathlib's one-step growth `stepBound`
(`Mathlib.Combinatorics.SimpleGraph.Regularity.Bound`); the gluing of per-cell witness
refinements follows the architecture of
`Mathlib.Combinatorics.SimpleGraph.Regularity.Increment`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

open Classical in
/-- The cutting sets landing in the cell `C`: left witnesses of bad pairs `(C, D)` and
right witnesses of bad pairs `(D, C)`, over all partners `D` (empty set for good
pairs). Every cut is a subset of `C`. -/
noncomputable def witnessCuts (P : Finpartition s) (C : Finset α) : Finset (Finset α) :=
  (P.parts.image fun D =>
      if h : IsBadPair R ε C D then (NonuniformWitness.ofNotUniform h.2).left else ∅)
    ∪ (P.parts.image fun D =>
      if h : IsBadPair R ε D C then (NonuniformWitness.ofNotUniform h.2).right else ∅)

theorem witnessCuts_card_le (P : Finpartition s) (C : Finset α) :
    (witnessCuts R ε P C).card ≤ 2 * P.parts.card := by
  classical
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := P.parts) (f := fun D =>
    if h : IsBadPair R ε C D then (NonuniformWitness.ofNotUniform h.2).left else ∅)
  have h2 := Finset.card_image_le (s := P.parts) (f := fun D =>
    if h : IsBadPair R ε D C then (NonuniformWitness.ofNotUniform h.2).right else ∅)
  omega

theorem witnessCuts_subset (P : Finpartition s) {C : Finset α}
    {b : Finset α} (hb : b ∈ witnessCuts R ε P C) : b ⊆ C := by
  rw [witnessCuts, Finset.mem_union] at hb
  rcases hb with hb | hb <;> rw [Finset.mem_image] at hb <;> obtain ⟨D, _, rfl⟩ := hb
  · split_ifs with h
    · exact (NonuniformWitness.ofNotUniform h.2).left_subset
    · exact Finset.empty_subset _
  · split_ifs with h
    · exact (NonuniformWitness.ofNotUniform h.2).right_subset
    · exact Finset.empty_subset _

/-- The simultaneous witness refinement: each cell atomised by its own cuts. -/
noncomputable def witnessRefinement (P : Finpartition s) : Finpartition s :=
  P.bind fun C _ => Finpartition.atomise C (witnessCuts R ε P C)

theorem witnessRefinement_le (P : Finpartition s) : witnessRefinement R ε P ≤ P := by
  intro b hb
  rw [witnessRefinement, Finpartition.mem_bind] at hb
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, (Finpartition.atomise C (witnessCuts R ε P C)).le hb⟩

/-- **Part-count bound `k · 2^(2k)`**: each cell may receive one left and one right
witness for each partner, hence at most `2k` cuts and `2^(2k)` atoms. -/
theorem witnessRefinement_parts_card_le (P : Finpartition s) :
    (witnessRefinement R ε P).parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) := by
  rw [witnessRefinement, Finpartition.card_bind]
  calc ∑ C ∈ P.parts.attach,
        (Finpartition.atomise C.1 (witnessCuts R ε P C.1)).parts.card
      ≤ ∑ _C ∈ P.parts.attach, 2 ^ (2 * P.parts.card) := by
        refine Finset.sum_le_sum fun C _ => ?_
        refine Finpartition.card_atomise_le.trans ?_
        exact Nat.pow_le_pow_right (by norm_num) (witnessCuts_card_le R ε P C.1)
    _ = P.parts.card * 2 ^ (2 * P.parts.card) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]

/-- Any member of a cell's cut family is a part union of the per-cell atomisation
refinement. -/
theorem isPartUnion_bind_atomise {P : Finpartition s} {F : ∀ C ∈ P.parts, Finset (Finset α)}
    {C b : Finset α} (hC : C ∈ P.parts) (hbF : b ∈ F C hC) (hbC : b ⊆ C) :
    IsPartUnion (P.bind fun C hC => Finpartition.atomise C (F C hC)) b := by
  set Q := P.bind fun C hC => Finpartition.atomise C (F C hC) with hQ
  show (Q.parts.filter (· ⊆ b)).biUnion id = b
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨u, huf, hxu⟩ := hx
    exact (Finset.mem_filter.mp huf).2 hxu
  · intro x hxb
    have hcov := Finpartition.biUnion_filter_atomise (s := C) hbF hbC
    rw [← hcov, Finset.mem_biUnion] at hxb
    obtain ⟨u, huf, hxu⟩ := hxb
    rw [Finset.mem_filter] at huf
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_filter.mpr ⟨?_, huf.2.1⟩, hxu⟩
    rw [hQ, Finpartition.mem_bind]
    exact ⟨C, hC, huf.1⟩

/-- **Witness resolution.** Every bad pair has a witness whose sides are part unions of
the witness refinement. -/
theorem witnessRefinement_resolves (P : Finpartition s) :
    ∀ C ∈ P.parts, ∀ D ∈ P.parts, IsBadPair R ε C D →
      ∃ w : NonuniformWitness R C D ε,
        IsPartUnion (witnessRefinement R ε P) w.left ∧
        IsPartUnion (witnessRefinement R ε P) w.right := by
  classical
  intro C hC D hD hbad
  refine ⟨NonuniformWitness.ofNotUniform hbad.2, ?_, ?_⟩
  · refine isPartUnion_bind_atomise hC ?_
      (NonuniformWitness.ofNotUniform hbad.2).left_subset
    rw [witnessCuts, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨D, hD, dif_pos hbad⟩
  · refine isPartUnion_bind_atomise hD ?_
      (NonuniformWitness.ofNotUniform hbad.2).right_subset
    rw [witnessCuts, Finset.mem_union]
    right
    rw [Finset.mem_image]
    exact ⟨C, hC, dif_pos hbad⟩

/-! ### Tests and adversarial examples -/

-- With no bad pairs, all cuts are ∅ or absent and the refinement still refines:
-- sanity-check `witnessRefinement_le` and the cardinality bound on a concrete host.
example :
    (witnessRefinement (fun a b : Fin 3 => a < b) (1 : ℝ)
        (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3)))).parts.card
      ≤ 3 * 2 ^ 6 :=
  witnessRefinement_parts_card_le _ _ _

example :
    witnessRefinement (fun a b : Fin 3 => a < b) (1 : ℝ)
        (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      ≤ ⊤ :=
  witnessRefinement_le _ _ _

end RegularityLemmata
