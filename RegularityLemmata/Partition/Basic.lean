import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Part-union and counting lemmas over `Finpartition`

Plumbing for partitions of a finite ground set `s : Finset α`, built directly on
mathlib's `Finpartition` (this library never introduces a private partition type).

**Refinement direction.** In the `Finpartition` order, `Q ≤ P` means `Q` is *finer*
than `P`: every part of `Q` is contained in some part of `P`. (See the sanity example
below.)

A finset is a *part union* of `P` when it is a union of `P`-parts. Part unions behave
like clopen sets: each part is inside or disjoint from them, and they are closed under
relative complement. `sum_over_parents` reindexes sums over a finer partition by the
containing coarser parts.

`predicatePartition p s` is the at-most-two-cell partition of `s` by a decidable
predicate, built on mathlib's `Finpartition.atomise` (not on relation-fiber machinery).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

-- Sanity check for the refinement direction: `Q ≤ P` = `Q` finer.
example {P Q : Finpartition s} (hQP : Q ≤ P) {B : Finset α} (hB : B ∈ Q.parts) :
    ∃ A ∈ P.parts, B ⊆ A := hQP hB

/-! ### Cardinality plumbing -/

/-- Real-cast form of `Finpartition.sum_card_parts`. -/
theorem sum_card_parts_cast (P : Finpartition s) :
    (∑ A ∈ P.parts, (A.card : ℝ)) = (s.card : ℝ) := by
  rw [← Nat.cast_sum, P.sum_card_parts]

theorem parts_top_card_le_one : (⊤ : Finpartition s).parts.card ≤ 1 := by
  calc (⊤ : Finpartition s).parts.card
      ≤ ({s} : Finset (Finset α)).card :=
        Finset.card_le_card (Finpartition.parts_top_subset _)
    _ = 1 := Finset.card_singleton _

/-- The common refinement has at most multiplicatively many parts. -/
theorem card_parts_inf_le (P Q : Finpartition s) :
    (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card := by
  rw [Finpartition.parts_inf]
  calc (((P.parts ×ˢ Q.parts).image fun bc => bc.1 ⊓ bc.2).erase ⊥).card
      ≤ ((P.parts ×ˢ Q.parts).image fun bc => bc.1 ⊓ bc.2).card := Finset.card_erase_le
    _ ≤ (P.parts ×ˢ Q.parts).card := Finset.card_image_le
    _ = P.parts.card * Q.parts.card := Finset.card_product _ _

/-! ### Part unions -/

/-- `S` is a union of parts of `P`. -/
def IsPartUnion (P : Finpartition s) (S : Finset α) : Prop :=
  (P.parts.filter (· ⊆ S)).biUnion id = S

instance {P : Finpartition s} {S : Finset α} : Decidable (IsPartUnion P S) :=
  inferInstanceAs (Decidable (_ = _))

/-- A part of `P` is inside or disjoint from any part union. -/
theorem part_subset_or_disjoint {P : Finpartition s} {S : Finset α} (hS : IsPartUnion P S)
    {E : Finset α} (hE : E ∈ P.parts) : E ⊆ S ∨ Disjoint E S := by
  rw [or_iff_not_imp_right, Finset.not_disjoint_iff]
  rintro ⟨x, hxE, hxS⟩
  have hSeq : (P.parts.filter (· ⊆ S)).biUnion id = S := hS
  rw [← hSeq, Finset.mem_biUnion] at hxS
  obtain ⟨E', hE'f, hxE'⟩ := hxS
  rw [Finset.mem_filter] at hE'f
  rw [P.eq_of_mem_parts hE hE'f.1 hxE hxE']
  exact hE'f.2

/-- A part union is contained in the ground set. -/
theorem IsPartUnion.subset_ground {P : Finpartition s} {S : Finset α}
    (hS : IsPartUnion P S) : S ⊆ s := by
  rw [← hS]
  exact Finset.biUnion_subset.mpr fun E hE => P.le (Finset.mem_filter.mp hE).1

/-- The ground set is a part union. -/
theorem isPartUnion_ground (P : Finpartition s) : IsPartUnion P s := by
  have hfil : P.parts.filter (· ⊆ s) = P.parts :=
    Finset.filter_true_of_mem fun E hE => P.le hE
  rw [IsPartUnion, hfil]
  exact P.biUnion_parts

/-- The relative complement of a part union inside another is a part union. -/
theorem isPartUnion_sdiff {P : Finpartition s} {C C' : Finset α}
    (hC : IsPartUnion P C) (hC' : IsPartUnion P C') (_hsub : C' ⊆ C) :
    IsPartUnion P (C \ C') := by
  have hCeq : (P.parts.filter (· ⊆ C)).biUnion id = C := hC
  show (P.parts.filter (· ⊆ C \ C')).biUnion id = C \ C'
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨E, hEf, hxE⟩ := hx
    rw [Finset.mem_filter] at hEf
    exact hEf.2 hxE
  · intro x hxCC'
    have hxC : x ∈ C := (Finset.mem_sdiff.mp hxCC').1
    have hxC' : x ∉ C' := (Finset.mem_sdiff.mp hxCC').2
    rw [← hCeq, Finset.mem_biUnion] at hxC
    obtain ⟨E, hEf, hxE⟩ := hxC
    rw [Finset.mem_filter] at hEf
    rw [Finset.mem_biUnion]
    refine ⟨E, ?_, hxE⟩
    rw [Finset.mem_filter]
    refine ⟨hEf.1, Finset.subset_sdiff.mpr ⟨hEf.2, ?_⟩⟩
    rcases part_subset_or_disjoint hC' hEf.1 with h | h
    · exact absurd (h hxE) hxC'
    · exact h

/-- Complement in the ground set of a part union is a part union. -/
theorem isPartUnion_compl {P : Finpartition s} {S : Finset α} (hS : IsPartUnion P S) :
    IsPartUnion P (s \ S) :=
  isPartUnion_sdiff (isPartUnion_ground P) hS hS.subset_ground

/-- The parts inside `C` split as those inside a part union `C' ⊆ C` and those inside
`C \ C'`. -/
theorem filter_subset_eq_union {P : Finpartition s} {C C' : Finset α}
    (hC' : IsPartUnion P C') (hsub : C' ⊆ C) :
    P.parts.filter (· ⊆ C) = P.parts.filter (· ⊆ C') ∪ P.parts.filter (· ⊆ C \ C') := by
  ext E
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hE, hEC⟩
    rcases part_subset_or_disjoint hC' hE with h | h
    · exact Or.inl ⟨hE, h⟩
    · exact Or.inr ⟨hE, Finset.subset_sdiff.mpr ⟨hEC, h⟩⟩
  · rintro (⟨hE, h⟩ | ⟨hE, h⟩)
    · exact ⟨hE, h.trans hsub⟩
    · exact ⟨hE, h.trans Finset.sdiff_subset⟩

/-- The two halves of the split are disjoint. -/
theorem filter_subset_disjoint {P : Finpartition s} {C C' : Finset α} :
    Disjoint (P.parts.filter (· ⊆ C')) (P.parts.filter (· ⊆ C \ C')) := by
  rw [Finset.disjoint_left]
  rintro E hE1 hE2
  rw [Finset.mem_filter] at hE1 hE2
  obtain ⟨_, hdisjEC'⟩ := Finset.subset_sdiff.mp hE2.2
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hE1.1
  exact absurd (hE1.2 hx) (Finset.disjoint_left.mp hdisjEC' hx)

/-! ### Refinement fibers -/

/-- When `Q` refines `P`, the `Q`-parts inside a `P`-part `C` cover `C`. -/
theorem biUnion_filter_subset_eq {P Q : Finpartition s} (hQ : Q ≤ P)
    {C : Finset α} (hC : C ∈ P.parts) :
    (Q.parts.filter (· ⊆ C)).biUnion id = C := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨Q', hQ'f, hxQ'⟩ := hx
    rw [Finset.mem_filter] at hQ'f
    exact hQ'f.2 hxQ'
  · intro x hxC
    obtain ⟨Q', hQ'mem, hxQ'⟩ := Q.exists_mem (P.le hC hxC)
    obtain ⟨C'', hC''mem, hQ'sub⟩ := hQ hQ'mem
    have hxC'' : x ∈ C'' := hQ'sub hxQ'
    have hCC : C = C'' := P.eq_of_mem_parts hC hC''mem hxC hxC''
    rw [Finset.mem_biUnion]
    exact ⟨Q', by rw [Finset.mem_filter]; exact ⟨hQ'mem, by rw [hCC]; exact hQ'sub⟩, hxQ'⟩

/-- Each `P`-part is a part union of any refinement. -/
theorem isPartUnion_of_mem_of_le {P Q : Finpartition s} (hQ : Q ≤ P) {C : Finset α}
    (hC : C ∈ P.parts) : IsPartUnion Q C :=
  biUnion_filter_subset_eq hQ hC

/-- The `P`-parts' contained-`Q`-part families biUnion to all of `Q.parts`. -/
theorem parts_biUnion_filter_subset {P Q : Finpartition s} (hQ : Q ≤ P) :
    P.parts.biUnion (fun C => Q.parts.filter (· ⊆ C)) = Q.parts := by
  ext Q'
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨C, _, hQ'mem, _⟩; exact hQ'mem
  · intro hQ'mem
    obtain ⟨C, hCmem, hsub⟩ := hQ hQ'mem
    exact ⟨C, hCmem, hQ'mem, hsub⟩

/-- Reindexing: summing a function of `Q`-parts over the `P`-part fibers recovers the
total (each `Q`-part lies in a unique `P`-part). -/
theorem sum_over_parents {P Q : Finpartition s} (hQ : Q ≤ P) (g : Finset α → ℝ) :
    ∑ C ∈ P.parts, ∑ C' ∈ Q.parts.filter (· ⊆ C), g C' = ∑ C' ∈ Q.parts, g C' := by
  have hfib : (↑P.parts : Set (Finset α)).PairwiseDisjoint
      (fun C => Q.parts.filter (· ⊆ C)) := by
    intro C₁ hC₁ C₂ hC₂ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro Q' ⟨hQ'mem, hsub₁⟩ ⟨-, hsub₂⟩
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hQ'mem
    exact hne (P.eq_of_mem_parts (Finset.mem_coe.mp hC₁) (Finset.mem_coe.mp hC₂)
      (hsub₁ hx) (hsub₂ hx))
  conv_rhs => rw [← parts_biUnion_filter_subset hQ]
  rw [Finset.sum_biUnion hfib]

/-! ### Predicate partitions -/

/-- The at-most-two-cell partition of `s` by a decidable predicate, via
`Finpartition.atomise` with the one-set family `{s.filter p}`. (Deliberately NOT built
on relation-fiber machinery.) -/
def predicatePartition (p : α → Prop) [DecidablePred p] (s : Finset α) : Finpartition s :=
  Finpartition.atomise s {s.filter p}

/-- The predicate is constant on each cell of `predicatePartition`. -/
theorem predicatePartition_constant {p : α → Prop} [DecidablePred p] {C : Finset α}
    (hC : C ∈ (predicatePartition p s).parts) :
    (∀ a ∈ C, p a) ∨ (∀ a ∈ C, ¬ p a) := by
  obtain ⟨-, Q, -, rfl⟩ := Finpartition.mem_atomise.mp hC
  by_cases hQ : s.filter p ∈ Q
  · left
    intro a ha
    rw [Finset.mem_filter] at ha
    have := (ha.2 (s.filter p) (Finset.mem_singleton_self _)).mp hQ
    exact (Finset.mem_filter.mp this).2
  · right
    intro a ha hpa
    rw [Finset.mem_filter] at ha
    exact hQ ((ha.2 (s.filter p) (Finset.mem_singleton_self _)).mpr
      (Finset.mem_filter.mpr ⟨ha.1, hpa⟩))

theorem predicatePartition_parts_card_le (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (predicatePartition p s).parts.card ≤ 2 := by
  simpa [predicatePartition] using
    Finpartition.card_atomise_le (s := s) (F := {s.filter p})

/-- Exact membership: the cells are the nonempty sets among `s.filter p` and
`s.filter (¬ p ·)`. -/
theorem mem_predicatePartition {p : α → Prop} [DecidablePred p] {C : Finset α} :
    C ∈ (predicatePartition p s).parts ↔
      C.Nonempty ∧ (C = s.filter p ∨ C = s.filter fun a => ¬ p a) := by
  rw [predicatePartition, Finpartition.mem_atomise]
  constructor
  · rintro ⟨hne, Q, hQ, rfl⟩
    refine ⟨hne, ?_⟩
    rcases Finset.subset_singleton_iff.mp hQ with rfl | rfl
    · right
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, false_iff,
        forall_eq]
      tauto
    · left
      ext a
      simp [Finset.mem_filter]
  · rintro ⟨hne, rfl | rfl⟩
    · refine ⟨hne, {s.filter p}, subset_rfl, ?_⟩
      ext a
      simp [Finset.mem_filter]
    · refine ⟨hne, ∅, Finset.empty_subset _, ?_⟩
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, false_iff,
        forall_eq]
      tauto

/-- Exact parts formula for the predicate partition. -/
theorem predicatePartition_parts (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (predicatePartition p s).parts
      = ({s.filter p, s.filter fun a => ¬ p a} : Finset (Finset α)).filter
          Finset.Nonempty := by
  ext C
  rw [mem_predicatePartition, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ### Tests and adversarial examples -/

-- Tiny concrete partitions of {0,1,2}: singletons (⊥) and the indiscrete partition (⊤).
example : ((⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts.card) = 3 := by decide
example : ((⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts.card) = 1 := by decide

-- The common refinement bound, computed: |⊤ ⊓ ⊥| = 3 ≤ 1 · 3.
example : ((⊤ ⊓ ⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts.card) = 3 := by decide

-- Part unions under ⊥ (every subset) and ⊤ (only ∅ and s).
example : IsPartUnion (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))) {0, 1} := by decide
example : IsPartUnion (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) ∅ := by decide
example : ¬ IsPartUnion (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) {0, 1} := by decide

-- Degenerate ground set: the empty partition.
example : IsPartUnion (⊥ : Finpartition (∅ : Finset (Fin 3))) ∅ := by decide

-- Predicate partition of {0,1,2} by `= 0`: exactly two cells.
example : (predicatePartition (fun a : Fin 3 => a = 0) {0, 1, 2}).parts.card = 2 := by
  decide

-- Constant predicate: one cell.
example : (predicatePartition (fun _ : Fin 3 => True) {0, 1, 2}).parts.card = 1 := by
  decide

end RegularityLemmata
