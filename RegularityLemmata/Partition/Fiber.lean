/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.Basic

/-!
# Fiber-type partitions

Elementary finite-relation compression: for a relation `R : α → β → Prop`, partition
a finite set `C` by the *fiber type* of its elements on a target set `D`, where
`fiberType R D a = {d ∈ D | R a d}` — the row of `a` in the `C × D` incidence matrix.
Elements with equal rows form the cells of `fiberPartition R C D` (a thin wrap of
mathlib's `Finpartition.ofSetSetoid`); the cell count is exactly the number of
distinct fiber types (`card_parts_fiberPartition`) and is at most `2 ^ |D|`
(`fiberTypeCount_le_two_pow`). Larger targets induce finer partitions
(`fiberPartition_le_of_subset`).

The payoff is *constancy*: a cell of the row partition and a cell of the column
partition see a constant relation (`fiberPartition_pair_constant`). For a homogeneous
relation the same follows on the common refinement of the forward and backward fiber
partitions (`inf_fiberPartition_constant`), and a single partition suffices when the
relation is symmetric (`fiberPartition_pair_constant_of_symm`). Constancy transfers
down any refinement (`pair_constant_of_le`, `pred_constant_of_le`); cell counts under
repeated common refinement are controlled by `card_parts_inf'_le`
(`Partition/Basic.lean`).

Constancy statements use the house disjunction form (`(∀ …, R a d) ∨ (∀ …, ¬R a d)`),
not a `Bool` encoding; parts of a `Finpartition` are nonempty, so no `Nonempty`
hypotheses appear.
-/

namespace RegularityLemmata

open Finset

variable {α β : Type*}

/-! ### Fiber types -/

section FiberType

variable (R : α → β → Prop) [DecidableRel R]

/-- The fiber type of `a` on `D`: the elements of `D` that `a` is `R`-related to. -/
def fiberType (D : Finset β) (a : α) : Finset β :=
  D.filter (R a)

@[simp] theorem mem_fiberType {D : Finset β} {a : α} {d : β} :
    d ∈ fiberType R D a ↔ d ∈ D ∧ R a d := by
  simp [fiberType]

theorem fiberType_subset (D : Finset β) (a : α) : fiberType R D a ⊆ D :=
  filter_subset _ _

/-- Equal fiber types on `D` = agreement of `R` against every element of `D`. -/
theorem fiberType_eq_iff {D : Finset β} {a₁ a₂ : α} :
    fiberType R D a₁ = fiberType R D a₂ ↔ ∀ d ∈ D, (R a₁ d ↔ R a₂ d) := by
  simp only [Finset.ext_iff, mem_fiberType]
  constructor
  · intro h d hd
    have := h d
    simp only [hd, true_and] at this
    exact this
  · intro h d
    constructor
    · rintro ⟨hd, hr⟩; exact ⟨hd, (h d hd).mp hr⟩
    · rintro ⟨hd, hr⟩; exact ⟨hd, (h d hd).mpr hr⟩

theorem fiberType_mono {D₁ D₂ : Finset β} (h : D₁ ⊆ D₂) (a : α) :
    fiberType R D₁ a ⊆ fiberType R D₂ a := by
  intro d hd
  rw [mem_fiberType] at hd ⊢
  exact ⟨h hd.1, hd.2⟩

end FiberType

/-! ### The fiber partition -/

section FiberPartition

variable [DecidableEq α] (R : α → β → Prop) [DecidableRel R]

/-- The setoid relating elements with the same fiber type on `D`. -/
def fiberSetoid (D : Finset β) : Setoid α where
  r a₁ a₂ := fiberType R D a₁ = fiberType R D a₂
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance fiberSetoid_decidableRel [DecidableEq β] (D : Finset β) :
    DecidableRel (fiberSetoid R D).r :=
  fun a₁ a₂ => inferInstanceAs (Decidable (fiberType R D a₁ = fiberType R D a₂))

variable [DecidableEq β]

/-- The partition of `C` by fiber type on `D` (mathlib's `Finpartition.ofSetSetoid`
at the fiber setoid). -/
def fiberPartition (C : Finset α) (D : Finset β) : Finpartition C :=
  Finpartition.ofSetSetoid (fiberSetoid R D) C

/-- The parts, explicitly: one filter per represented fiber type. -/
theorem fiberPartition_parts (C : Finset α) (D : Finset β) :
    (fiberPartition R C D).parts
      = C.image fun a => C.filter fun b => fiberType R D a = fiberType R D b := by
  simp [fiberPartition, Finpartition.ofSetSetoid_parts, fiberSetoid]

/-- Members of one part share their fiber type. -/
theorem fiberType_eq_of_mem_part {C : Finset α} {D : Finset β} {t : Finset α}
    (ht : t ∈ (fiberPartition R C D).parts) {a b : α} (ha : a ∈ t) (hb : b ∈ t) :
    fiberType R D a = fiberType R D b := by
  rw [fiberPartition_parts] at ht
  rw [Finset.mem_image] at ht
  obtain ⟨c, _, rfl⟩ := ht
  rw [Finset.mem_filter] at ha hb
  exact ha.2.symm.trans hb.2

/-- The number of distinct fiber types of elements of `C` on `D`. -/
def fiberTypeCount (C : Finset α) (D : Finset β) : ℕ :=
  (C.image (fiberType R D)).card

/-- Cells of the fiber partition biject with the represented fiber types. -/
theorem card_parts_fiberPartition (C : Finset α) (D : Finset β) :
    (fiberPartition R C D).parts.card = fiberTypeCount R C D := by
  rw [fiberPartition_parts, fiberTypeCount]
  set fT := fiberType R D with hfT
  have hcomp : Set.EqOn (fun a => C.filter fun b => fT a = fT b)
      ((fun F => C.filter fun b => fT b = F) ∘ fT) ↑C := by
    intro a _
    simp only [Function.comp]
    exact Finset.filter_congr fun b _ => by rw [eq_comm]
  rw [Finset.image_congr hcomp, ← Finset.image_image]
  refine Finset.card_image_of_injOn fun F₁ hF₁ F₂ hF₂ heq => ?_
  rw [Finset.coe_image, Set.mem_image] at hF₁ hF₂
  obtain ⟨a₁, ha₁, rfl⟩ := hF₁
  obtain ⟨a₂, ha₂, rfl⟩ := hF₂
  have h1 : a₁ ∈ C.filter fun b => fT b = fT a₁ := by
    rw [Finset.mem_filter]
    exact ⟨ha₁, rfl⟩
  rw [heq, Finset.mem_filter] at h1
  exact h1.2

omit [DecidableEq α] in
/-- At most `2 ^ |D|` fiber types: fiber types are subsets of `D`. -/
theorem fiberTypeCount_le_two_pow (C : Finset α) (D : Finset β) :
    fiberTypeCount R C D ≤ 2 ^ D.card := by
  rw [fiberTypeCount, ← Finset.card_powerset]
  refine Finset.card_le_card fun F hF => ?_
  rw [Finset.mem_image] at hF
  obtain ⟨a, _, rfl⟩ := hF
  rw [Finset.mem_powerset]
  exact fiberType_subset R D a

/-- Larger targets distinguish more, so they induce finer partitions
(`P ≤ Q` = `P` finer). -/
theorem fiberPartition_le_of_subset {C : Finset α} {D₁ D₂ : Finset β} (h : D₁ ⊆ D₂) :
    fiberPartition R C D₂ ≤ fiberPartition R C D₁ := by
  intro t ht
  rw [fiberPartition_parts, Finset.mem_image] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  refine ⟨C.filter fun b => fiberType R D₁ a = fiberType R D₁ b, ?_, ?_⟩
  · rw [fiberPartition_parts]
    exact Finset.mem_image_of_mem _ ha
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨hb.1, ?_⟩
    rw [fiberType_eq_iff] at hb ⊢
    exact fun d hd => hb.2 d (h hd)

end FiberPartition

/-! ### Constancy on pairs of cells -/

section Constancy

variable [DecidableEq α] [DecidableEq β]

/-- **Pairwise constancy, heterogeneous base form.** A cell of the row partition of
`s` (fiber types on `t`) and a cell of the column partition of `t` (fiber types on
`s`) see a constant relation. -/
theorem fiberPartition_pair_constant (R : α → β → Prop) [DecidableRel R]
    {s : Finset α} {t : Finset β} {C : Finset α} {D : Finset β}
    (hC : C ∈ (fiberPartition R s t).parts)
    (hD : D ∈ (fiberPartition (fun b a => R a b) t s).parts) :
    (∀ a ∈ C, ∀ d ∈ D, R a d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬R a d) := by
  obtain ⟨a₀, ha₀⟩ := (fiberPartition R s t).nonempty_of_mem_parts hC
  obtain ⟨d₀, hd₀⟩ := (fiberPartition (fun b a => R a b) t s).nonempty_of_mem_parts hD
  have hCs : C ⊆ s := (fiberPartition R s t).le hC
  have hDt : D ⊆ t := (fiberPartition (fun b a => R a b) t s).le hD
  have hfwd : ∀ a ∈ C, ∀ x ∈ t, (R a x ↔ R a₀ x) := fun a ha x hx =>
    (fiberType_eq_iff R).mp (fiberType_eq_of_mem_part R hC ha ha₀) x hx
  have hbwd : ∀ d ∈ D, ∀ x ∈ s, (R x d ↔ R x d₀) := fun d hd x hx =>
    (fiberType_eq_iff _).mp (fiberType_eq_of_mem_part (fun b a => R a b) hD hd hd₀) x hx
  have hchain : ∀ a ∈ C, ∀ d ∈ D, (R a d ↔ R a₀ d₀) := fun a ha d hd =>
    (hfwd a ha d (hDt hd)).trans (hbwd d hd a₀ (hCs ha₀))
  by_cases h₀ : R a₀ d₀
  · exact Or.inl fun a ha d hd => (hchain a ha d hd).mpr h₀
  · exact Or.inr fun a ha d hd hR => h₀ ((hchain a ha d hd).mp hR)

/-- Homogeneous corollary: on the common refinement of the forward and backward
fiber partitions of `s`, the relation is constant on every ordered pair of cells. -/
theorem inf_fiberPartition_constant (R : α → α → Prop) [DecidableRel R]
    {s : Finset α} {C D : Finset α}
    (hC : C ∈ (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).parts)
    (hD : D ∈ (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).parts) :
    (∀ a ∈ C, ∀ d ∈ D, R a d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬R a d) := by
  obtain ⟨A, hA, hCA⟩ :=
    (inf_le_left : fiberPartition R s s ⊓ _ ≤ fiberPartition R s s) hC
  obtain ⟨B, hB, hDB⟩ :=
    (inf_le_right : _ ⊓ fiberPartition (fun a b => R b a) s s ≤ _) hD
  rcases fiberPartition_pair_constant R hA hB with h | h
  · exact Or.inl fun a ha d hd => h a (hCA ha) d (hDB hd)
  · exact Or.inr fun a ha d hd => h a (hCA ha) d (hDB hd)

/-- For a symmetric relation the backward fiber partition coincides with the
forward one. -/
theorem fiberPartition_symm_eq {R : α → α → Prop} [DecidableRel R]
    (hR : ∀ a b, R a b → R b a) (C D : Finset α) :
    fiberPartition (fun a b => R b a) C D = fiberPartition R C D := by
  have hfT : ∀ a, fiberType (fun a b => R b a) D a = fiberType R D a := fun a =>
    Finset.filter_congr fun d _ => ⟨fun h => hR _ _ h, fun h => hR _ _ h⟩
  refine Finpartition.ext ?_
  rw [fiberPartition_parts, fiberPartition_parts]
  refine Finset.image_congr fun a _ => ?_
  refine Finset.filter_congr fun b _ => ?_
  rw [hfT, hfT]

/-- **Symmetric corollary**: for a symmetric relation, one fiber partition suffices
for pairwise constancy. -/
theorem fiberPartition_pair_constant_of_symm {R : α → α → Prop} [DecidableRel R]
    (hR : ∀ a b, R a b → R b a) {s : Finset α} {C D : Finset α}
    (hC : C ∈ (fiberPartition R s s).parts) (hD : D ∈ (fiberPartition R s s).parts) :
    (∀ a ∈ C, ∀ d ∈ D, R a d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬R a d) := by
  refine fiberPartition_pair_constant R hC ?_
  rw [fiberPartition_symm_eq hR]
  exact hD

/-- Pairwise constancy transfers down refinement: constant on `Q`-cell pairs and
`P ≤ Q` gives constancy on `P`-cell pairs. -/
theorem pair_constant_of_le {s : Finset α} {P Q : Finpartition s} (hle : P ≤ Q)
    (R : α → α → Prop) {C D : Finset α} (hC : C ∈ P.parts) (hD : D ∈ P.parts)
    (hconst : ∀ C' ∈ Q.parts, ∀ D' ∈ Q.parts,
      (∀ a ∈ C', ∀ d ∈ D', R a d) ∨ (∀ a ∈ C', ∀ d ∈ D', ¬R a d)) :
    (∀ a ∈ C, ∀ d ∈ D, R a d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬R a d) := by
  obtain ⟨C', hC'mem, hCC'⟩ := hle hC
  obtain ⟨D', hD'mem, hDD'⟩ := hle hD
  rcases hconst C' hC'mem D' hD'mem with h | h
  · exact Or.inl fun a ha d hd => h a (hCC' ha) d (hDD' hd)
  · exact Or.inr fun a ha d hd => h a (hCC' ha) d (hDD' hd)

/-- Predicate constancy transfers down refinement. -/
theorem pred_constant_of_le {s : Finset α} {P Q : Finpartition s} (hle : P ≤ Q)
    (p : α → Prop) {C : Finset α} (hC : C ∈ P.parts)
    (hconst : ∀ C' ∈ Q.parts, (∀ a ∈ C', p a) ∨ (∀ a ∈ C', ¬p a)) :
    (∀ a ∈ C, p a) ∨ (∀ a ∈ C, ¬p a) := by
  obtain ⟨C', hC'mem, hCC'⟩ := hle hC
  rcases hconst C' hC'mem with h | h
  · exact Or.inl fun a ha => h a (hCC' ha)
  · exact Or.inr fun a ha => h a (hCC' ha)

end Constancy

/-! ### Tests and adversarial examples -/

section Tests

-- Divisibility on Fin 4 (as naturals): fiber types on {1, 2} distinguish 1, 2 from 3.
-- fiberType (· ∣ ·) {1,2} 1 = {1,2}, at 2 = {2}, at 3 = ∅, at 0 = ∅ — three types.
example :
    fiberTypeCount (fun a b : Fin 4 => (a : ℕ) ∣ (b : ℕ))
      (Finset.univ : Finset (Fin 4)) {1, 2} = 3 := by decide

-- The partition cell count agrees (via the general theorem, then compute).
example :
    (fiberPartition (fun a b : Fin 4 => (a : ℕ) ∣ (b : ℕ))
      (Finset.univ : Finset (Fin 4)) {1, 2}).parts.card = 3 := by
  rw [card_parts_fiberPartition]
  decide

-- Heterogeneous relation: elements of Fin 2 classified against Fin 3 by a coset
-- condition; both rows are distinct, so two cells.
example :
    fiberTypeCount (fun a : Fin 2 => fun b : Fin 3 => (a : ℕ) + (b : ℕ) = 2)
      (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 3)) = 2 := by decide

-- The 2^|D| bound is tight here: 3 types ≤ 2^2 = 4 (and the bound instance holds).
example :
    fiberTypeCount (fun a b : Fin 4 => (a : ℕ) ∣ (b : ℕ))
      (Finset.univ : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)) ≤ 2 ^ 2 :=
  le_trans (fiberTypeCount_le_two_pow _ _ _) (by decide)

-- Degenerate target: fiber types on ∅ are all equal, so one cell (for nonempty C).
example :
    (fiberPartition (fun a b : Fin 3 => a = b)
      (Finset.univ : Finset (Fin 3)) ∅).parts.card = 1 := by
  rw [card_parts_fiberPartition]
  decide

-- Degenerate source: no elements, no cells.
example :
    (fiberPartition (fun a b : Fin 3 => a = b) ∅ Finset.univ).parts.card = 0 := by
  rw [card_parts_fiberPartition]
  decide

-- Refinement under target growth: the divisibility partition on the full target is
-- finer than on the subtarget (instance of the general theorem).
example :
    fiberPartition (fun a b : Fin 4 => (a : ℕ) ∣ (b : ℕ))
        (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 4))
      ≤ fiberPartition (fun a b : Fin 4 => (a : ℕ) ∣ (b : ℕ))
          (Finset.univ : Finset (Fin 4)) {1, 2} :=
  fiberPartition_le_of_subset _ (Finset.subset_univ _)

-- Symmetric constancy: equality is symmetric, so one partition suffices.
example :
    ∀ C ∈ (fiberPartition (fun a b : Fin 2 => a = b) Finset.univ Finset.univ).parts,
      ∀ D ∈ (fiberPartition (fun a b : Fin 2 => a = b) Finset.univ Finset.univ).parts,
        (∀ a ∈ C, ∀ d ∈ D, a = d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬(a = d)) :=
  fun _ hC _ hD =>
    fiberPartition_pair_constant_of_symm (fun _ _ h => h.symm) hC hD

-- Constancy on the common refinement, concretely (the general homogeneous form).
example :
    ∀ C ∈ ((fiberPartition (fun a b : Fin 2 => a = b) Finset.univ Finset.univ)
        ⊓ (fiberPartition (fun a b : Fin 2 => b = a) Finset.univ Finset.univ)).parts,
      ∀ D ∈ ((fiberPartition (fun a b : Fin 2 => a = b) Finset.univ Finset.univ)
        ⊓ (fiberPartition (fun a b : Fin 2 => b = a) Finset.univ Finset.univ)).parts,
        (∀ a ∈ C, ∀ d ∈ D, a = d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬(a = d)) := by
  intro C hC D hD
  exact inf_fiberPartition_constant (fun a b : Fin 2 => a = b) hC hD

end Tests

end RegularityLemmata
