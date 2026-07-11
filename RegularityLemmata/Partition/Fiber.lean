/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.Basic

/-!
# Fiber-type partitions

Partition a finite set `C` by the *fiber type* of its elements on a target set `D`:
`fiberType R D a = {d ∈ D | R a d}`. Elements with equal fiber types form the cells of
`fiberPartition R C D` — a thin wrap of mathlib's `Finpartition.ofSetSetoid` — and the
cell count is exactly the number of distinct fiber types (`card_parts_fiberPartition`).

The payoff is *constancy*: on the common refinement of the forward and backward fiber
partitions of a ground set, the relation is constant on every ordered pair of cells
(`inf_fiberPartition_constant`), and constancy transfers down any further refinement
(`pair_constant_of_le`, `pred_constant_of_le`). This is the finite type-space
partition underlying stable regularity — see M. Malliaris, S. Shelah, *Regularity
lemmas for stable graphs*, Trans. AMS 366 (2014), where cells are Δ-types over a
finite parameter set; here the "types" are quantifier-free fiber types of a single
relation. Cell counts under repeated common refinement are controlled by
`card_parts_inf'_le` (in `Partition/Basic.lean`).

Constancy statements use the house disjunction form (`(∀ …, R a d) ∨ (∀ …, ¬R a d)`),
not a `Bool` encoding; parts of a `Finpartition` are nonempty, so no `Nonempty`
hypotheses appear.
-/

namespace RegularityLemmata

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Fiber types -/

section FiberType

variable (R : α → α → Prop) [DecidableRel R]

/-- The fiber type of `a` on `D`: the elements of `D` that `a` is `R`-related to. -/
def fiberType (D : Finset α) (a : α) : Finset α :=
  D.filter (R a)

omit [DecidableEq α] in
@[simp] theorem mem_fiberType {D : Finset α} {a d : α} :
    d ∈ fiberType R D a ↔ d ∈ D ∧ R a d := by
  simp [fiberType]

omit [DecidableEq α] in
theorem fiberType_subset (D : Finset α) (a : α) : fiberType R D a ⊆ D :=
  filter_subset _ _

omit [DecidableEq α] in
/-- Equal fiber types on `D` = agreement of `R` against every element of `D`. -/
theorem fiberType_eq_iff {D : Finset α} {a₁ a₂ : α} :
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

omit [DecidableEq α] in
theorem fiberType_mono {D₁ D₂ : Finset α} (h : D₁ ⊆ D₂) (a : α) :
    fiberType R D₁ a ⊆ fiberType R D₂ a := by
  intro d hd
  rw [mem_fiberType] at hd ⊢
  exact ⟨h hd.1, hd.2⟩

end FiberType

/-! ### The fiber partition -/

section FiberPartition

variable (R : α → α → Prop) [DecidableRel R]

/-- The setoid relating elements with the same fiber type on `D`. -/
def fiberSetoid (D : Finset α) : Setoid α where
  r a₁ a₂ := fiberType R D a₁ = fiberType R D a₂
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance fiberSetoid_decidableRel (D : Finset α) : DecidableRel (fiberSetoid R D).r :=
  fun a₁ a₂ => inferInstanceAs (Decidable (fiberType R D a₁ = fiberType R D a₂))

/-- The partition of `C` by fiber type on `D` (mathlib's `Finpartition.ofSetSetoid`
at the fiber setoid). -/
def fiberPartition (C D : Finset α) : Finpartition C :=
  Finpartition.ofSetSetoid (fiberSetoid R D) C

/-- The parts, explicitly: one filter per represented fiber type. -/
theorem fiberPartition_parts (C D : Finset α) :
    (fiberPartition R C D).parts
      = C.image fun a => C.filter fun b => fiberType R D a = fiberType R D b := by
  simp [fiberPartition, Finpartition.ofSetSetoid_parts, fiberSetoid]

/-- Members of one part share their fiber type. -/
theorem fiberType_eq_of_mem_part {C D : Finset α} {t : Finset α}
    (ht : t ∈ (fiberPartition R C D).parts) {a b : α} (ha : a ∈ t) (hb : b ∈ t) :
    fiberType R D a = fiberType R D b := by
  rw [fiberPartition_parts] at ht
  rw [Finset.mem_image] at ht
  obtain ⟨c, _, rfl⟩ := ht
  rw [Finset.mem_filter] at ha hb
  exact ha.2.symm.trans hb.2

/-- The number of distinct fiber types of elements of `C` on `D`. -/
def fiberTypeCount (C D : Finset α) : ℕ :=
  (C.image (fiberType R D)).card

/-- Cells of the fiber partition biject with the represented fiber types. -/
theorem card_parts_fiberPartition (C D : Finset α) :
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

end FiberPartition

/-! ### Constancy on common refinements -/

section Constancy

variable {s : Finset α}

/-- **Pairwise constancy.** On the common refinement of the forward and backward
fiber partitions of `s` (fiber types taken on all of `s`), the relation is constant
on every ordered pair of cells. -/
theorem inf_fiberPartition_constant (R : α → α → Prop) [DecidableRel R]
    {C D : Finset α}
    (hC : C ∈ (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).parts)
    (hD : D ∈ (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).parts) :
    (∀ a ∈ C, ∀ d ∈ D, R a d) ∨ (∀ a ∈ C, ∀ d ∈ D, ¬R a d) := by
  classical
  obtain ⟨a₀, ha₀⟩ :=
    (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).nonempty_of_mem_parts hC
  obtain ⟨d₀, hd₀⟩ :=
    (fiberPartition R s s ⊓ fiberPartition (fun a b => R b a) s s).nonempty_of_mem_parts hD
  rw [Finpartition.parts_inf] at hC hD
  rw [Finset.mem_erase, Finset.mem_image] at hC hD
  obtain ⟨-, ⟨⟨A₁, B₁⟩, hAB₁, hCeq⟩⟩ := hC
  obtain ⟨-, ⟨⟨A₂, B₂⟩, hAB₂, hDeq⟩⟩ := hD
  rw [Finset.mem_product] at hAB₁ hAB₂
  -- Everything in one cell agrees with the representative:
  have hfwd : ∀ a ∈ C, ∀ x ∈ s, (R a x ↔ R a₀ x) := by
    intro a ha x hx
    have haA : a ∈ A₁ := by
      rw [← hCeq] at ha
      exact (Finset.mem_inter.mp ha).1
    have ha₀A : a₀ ∈ A₁ := by
      rw [← hCeq] at ha₀
      exact (Finset.mem_inter.mp ha₀).1
    exact (fiberType_eq_iff R).mp (fiberType_eq_of_mem_part R hAB₁.1 haA ha₀A) x hx
  have hbwd : ∀ d ∈ D, ∀ x ∈ s, (R x d ↔ R x d₀) := by
    intro d hd x hx
    have hdB : d ∈ B₂ := by
      rw [← hDeq] at hd
      exact (Finset.mem_inter.mp hd).2
    have hd₀B : d₀ ∈ B₂ := by
      rw [← hDeq] at hd₀
      exact (Finset.mem_inter.mp hd₀).2
    exact (fiberType_eq_iff _).mp
      (fiberType_eq_of_mem_part (fun a b => R b a) hAB₂.2 hdB hd₀B) x hx
  have hDs : D ⊆ s := by
    rw [← hDeq]
    exact (Finset.inter_subset_left).trans
      ((fiberPartition R s s).le hAB₂.1)
  have hCs : C ⊆ s := by
    rw [← hCeq]
    exact (Finset.inter_subset_left).trans
      ((fiberPartition R s s).le hAB₁.1)
  have hchain : ∀ a ∈ C, ∀ d ∈ D, (R a d ↔ R a₀ d₀) := by
    intro a ha d hd
    exact (hfwd a ha d (hDs hd)).trans (hbwd d hd a₀ (hCs ha₀))
  by_cases h₀ : R a₀ d₀
  · exact Or.inl fun a ha d hd => (hchain a ha d hd).mpr h₀
  · exact Or.inr fun a ha d hd hR => h₀ ((hchain a ha d hd).mp hR)

/-- Pairwise constancy transfers down refinement: constant on `Q`-cell pairs and
`P ≤ Q` gives constancy on `P`-cell pairs. -/
theorem pair_constant_of_le {P Q : Finpartition s} (hle : P ≤ Q)
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
theorem pred_constant_of_le {P Q : Finpartition s} (hle : P ≤ Q)
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

-- Constancy on the common refinement, concretely: for equality on Fin 2, both
-- fiber partitions are ⊥-like (each cell a singleton), and R is constant on each
-- ordered pair of cells (true on the diagonal pair, false off it).
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
