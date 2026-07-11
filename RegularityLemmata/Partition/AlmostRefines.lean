/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.Equitable
import Mathlib.Tactic.Ring

/-!
# Almost-refinement of partitions

`AlmostRefinesAt Q P m` is the raw per-parent form of almost-refinement: inside every
part `t` of `P`, the elements not covered by `Q`-parts contained in `t` number at most
`m`. This is exactly the shape mathlib proves for `Finpartition.equitabilise`
(`Finpartition.card_parts_equitabilise_subset_le`), re-exported here as
`equitabilise_almostRefinesAt` — the quantitative bridge the graph regularity ladder
consumes: an equitabilisation with part sizes in `{m, m+1}` almost-refines `P` at
tolerance `ε` as soon as `m · #P.parts ≤ ε · |s|`
(`almostRefines_of_almostRefinesAt`).

`exceptionalMass Q P` is the total uncovered mass, and `AlmostRefines Q P ε` its
normalized form. Composition is additive at the mass level (`AlmostRefines.trans`), and
almost-refinement is stable under further refinement of `Q`
(`almostRefinesAt_anti_left`). These were proved in general — not just checked on small
hosts — before this API was frozen.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The part of `t` not covered by parts of `Q` contained in `t`. -/
def uncoveredWithin (Q : Finpartition s) (t : Finset α) : Finset α :=
  t \ (Q.parts.filter (· ⊆ t)).biUnion id

/-- Raw per-parent almost-refinement: every part of `P` has uncovered remainder of size
at most `m` in `Q`. -/
def AlmostRefinesAt (Q P : Finpartition s) (m : ℕ) : Prop :=
  ∀ t ∈ P.parts, (uncoveredWithin Q t).card ≤ m

/-- Total uncovered mass of `Q` against the parts of `P`. -/
def exceptionalMass (Q P : Finpartition s) : ℕ :=
  ∑ t ∈ P.parts, (uncoveredWithin Q t).card

/-- Normalized almost-refinement: the exceptional mass is at most `ε · |s|`. -/
def AlmostRefines (Q P : Finpartition s) (ε : ℝ) : Prop :=
  (exceptionalMass Q P : ℝ) ≤ ε * s.card

variable {P Q Q' R : Finpartition s} {m : ℕ} {ε ε₁ ε₂ : ℝ}

/-! ### Exact refinement gives zero remainder -/

/-- An actual refinement almost-refines with zero remainder. -/
theorem almostRefinesAt_of_le (hQ : Q ≤ P) : AlmostRefinesAt Q P 0 := by
  intro t ht
  rw [uncoveredWithin, biUnion_filter_subset_eq hQ ht, Finset.sdiff_self,
    Finset.card_empty]

theorem almostRefinesAt_refl : AlmostRefinesAt P P 0 :=
  almostRefinesAt_of_le le_rfl

theorem bot_almostRefinesAt : AlmostRefinesAt (⊥ : Finpartition s) P 0 :=
  almostRefinesAt_of_le bot_le

/-! ### Monotonicity -/

theorem AlmostRefinesAt.mono {m' : ℕ} (hm : m ≤ m') (h : AlmostRefinesAt Q P m) :
    AlmostRefinesAt Q P m' := fun t ht => (h t ht).trans hm

theorem AlmostRefines.mono (hε : ε₁ ≤ ε₂) (h : AlmostRefines Q P ε₁) :
    AlmostRefines Q P ε₂ :=
  h.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- Refining `Q` further can only shrink each uncovered remainder. -/
theorem uncoveredWithin_anti (hQ' : Q' ≤ Q) (t : Finset α) :
    uncoveredWithin Q' t ⊆ uncoveredWithin Q t := by
  intro x hx
  rw [uncoveredWithin, Finset.mem_sdiff] at hx ⊢
  refine ⟨hx.1, fun hcov => hx.2 ?_⟩
  rw [Finset.mem_biUnion] at hcov
  obtain ⟨E, hEf, hxE⟩ := hcov
  rw [Finset.mem_filter] at hEf
  obtain ⟨E', hE'mem, hxE'⟩ := Q'.exists_mem (Q.le hEf.1 hxE)
  obtain ⟨E'', hE''mem, hE'sub⟩ := hQ' hE'mem
  have : E'' = E := Q.eq_of_mem_parts hE''mem hEf.1 (hE'sub hxE') hxE
  rw [Finset.mem_biUnion]
  exact ⟨E', Finset.mem_filter.mpr ⟨hE'mem, (this ▸ hE'sub).trans hEf.2⟩, hxE'⟩

/-- Almost-refinement is stable under further refinement of the finer partition. -/
theorem almostRefinesAt_anti_left (hQ' : Q' ≤ Q) (h : AlmostRefinesAt Q P m) :
    AlmostRefinesAt Q' P m := fun t ht =>
  (Finset.card_le_card (uncoveredWithin_anti hQ' t)).trans (h t ht)

theorem exceptionalMass_anti_left (hQ' : Q' ≤ Q) :
    exceptionalMass Q' P ≤ exceptionalMass Q P :=
  Finset.sum_le_sum fun t _ => Finset.card_le_card (uncoveredWithin_anti hQ' t)

theorem almostRefines_anti_left (hQ' : Q' ≤ Q) (h : AlmostRefines Q P ε) :
    AlmostRefines Q' P ε :=
  le_trans (by exact_mod_cast exceptionalMass_anti_left hQ') h

/-! ### Mass bounds and the normalized form -/

theorem exceptionalMass_le_of_almostRefinesAt (h : AlmostRefinesAt Q P m) :
    exceptionalMass Q P ≤ m * P.parts.card := by
  calc exceptionalMass Q P ≤ ∑ _t ∈ P.parts, m := Finset.sum_le_sum h
    _ = P.parts.card * m := by rw [Finset.sum_const, smul_eq_mul]
    _ = m * P.parts.card := Nat.mul_comm _ _

/-- **Quantitative bridge.** A per-parent remainder `m` gives normalized
almost-refinement at any `ε` with `m · #P.parts ≤ ε · |s|` — the exact arithmetic the
regular-equipartition theorems consume. -/
theorem almostRefines_of_almostRefinesAt (h : AlmostRefinesAt Q P m)
    (hm : (m * P.parts.card : ℝ) ≤ ε * s.card) : AlmostRefines Q P ε := by
  refine le_trans ?_ hm
  exact_mod_cast exceptionalMass_le_of_almostRefinesAt h

theorem almostRefines_of_le (hQ : Q ≤ P) (hε : 0 ≤ ε) : AlmostRefines Q P ε := by
  refine almostRefines_of_almostRefinesAt (almostRefinesAt_of_le hQ) ?_
  simp only [Nat.cast_zero, zero_mul]
  exact mul_nonneg hε (Nat.cast_nonneg _)

theorem almostRefines_refl : AlmostRefines P P 0 :=
  almostRefines_of_le le_rfl le_rfl

/-! ### The equitabilise bridge -/

/-- **Equitabilisation almost-refines.** Direct re-export of mathlib's per-parent
remainder bound for `Finpartition.equitabilise`. -/
theorem equitabilise_almostRefinesAt {a b : ℕ} (P : Finpartition s)
    (h : a * m + b * (m + 1) = s.card) :
    AlmostRefinesAt (P.equitabilise h) P m := fun _ ht =>
  equitabilise_uncovered_card_le ht

/-! ### Composition -/

/-- Set-level composition bound: what `R` leaves uncovered in a `P`-part is covered by
what `Q` leaves uncovered there plus what `R` leaves uncovered inside each `Q`-part. -/
theorem uncoveredWithin_subset_trans (t : Finset α) :
    uncoveredWithin R t ⊆
      uncoveredWithin Q t ∪
        (Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u) := by
  intro x hx
  rw [uncoveredWithin, Finset.mem_sdiff] at hx
  rw [Finset.mem_union]
  by_cases hq : x ∈ (Q.parts.filter (· ⊆ t)).biUnion id
  · right
    rw [Finset.mem_biUnion] at hq ⊢
    obtain ⟨u, huf, hxu⟩ := hq
    refine ⟨u, huf, ?_⟩
    rw [uncoveredWithin, Finset.mem_sdiff]
    refine ⟨hxu, fun hcov => hx.2 ?_⟩
    rw [Finset.mem_biUnion] at hcov ⊢
    obtain ⟨v, hvf, hxv⟩ := hcov
    rw [Finset.mem_filter] at hvf huf
    exact ⟨v, Finset.mem_filter.mpr ⟨hvf.1, hvf.2.trans huf.2⟩, hxv⟩
  · left
    rw [uncoveredWithin, Finset.mem_sdiff]
    exact ⟨hx.1, hq⟩

/-- **Composition, additive at the mass level.** -/
theorem AlmostRefines.trans (hRQ : AlmostRefines R Q ε₂) (hQP : AlmostRefines Q P ε₁) :
    AlmostRefines R P (ε₁ + ε₂) := by
  have hstep : ∀ t ∈ P.parts, (uncoveredWithin R t).card
      ≤ (uncoveredWithin Q t).card
        + ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card := by
    intro t ht
    calc (uncoveredWithin R t).card
        ≤ (uncoveredWithin Q t ∪
            (Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u)).card :=
          Finset.card_le_card (uncoveredWithin_subset_trans t)
      _ ≤ (uncoveredWithin Q t).card
            + ((Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u)).card :=
          Finset.card_union_le _ _
      _ ≤ (uncoveredWithin Q t).card
            + ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
  -- Is Q ≤ P available? NO — composition must not assume it. Reindex the double sum
  -- over Q-parts-inside-t by bounding it by the full sum over Q.parts instead.
  have hmass : (exceptionalMass R P : ℝ)
      ≤ (exceptionalMass Q P : ℝ) + (exceptionalMass R Q : ℝ) := by
    have hnat : exceptionalMass R P
        ≤ exceptionalMass Q P
          + ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card := by
      rw [exceptionalMass, exceptionalMass, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hstep
    have hinner : ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card
        ≤ exceptionalMass R Q := by
      rw [exceptionalMass]
      calc ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card
          = ∑ u ∈ P.parts.biUnion (fun t => Q.parts.filter (· ⊆ t)),
              (uncoveredWithin R u).card := by
            rw [Finset.sum_biUnion ?_]
            intro t₁ ht₁ t₂ ht₂ hne
            simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
            rintro u ⟨humem, hsub₁⟩ ⟨-, hsub₂⟩
            obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts humem
            exact hne (P.eq_of_mem_parts (Finset.mem_coe.mp ht₁) (Finset.mem_coe.mp ht₂)
              (hsub₁ hx) (hsub₂ hx))
        _ ≤ ∑ u ∈ Q.parts, (uncoveredWithin R u).card := by
            refine Finset.sum_le_sum_of_subset (fun u hu => ?_)
            rw [Finset.mem_biUnion] at hu
            obtain ⟨t, -, huf⟩ := hu
            exact (Finset.mem_filter.mp huf).1
    exact_mod_cast le_trans hnat (Nat.add_le_add_left hinner _)
  calc (exceptionalMass R P : ℝ)
      ≤ (exceptionalMass Q P : ℝ) + (exceptionalMass R Q : ℝ) := hmass
    _ ≤ ε₁ * s.card + ε₂ * s.card := add_le_add hQP hRQ
    _ = (ε₁ + ε₂) * s.card := by ring

/-! ### Tests and adversarial examples (the falsification-gate battery) -/

-- Reflexivity and exact refinement, computed: uncovered remainders are empty.
example :
    exceptionalMass (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) = 0 := by decide
example :
    exceptionalMass (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) = 0 := by decide

-- NON-refinement has positive mass: ⊤ does not almost-refine ⊥ for free.
example :
    exceptionalMass (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
      (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))) = 3 := by decide

-- Degenerate hosts: empty ground set (mass 0; `AlmostRefines` holds even at ε = 0),
-- and a singleton ground set.
example (P Q : Finpartition (∅ : Finset (Fin 3))) : AlmostRefines Q P 0 := by
  have : exceptionalMass Q P = 0 := by
    rw [exceptionalMass, Finset.sum_eq_zero]
    intro t ht
    have := P.le ht
    simp_all [Finset.subset_empty.mp this]
  rw [AlmostRefines, this]
  simp
example :
    exceptionalMass (⊥ : Finpartition ({0} : Finset (Fin 3)))
      (⊤ : Finpartition ({0} : Finset (Fin 3))) = 0 := by decide

-- The quantitative bridge instantiated: singletons almost-refine anything at ε = 0.
example (P : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    AlmostRefines (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))) P 0 :=
  almostRefines_of_le bot_le le_rfl

end RegularityLemmata
