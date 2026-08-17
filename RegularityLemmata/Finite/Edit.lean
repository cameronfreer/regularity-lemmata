/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Injective

/-!
# Edit sets and edit distance

The edit set of two relations on a box is the finset of tuples where they disagree; the
edit distance is its cardinality (a raw `ℕ` count), and the relative edit distance its
density. Disagreement is phrased as `¬ (R₁ x ↔ R₂ x)`, which is decidable from
`DecidablePred` instances, so edit sets and distances are computable.

Besides the metric laws (symmetry, triangle inequality), the file provides the budget
lemmas used by removal arguments: monotonicity in the box, summation along a chain of
relations, and the split of the full-box edit distance into an injective part plus the
collision count from `RegularityLemmata.Finite.Injective`.

It also provides the **bridges to tuple counting**: when one relation is constant on the box
the edit distance is a plain `tupleCount`, and a `tupleDensity` bound on the other becomes a
count bound against the box mass. These relate two pinned definitions and introduce no second
counting layer — every counting primitive they use comes from
`RegularityLemmata.Finite.Density`.

Coordinates are indexed by an **arbitrary** finite type `ι` with decidable equality, matching
`RegularityLemmata.Finite.Density`. Nothing here uses the order structure of `Fin k`; the
chain-summation lemma indexes its *chain* by `Fin (m + 1)`, which is a separate index and
stays as it is.
-/

namespace RegularityLemmata

variable {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R₁ R₂ R₃ : (ι → α) → Prop}
  [DecidablePred R₁] [DecidablePred R₂] [DecidablePred R₃]
variable {A B : ι → Finset α}

/-! ### Edit sets -/

/-- The tuples of the box `A` on which `R₁` and `R₂` disagree. -/
def editSet (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁] [DecidablePred R₂]
    (A : ι → Finset α) : Finset (ι → α) :=
  (Fintype.piFinset A).filter fun x => ¬ (R₁ x ↔ R₂ x)

@[simp] theorem mem_editSet {x : ι → α} :
    x ∈ editSet R₁ R₂ A ↔ x ∈ Fintype.piFinset A ∧ ¬ (R₁ x ↔ R₂ x) := by
  simp [editSet]

theorem editSet_comm : editSet R₁ R₂ A = editSet R₂ R₁ A := by
  simp only [editSet]
  exact Finset.filter_congr fun x _ => by tauto

/-! ### Edit distance -/

/-- The number of tuples of the box on which the relations disagree. -/
def editDistance (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁] [DecidablePred R₂]
    (A : ι → Finset α) : ℕ :=
  (editSet R₁ R₂ A).card

theorem editDistance_comm : editDistance R₁ R₂ A = editDistance R₂ R₁ A := by
  rw [editDistance, editDistance, editSet_comm]

@[simp] theorem editDistance_self : editDistance R₁ R₁ A = 0 := by
  simp [editDistance, editSet]

theorem editDistance_le_card :
    editDistance R₁ R₂ A ≤ (Fintype.piFinset A).card :=
  Finset.card_filter_le _ _

theorem editDistance_triangle :
    editDistance R₁ R₃ A ≤ editDistance R₁ R₂ A + editDistance R₂ R₃ A := by
  classical
  have hsub : editSet R₁ R₃ A ⊆ editSet R₁ R₂ A ∪ editSet R₂ R₃ A := by
    intro x hx
    rw [mem_editSet] at hx
    rw [Finset.mem_union, mem_editSet, mem_editSet]
    by_cases h12 : R₁ x ↔ R₂ x
    · exact Or.inr ⟨hx.1, fun h23 => hx.2 (h12.trans h23)⟩
    · exact Or.inl ⟨hx.1, h12⟩
  calc editDistance R₁ R₃ A ≤ (editSet R₁ R₂ A ∪ editSet R₂ R₃ A).card :=
        Finset.card_le_card hsub
    _ ≤ editDistance R₁ R₂ A + editDistance R₂ R₃ A := Finset.card_union_le _ _

/-- Edit distance grows with the box. -/
theorem editDistance_mono_box (h : ∀ i, A i ⊆ B i) :
    editDistance R₁ R₂ A ≤ editDistance R₁ R₂ B := by
  refine Finset.card_le_card fun x hx => ?_
  rw [mem_editSet] at hx ⊢
  exact ⟨Fintype.mem_piFinset.mpr fun i => h i (Fintype.mem_piFinset.mp hx.1 i), hx.2⟩

/-- Edit-budget summation along a chain of relations. -/
theorem editDistance_le_sum_chain {m : ℕ}
    (Rs : Fin (m + 1) → (ι → α) → Prop) [∀ i, DecidablePred (Rs i)]
    (A : ι → Finset α) :
    editDistance (Rs 0) (Rs (Fin.last m)) A
      ≤ ∑ i : Fin m, editDistance (Rs i.castSucc) (Rs i.succ) A := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc editDistance (Rs 0) (Rs (Fin.last (m + 1))) A
        ≤ editDistance (Rs 0) (Rs (Fin.last m).castSucc) A
            + editDistance (Rs (Fin.last m).castSucc) (Rs (Fin.last (m + 1))) A :=
          editDistance_triangle
      _ ≤ (∑ i : Fin m, editDistance (Rs i.castSucc.castSucc) (Rs i.succ.castSucc) A)
            + editDistance (Rs (Fin.last m).castSucc) (Rs (Fin.last (m + 1))) A := by
          have hih := ih (fun i : Fin (m + 1) => Rs i.castSucc)
          rw [Fin.castSucc_zero] at hih
          exact Nat.add_le_add_right hih _
      _ = ∑ i : Fin (m + 1), editDistance (Rs i.castSucc) (Rs i.succ) A := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.succ_castSucc, Fin.succ_last, Nat.succ_eq_add_one]

/-- Diagonal control on the full box: the edit distance splits into its injective part
plus at most the collision count. -/
theorem editDistance_univ_le_injective_add_nonInjective [Fintype α] [DecidableEq α] :
    editDistance R₁ R₂ (fun _ => Finset.univ)
      ≤ ((editSet R₁ R₂ fun _ => Finset.univ).filter Function.Injective).card
        + (nonInjectiveMaps ι α).card := by
  rw [editDistance,
    ← Finset.card_filter_add_card_filter_not
      (s := editSet R₁ R₂ fun _ => Finset.univ) Function.Injective]
  refine Nat.add_le_add_left (Finset.card_le_card fun f hf => ?_) _
  rw [Finset.mem_filter] at hf
  exact mem_nonInjectiveMaps.mpr hf.2

/-! ### Bridges to tuple counting

If one of the two relations is constant on the box, the edit set is exactly the truth set (or
the falsity set) of the other, so the edit distance collapses to a `tupleCount` and a
`tupleDensity` bound converts into a count bound against the box mass.

The two count bounds are deliberately asymmetric. The sparse form is guard-free; the dense form
requires every side of the box to be nonempty, because that is what the pinned
`tupleDensity_neg` requires. The same asymmetry is recorded in
`RegularityLemmata.Finite.HomogeneousCell`'s frozen conventions and is not an artefact here. -/

/-- If `R₂` is false on every tuple of the box, the edit distance counts the tuples
satisfying `R₁`. -/
theorem editDistance_eq_tupleCount_of_forall_not (h : ∀ x ∈ Fintype.piFinset A, ¬ R₂ x) :
    editDistance R₁ R₂ A = tupleCount R₁ A :=
  congrArg Finset.card (Finset.filter_congr fun x hx ↦ by simp [h x hx])

/-- If `R₂` is true on every tuple of the box, the edit distance counts the tuples where `R₁`
fails. -/
theorem editDistance_eq_tupleCount_not_of_forall (h : ∀ x ∈ Fintype.piFinset A, R₂ x) :
    editDistance R₁ R₂ A = tupleCount (fun x ↦ ¬ R₁ x) A :=
  congrArg Finset.card (Finset.filter_congr fun x hx ↦ by simp [h x hx])

/-- **Sparse branch.** Against a relation that is constantly false on the box, a density upper
bound on `R₁` bounds the edit distance by that fraction of the box mass. Guard-free: with an
empty side both sides are `0`. -/
theorem editDistance_le_of_tupleDensity_le {ε : ℝ} (hd : tupleDensity R₁ A ≤ ε)
    (hconst : ∀ x ∈ Fintype.piFinset A, ¬ R₂ x) :
    (editDistance R₁ R₂ A : ℝ) ≤ ε * ∏ i, ((A i).card : ℝ) := by
  rw [editDistance_eq_tupleCount_of_forall_not hconst]
  exact card_filter_le_of_tupleDensity_le hd

/-- **Dense branch.** Against a relation that is constantly true on the box, a density lower
bound `1 - ε ≤ d` on `R₁` bounds the edit distance by an `ε` fraction of the box mass. The
nonemptiness hypothesis is the one `tupleDensity_neg` carries. -/
theorem editDistance_le_of_le_tupleDensity {ε : ℝ} (hd : 1 - ε ≤ tupleDensity R₁ A)
    (hconst : ∀ x ∈ Fintype.piFinset A, R₂ x) (hne : ∀ i, (A i).Nonempty) :
    (editDistance R₁ R₂ A : ℝ) ≤ ε * ∏ i, ((A i).card : ℝ) := by
  rw [editDistance_eq_tupleCount_not_of_forall hconst]
  refine card_filter_le_of_tupleDensity_le ?_
  rw [tupleDensity_neg hne]
  linarith

/-! ### Relative edit distance -/

/-- Normalized edit distance: the density of disagreement on the box. -/
noncomputable def relativeEditDistance (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁]
    [DecidablePred R₂] (A : ι → Finset α) : ℝ :=
  densityOn (Fintype.piFinset A) fun x => ¬ (R₁ x ↔ R₂ x)

/-- The bridge between relative and raw edit distance. -/
theorem relativeEditDistance_eq :
    relativeEditDistance R₁ R₂ A
      = (editDistance R₁ R₂ A : ℝ) / ((Fintype.piFinset A).card : ℝ) := rfl

theorem relativeEditDistance_nonneg : 0 ≤ relativeEditDistance R₁ R₂ A :=
  densityOn_nonneg

theorem relativeEditDistance_le_one : relativeEditDistance R₁ R₂ A ≤ 1 :=
  densityOn_le_one

theorem relativeEditDistance_comm :
    relativeEditDistance R₁ R₂ A = relativeEditDistance R₂ R₁ A := by
  rw [relativeEditDistance_eq, relativeEditDistance_eq, editDistance_comm]

/-! ### Tests and adversarial examples -/

-- Full flip: the relations disagree everywhere on the box.
example :
    editDistance (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun x => ¬ x 0 = x 1)
      (fun _ => Finset.univ) = 4 := by decide

example : editDistance (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun x => x 0 = x 1)
    (fun _ => Finset.univ) = 0 := by decide

-- A triangle instance with strict slack: d(R₁,R₃) = 0 < d(R₁,R₂) + d(R₂,R₃) = 8.
example :
    editDistance (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun x => x 0 = x 1)
        (fun _ => Finset.univ)
      < editDistance (fun x : Fin 2 → Fin 2 => x 0 = x 1) (fun x => ¬ x 0 = x 1)
          (fun _ => Finset.univ)
        + editDistance (fun x : Fin 2 → Fin 2 => ¬ x 0 = x 1) (fun x => x 0 = x 1)
            (fun _ => Finset.univ) := by decide

-- An empty box side kills the edit distance.
example :
    editDistance (fun x : Fin 2 → Fin 3 => x 0 = x 1) (fun x => ¬ x 0 = x 1)
      ![Finset.univ, ∅] = 0 := by decide

-- **Index-generic**: coordinates indexed by `Bool` rather than `Fin 2`. A full flip still
-- disagrees on all 4 tuples of the full box.
example :
    editDistance (fun x : Bool → Fin 2 => x true = x false) (fun x => ¬ x true = x false)
      (fun _ => Finset.univ) = 4 := by decide

-- **Degenerate index**: over an empty index type the box is a singleton, so two relations
-- that disagree on the empty tuple are at edit distance `1`.
example :
    editDistance (fun _ : Empty → Fin 3 => True) (fun _ => False) (fun _ => Finset.univ) = 1 := by
  decide

-- **Bridge, constantly-false side**: the edit distance against `False` is the count of `R₁`.
example :
    editDistance (fun x : Fin 1 → Fin 2 => x 0 = 0) (fun _ => False) (fun _ => Finset.univ)
      = tupleCount (fun x : Fin 1 → Fin 2 => x 0 = 0) (fun _ => Finset.univ) := by decide

-- **Bridge, constantly-true side**: the edit distance against `True` is the count of `¬ R₁`.
example :
    editDistance (fun x : Fin 1 → Fin 2 => x 0 = 0) (fun _ => True) (fun _ => Finset.univ)
      = tupleCount (fun x : Fin 1 → Fin 2 => ¬ x 0 = 0) (fun _ => Finset.univ) := by decide

-- Relative edit distance of a half-flip is 1/2: over `Fin 2` (as `Fin 1`-tuples),
-- `x 0 = 0` and `True` disagree exactly on `x 0 = 1`, i.e. on 1 of 2 tuples.
example :
    relativeEditDistance (fun x : Fin 1 → Fin 2 => x 0 = 0) (fun _ => True)
      (fun _ => Finset.univ) = 1 / 2 := by
  rw [relativeEditDistance_eq,
    show editDistance (fun x : Fin 1 → Fin 2 => x 0 = 0) (fun _ => True)
        (fun _ => Finset.univ) = 1 from by decide,
    show (Fintype.piFinset fun _ : Fin 1 => (Finset.univ : Finset (Fin 2))).card = 2 from by
      decide]
  norm_num

end RegularityLemmata
