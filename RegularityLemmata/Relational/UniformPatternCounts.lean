/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.PatternExtensions
import RegularityLemmata.Finite.Edit
import RegularityLemmata.Relational.BinaryPattern
import RegularityLemmata.Relational.CellwiseEdit

/-!
# Uniform pattern-count transfer

All symbol arguments touched by a non-diagonal pattern atom are fixed in the
extension count. Nullary compatibility and repeated-entry agreement are distinct
hypotheses. No diagonal agreement is inferred from majority rounding.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : Language} [FiniteRelational L] {V : Type*} [DecidableEq V] {k : ℕ}

/-- The finite set of ordered atomic assignments; diagonal assignments are
included in this coefficient even when they cause no error. -/
abbrev PatternAtom (L : Language) [FiniteRelational L] (k : ℕ) :=
  Σ S : RelSymbol L, Fin (S.1 : ℕ) → Fin k

/-- The language-dependent atomic coefficient, including nullary symbols. -/
def patternAtomCoefficient (L : Language) [FiniteRelational L] (k : ℕ) : ℕ :=
  ∑ S : RelSymbol L, k ^ (S.1 : ℕ)

private theorem single_atom_bound (s : Finset V) {n : ℕ} (E : Finset (Fin n → V))
    (x : Fin n → Fin k) (hx : Function.Injective x) {ε : ℝ}
    (hE : (E.card : ℝ) ≤ ε * (s.card : ℝ) ^ n) :
    (((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ f ∘ x ∈ E).card : ℝ) ≤
      ε * (s.card : ℝ) ^ k := by
  have hn : n ≤ k := by simpa using Fintype.card_le_of_injective x hx
  have hb := card_filter_comp_mem_le_of_injective s E x hx
  calc
    _ ≤ (E.card : ℝ) * (s.card : ℝ) ^ (k - n) := by exact_mod_cast hb
    _ ≤ (ε * (s.card : ℝ) ^ n) * (s.card : ℝ) ^ (k - n) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

/-- Shared counting step. Every changed test is covered by an edited atom on
distinct pattern vertices. No assumption on injectivity of the host map is
needed by this counting step itself. -/
theorem abs_filter_card_sub_le_of_atom_cover (s : Finset V)
    (A B : (Fin k → V) → Prop) [DecidablePred A] [DecidablePred B]
    (E : (S : RelSymbol L) → Finset (Fin (S.1 : ℕ) → V)) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hE : ∀ S, 0 < (S.1 : ℕ) → ((E S).card : ℝ) ≤ ε * (s.card : ℝ) ^ (S.1 : ℕ))
    (hcover : ∀ f ∈ Fintype.piFinset (fun _ : Fin k ↦ s), ¬ (A f ↔ B f) →
      ∃ z : PatternAtom L k, 0 < (z.1.1 : ℕ) ∧ Function.Injective z.2 ∧
        f ∘ z.2 ∈ E z.1) :
    |(((Fintype.piFinset fun _ : Fin k ↦ s).filter A).card : ℝ) -
      ((Fintype.piFinset fun _ : Fin k ↦ s).filter B).card| ≤
        patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k := by
  classical
  let box := Fintype.piFinset fun _ : Fin k ↦ s
  let event := fun z : PatternAtom L k ↦ box.filter fun f ↦
    0 < (z.1.1 : ℕ) ∧ Function.Injective z.2 ∧ f ∘ z.2 ∈ E z.1
  let bad := Finset.univ.biUnion event
  have hsingle (z : PatternAtom L k) : ((event z).card : ℝ) ≤ ε * (s.card : ℝ) ^ k := by
    by_cases hz : 0 < (z.1.1 : ℕ) ∧ Function.Injective z.2
    · have he : event z = box.filter (fun f ↦ f ∘ z.2 ∈ E z.1) := by
        ext f
        simp only [event, Finset.mem_filter]
        exact ⟨fun ⟨hf, _, _, he⟩ ↦ ⟨hf, he⟩,
          fun ⟨hf, he⟩ ↦ ⟨hf, hz.1, hz.2, he⟩⟩
      rw [he]
      exact single_atom_bound s (E z.1) z.2 hz.2 (hE z.1 hz.1)
    · have he : event z = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro f hf
        exact hz ⟨(Finset.mem_filter.mp hf).2.1, (Finset.mem_filter.mp hf).2.2.1⟩
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  have hbad : (bad.card : ℝ) ≤ patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k := by
    calc
      _ ≤ ∑ z : PatternAtom L k, ((event z).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : bad.card ≤ ∑ z, (event z).card)
      _ ≤ ∑ _z : PatternAtom L k, ε * (s.card : ℝ) ^ k :=
        Finset.sum_le_sum fun z _ ↦ hsingle z
      _ = _ := by
        simp [patternAtomCoefficient, PatternAtom, Fintype.card_sigma,
          Fintype.card_fin, mul_assoc]
  have hsub : ∀ (C D : (Fin k → V) → Prop) [DecidablePred C] [DecidablePred D],
      (∀ f, ¬ (C f ↔ D f) → ¬ (A f ↔ B f)) →
      box.filter C \ box.filter D ⊆ bad := by
    intro C D _ _ hc f hf
    obtain ⟨hfC, hfD⟩ := Finset.mem_sdiff.mp hf
    obtain ⟨hfbox, hfC⟩ := Finset.mem_filter.mp hfC
    have hnD : ¬ D f := fun h ↦ hfD (Finset.mem_filter.mpr ⟨hfbox, h⟩)
    obtain ⟨z, hz⟩ := hcover f hfbox (hc f (fun he ↦ hnD (he.mp hfC)))
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hfbox, hz⟩⟩
  have hAB := Finset.card_le_card (hsub A B (fun _ h ↦ h))
  have hBA := Finset.card_le_card (hsub B A (fun _ h he ↦ h he.symm))
  have hA := Finset.card_le_card_sdiff_add_card (s := box.filter A) (t := box.filter B)
  have hB := Finset.card_le_card_sdiff_add_card (s := box.filter B) (t := box.filter A)
  have ha : ((box.filter A).card : ℝ) ≤ bad.card + (box.filter B).card := by
    exact_mod_cast hA.trans (Nat.add_le_add_right hAB _)
  have hb : ((box.filter B).card : ℝ) ≤ bad.card + (box.filter A).card := by
    exact_mod_cast hB.trans (Nat.add_le_add_right hBA _)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Agreement on all repeated-entry tuples through `s`, independent of nullary
compatibility. It is not supplied by majority rounding. -/
def DiagonalAgreementOn (M N : FiniteRelModel L V) (s : Finset V) : Prop :=
  ∀ (S : RelSymbol L) (y : Fin (S.1 : ℕ) → V), (∀ i, y i ∈ s) →
    ¬ Function.Injective y → (M.Holds S.2 y ↔ N.Holds S.2 y)

/-- Every true pattern atom uses distinct vertices. Negative atoms are not
constrained; the condition does not assert simplicity of either host. -/
def SimplePattern (P : FiniteRelModel L (Fin k)) : Prop :=
  ∀ (S : RelSymbol L) (x : Fin (S.1 : ℕ) → Fin k), P.Holds S.2 x → Function.Injective x

omit [DecidableEq V] in
private theorem nullary_agreement {M N : FiniteRelModel L V} (hnull : NullaryCompatible M N)
    {n : ℕ} (S : L.Relations n) (hn : n = 0) (y : Fin n → V) :
    M.Holds S y ↔ N.Holds S y := by
  subst n
  have he : y = Fin.elim0 := funext fun i ↦ i.elim0
  simpa [he] using hnull S

/-- Uniform induced-count transfer under diagonal and nullary agreement.
The coefficient is independent of the host size. In fact the pattern need not
be simple once all repeated-entry atoms agree. -/
theorem abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement
    (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V) (s : Finset V)
    {ε : ℝ} (hε : 0 ≤ ε) (hnull : NullaryCompatible M N)
    (hdiag : DiagonalAgreementOn M N s)
    (hedit : ∀ S : RelSymbol L, 0 < (S.1 : ℕ) →
      (editDistance (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s) : ℝ) ≤
        ε * (s.card : ℝ) ^ (S.1 : ℕ)) :
    |(inducedEmbeddingCountOn P M (fun _ ↦ s) : ℝ) -
      inducedEmbeddingCountOn P N (fun _ ↦ s)| ≤
        patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k := by
  classical
  apply abs_filter_card_sub_le_of_atom_cover s _ _
    (fun S ↦ editSet (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s)) hε hedit
  intro f hf hdiff
  by_contra hn
  have hagree (S : RelSymbol L) (x : Fin (S.1 : ℕ) → Fin k) :
      M.Holds S.2 (f ∘ x) ↔ N.Holds S.2 (f ∘ x) := by
    by_cases hr : 0 < (S.1 : ℕ)
    · by_cases hx : Function.Injective x
      · by_contra he
        exact hn ⟨⟨S, x⟩, hr, hx, mem_editSet.mpr
          ⟨Fintype.mem_piFinset.mpr (fun i ↦ Fintype.mem_piFinset.mp hf (x i)), he⟩⟩
      · exact hdiag S (f ∘ x) (fun i ↦ Fintype.mem_piFinset.mp hf (x i))
          (fun hfx ↦ hx (fun i j hij ↦ hfx (congrArg f hij)))
    · exact nullary_agreement hnull S.2 (Nat.eq_zero_of_not_pos hr) _
  apply hdiff
  constructor
  · rintro ⟨hi, hM⟩
    exact ⟨hi, fun S x ↦ (hM S x).trans (hagree S x)⟩
  · rintro ⟨hi, hN⟩
    exact ⟨hi, fun S x ↦ (hN S x).trans (hagree S x).symm⟩

/-- Preservation-only count through a specified host set. -/
def homCountOn (P : FiniteRelModel L (Fin k)) (M : FiniteRelModel L V) (s : Finset V) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ Preserves P M f).card

/-- Injective preservation-only count through a specified host set. -/
def injectiveHomCountOn (P : FiniteRelModel L (Fin k)) (M : FiniteRelModel L V)
    (s : Finset V) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦
    Function.Injective f ∧ Preserves P M f).card

/-- Uniform injective-homomorphism transfer for a simple pattern. The hosts
need not agree on diagonals, but nullary agreement is explicit. -/
theorem abs_injectiveHomCountOn_sub_le_of_simple
    (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V) (s : Finset V)
    {ε : ℝ} (hε : 0 ≤ ε) (hnull : NullaryCompatible M N) (hP : SimplePattern P)
    (hedit : ∀ S : RelSymbol L, 0 < (S.1 : ℕ) →
      (editDistance (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s) : ℝ) ≤
        ε * (s.card : ℝ) ^ (S.1 : ℕ)) :
    |(injectiveHomCountOn P M s : ℝ) - injectiveHomCountOn P N s| ≤
      patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k := by
  classical
  apply abs_filter_card_sub_le_of_atom_cover s _ _
    (fun S ↦ editSet (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s)) hε hedit
  intro f hf hdiff
  by_contra hn
  have hagree (S : RelSymbol L) (x : Fin (S.1 : ℕ) → Fin k) (hPx : P.Holds S.2 x) :
      M.Holds S.2 (f ∘ x) ↔ N.Holds S.2 (f ∘ x) := by
    by_cases hr : 0 < (S.1 : ℕ)
    · by_contra he
      exact hn ⟨⟨S, x⟩, hr, hP S x hPx, mem_editSet.mpr
        ⟨Fintype.mem_piFinset.mpr (fun i ↦ Fintype.mem_piFinset.mp hf (x i)), he⟩⟩
    · exact nullary_agreement hnull S.2 (Nat.eq_zero_of_not_pos hr) _
  apply hdiff
  constructor
  · rintro ⟨hi, hM⟩
    exact ⟨hi, fun S x hPx ↦ (hagree S x hPx).mp (hM S x hPx)⟩
  · rintro ⟨hi, hN⟩
    exact ⟨hi, fun S x hPx ↦ (hagree S x hPx).mpr (hN S x hPx)⟩

/-- The excess of all homomorphisms over injective homomorphisms is bounded by
the ambient non-injective-map count, without any stability or simplicity premise. -/
theorem homCountOn_eq_injective_add_collision (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) (s : Finset V) :
    ∃ b : ℕ, b ≤ k.choose 2 * s.card ^ (k - 1) ∧
      homCountOn P M s = injectiveHomCountOn P M s + b := by
  classical
  let H := (Fintype.piFinset fun _ : Fin k ↦ s).filter fun f ↦ Preserves P M f
  let B := H.filter fun f ↦ ¬ Function.Injective f
  refine ⟨B.card, ?_, ?_⟩
  · have hsub : B ⊆ nonInjectiveTuplesOn (Fin k) s := by
      intro f hf
      obtain ⟨hfH, hnot⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfH).1, hnot⟩
    exact (Finset.card_le_card hsub).trans (card_nonInjectiveTuplesOn_le s k)
  · have he := Finset.card_filter_add_card_filter_not (s := H) (p := Function.Injective)
    simpa [homCountOn, injectiveHomCountOn, H, B, Finset.filter_filter, and_comm] using he.symm

/-- All homomorphisms of a simple pattern: the injective estimate plus one
explicit non-injective term. There is no diagonal-agreement hypothesis, and no
host-size premise silently absorbing the collision term into epsilon. -/
theorem abs_homCountOn_sub_le_of_simple
    (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V) (s : Finset V)
    {ε : ℝ} (hε : 0 ≤ ε) (hnull : NullaryCompatible M N) (hP : SimplePattern P)
    (hedit : ∀ S : RelSymbol L, 0 < (S.1 : ℕ) →
      (editDistance (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s) : ℝ) ≤
        ε * (s.card : ℝ) ^ (S.1 : ℕ)) :
    |(homCountOn P M s : ℝ) - homCountOn P N s| ≤
      patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k +
        (k.choose 2 : ℝ) * s.card ^ (k - 1) := by
  obtain ⟨a, ha, heqa⟩ := homCountOn_eq_injective_add_collision P M s
  obtain ⟨b, hb, heqb⟩ := homCountOn_eq_injective_add_collision P N s
  have hi := abs_sub_le_iff.mp (abs_injectiveHomCountOn_sub_le_of_simple P M N s hε hnull hP hedit)
  have ha' : (a : ℝ) ≤ (k.choose 2 : ℝ) * s.card ^ (k - 1) := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ (k.choose 2 : ℝ) * s.card ^ (k - 1) := by exact_mod_cast hb
  rw [heqa, heqb, Nat.cast_add, Nat.cast_add, abs_sub_le_iff]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]

omit [DecidableEq V] in
@[simp] theorem homCountOn_univ [Fintype V] (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) : homCountOn P M Finset.univ = homCount P M := by
  simp [homCountOn, homCount]

@[simp] theorem injectiveHomCountOn_univ [Fintype V] (P : FiniteRelModel L (Fin k))
    (M : FiniteRelModel L V) : injectiveHomCountOn P M Finset.univ = injectiveHomCount P M := by
  simp [injectiveHomCountOn, injectiveHomCount]

/-- Cellwise-error specialization of the induced transfer. Diagonal agreement
is still a separate premise, not a consequence of the cellwise bound. -/
theorem abs_inducedEmbeddingCountOn_sub_le_of_cellwise_diagonalAgreement
    (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V) (s : Finset V)
    (Q : Finpartition s) {ε : ℝ} (hε : 0 ≤ ε) (hnull : NullaryCompatible M N)
    (hdiag : DiagonalAgreementOn M N s) (hcell : CellwiseEditBound M N Q ε) :
    |(inducedEmbeddingCountOn P M (fun _ ↦ s) : ℝ) -
      inducedEmbeddingCountOn P N (fun _ ↦ s)| ≤
        patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k :=
  abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement P M N s hε hnull hdiag
    (fun S hS ↦ hcell.editDistance_const_le hS S.2)

/-- Cellwise-error specialization for preservation-only homomorphisms. The
non-injective contribution remains explicit, with no diagonal premise. -/
theorem abs_homCountOn_sub_le_of_cellwise_simple
    (P : FiniteRelModel L (Fin k)) (M N : FiniteRelModel L V) (s : Finset V)
    (Q : Finpartition s) {ε : ℝ} (hε : 0 ≤ ε) (hnull : NullaryCompatible M N)
    (hP : SimplePattern P) (hcell : CellwiseEditBound M N Q ε) :
    |(homCountOn P M s : ℝ) - homCountOn P N s| ≤
      patternAtomCoefficient L k * ε * (s.card : ℝ) ^ k +
        (k.choose 2 : ℝ) * s.card ^ (k - 1) :=
  abs_homCountOn_sub_le_of_simple P M N s hε hnull hP
    (fun S hS ↦ hcell.editDistance_const_le hS S.2)

end RegularityLemmata

#print axioms RegularityLemmata.abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement
#print axioms RegularityLemmata.abs_injectiveHomCountOn_sub_le_of_simple
#print axioms RegularityLemmata.abs_homCountOn_sub_le_of_simple
#print axioms RegularityLemmata.abs_inducedEmbeddingCountOn_sub_le_of_cellwise_diagonalAgreement
#print axioms RegularityLemmata.abs_homCountOn_sub_le_of_cellwise_simple
