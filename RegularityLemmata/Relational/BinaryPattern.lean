/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPalette

/-!
# Reducing binary induced structure to profiles and palettes

Phase 10 units 0–1 (design freeze in `ARCHITECTURE.md`): the arity discipline and the
**load-bearing reduction** turning relational induced embeddings into palette
bookkeeping.

`AtMostBinary L` records that `L` has no relation symbol of arity `> 2` (as a Prop,
not via the loose stored `arityBound`). Under it, for **any** `f`,
`PreservesAndReflects P M f` is equivalent to three concrete conditions
(`preservesAndReflects_iff_profiles_palettes`): nullary compatibility, agreement of
every vertex profile along `f`, and agreement of every pair palette on distinct
indices. (Injectivity is the intended domain — supplied by
`inducedEmbeddingCountOn`'s filter — but the equivalence needs it nowhere.) Every later
pattern-specific count is then bookkeeping over the palette machinery rather than model
theory.

`inducedEmbeddingCountOn P M A` counts induced embeddings landing in a prescribed box
`A : W → Finset V`, with box monotonicity, automatic injectivity on disjoint boxes,
and the vanishing under a nullary or profile mismatch.

`preservesAndReflects_transport` reads the reduction the other way: two maps into the SAME
model realize the same patterns once they agree coordinatewise on profiles and on
distinct-index palettes. It assumes neither injectivity nor any symmetry of the palette.
`preservesAndReflects_transport_three` is the `Fin 3` form in which only the three FORWARD
pairs are exhibited, the reverse three coming from `binaryPairPalette_swap`.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

/-- A finite relational language with no relation symbol of arity greater than two. -/
class AtMostBinary (L : FirstOrder.Language) : Prop where
  /-- No relation symbol above arity two. -/
  relationsEmptyAboveTwo : ∀ n, 2 < n → IsEmpty (L.Relations n)

theorem isEmpty_relations_of_two_lt (L : FirstOrder.Language) [AtMostBinary L] {n : ℕ}
    (h : 2 < n) : IsEmpty (L.Relations n) :=
  AtMostBinary.relationsEmptyAboveTwo n h

variable {L : FirstOrder.Language} [FiniteRelational L] {V W : Type*}

/-- Nullary relations agree between pattern and host. -/
def NullaryCompatible (P : FiniteRelModel L W) (M : FiniteRelModel L V) : Prop :=
  ∀ R : L.Relations 0, P.Holds R Fin.elim0 ↔ M.Holds R Fin.elim0

/-! ### Tuple bookkeeping -/

private theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem eq_cons_one {α : Type*} (x : Fin 1 → α) : x = ![x 0] := by
  funext i; fin_cases i; rfl

private theorem eq_cons_two {α : Type*} (x : Fin 2 → α) : x = ![x 0, x 1] := by
  funext i; fin_cases i <;> rfl

private theorem comp_cons_two {α β : Type*} (f : α → β) (a b : α) :
    f ∘ ![a, b] = ![f a, f b] := by
  funext i; fin_cases i <;> rfl

private theorem comp_cons_one {α β : Type*} (f : α → β) (a : α) :
    f ∘ ![a] = ![f a] := by
  funext i; fin_cases i; rfl

/-! ### The reduction -/

/-- **The load-bearing reduction.** For **any** `f`, preservation-and-reflection is
exactly nullary compatibility, vertex-profile agreement, and pair-palette agreement on
distinct indices (injectivity, the intended domain, is not needed). -/
theorem preservesAndReflects_iff_profiles_palettes [AtMostBinary L]
    {P : FiniteRelModel L W} {M : FiniteRelModel L V} {f : W → V} :
    PreservesAndReflects P M f ↔ NullaryCompatible P M ∧
      (∀ i, binaryVertexProfile P i = binaryVertexProfile M (f i)) ∧
      (∀ i j, i ≠ j →
        binaryPairPalette P i j = binaryPairPalette M (f i) (f j)) := by
  rw [preservesAndReflects_iff_forall]
  constructor
  · intro h
    refine ⟨fun R => ?_, fun i => ?_, fun i j hij => ?_⟩
    · have hcomp : f ∘ (Fin.elim0 : Fin 0 → W) = Fin.elim0 := Subsingleton.elim _ _
      have := h R Fin.elim0
      rwa [hcomp] at this
    · refine Prod.ext (funext fun U => ?_) (funext fun R => ?_)
      · exact bool_eq_of_iff (by have := h U ![i]; rwa [comp_cons_one] at this)
      · exact bool_eq_of_iff (by have := h R ![i, i]; rwa [comp_cons_two] at this)
    · refine funext fun R => Prod.ext ?_ ?_
      · exact bool_eq_of_iff (by have := h R ![i, j]; rwa [comp_cons_two] at this)
      · exact bool_eq_of_iff (by have := h R ![j, i]; rwa [comp_cons_two] at this)
  · rintro ⟨hnull, hprof, hpal⟩ n R x
    match n, R, x with
    | 0, R, x =>
      have hfx : f ∘ x = Fin.elim0 := Subsingleton.elim _ _
      rw [hfx, Subsingleton.elim x Fin.elim0]
      exact hnull R
    | 1, R, x =>
      rw [eq_cons_one x, comp_cons_one]
      have hprofR : P.rel R ![x 0] = M.rel R ![f (x 0)] :=
        congrFun (congrArg Prod.fst (hprof (x 0))) R
      show P.rel R ![x 0] = true ↔ M.rel R ![f (x 0)] = true
      rw [hprofR]
    | 2, R, x =>
      rw [eq_cons_two x, comp_cons_two]
      by_cases hxeq : x 0 = x 1
      · have hprofLoop : P.rel R ![x 0, x 0] = M.rel R ![f (x 0), f (x 0)] :=
          congrFun (congrArg Prod.snd (hprof (x 0))) R
        show P.rel R ![x 0, x 1] = true ↔ M.rel R ![f (x 0), f (x 1)] = true
        rw [← hxeq, hprofLoop]
      · have h1 : P.rel R ![x 0, x 1] = M.rel R ![f (x 0), f (x 1)] :=
          congrArg Prod.fst (congrFun (hpal (x 0) (x 1) hxeq) R)
        show P.rel R ![x 0, x 1] = true ↔ M.rel R ![f (x 0), f (x 1)] = true
        rw [h1]
    | (n + 3), R, _ =>
      haveI := isEmpty_relations_of_two_lt L (show 2 < n + 3 by omega)
      exact isEmptyElim R

/-! ### Same-host transport

Two maps into the SAME model realize the same patterns as soon as they agree
coordinatewise on the data the reduction above sees: vertex profiles, and pair palettes at
distinct indices. Neither injectivity nor any symmetry hypothesis is needed — the palette
may be symmetric or not, and the statement is about agreement, not about the palette's
shape. -/

/-- **Same-host transport.** If `f` and `g` agree coordinatewise on vertex profiles and on
pair palettes at distinct indices, they realize exactly the same patterns of `M`. Nullary
compatibility does not mention the map, so it transfers unchanged. -/
theorem preservesAndReflects_transport [AtMostBinary L]
    {P : FiniteRelModel L W} {M : FiniteRelModel L V} {f g : W → V}
    (hprof : ∀ i, binaryVertexProfile M (f i) = binaryVertexProfile M (g i))
    (hpal : ∀ i j, i ≠ j →
      binaryPairPalette M (f i) (f j) = binaryPairPalette M (g i) (g j)) :
    PreservesAndReflects P M f ↔ PreservesAndReflects P M g := by
  rw [preservesAndReflects_iff_profiles_palettes, preservesAndReflects_iff_profiles_palettes]
  constructor
  · rintro ⟨hn, hp, hq⟩
    exact ⟨hn, fun i => (hp i).trans (hprof i),
      fun i j hij => (hq i j hij).trans (hpal i j hij)⟩
  · rintro ⟨hn, hp, hq⟩
    exact ⟨hn, fun i => (hp i).trans (hprof i).symm,
      fun i j hij => (hq i j hij).trans (hpal i j hij).symm⟩

/-- **The three-vertex ordered corollary.** For a `Fin 3` index the six distinct-index
palette hypotheses collapse to the three FORWARD pairs: the reversal law
`binaryPairPalette_swap` supplies the other three. This is the form an ordered-orbit
argument uses, where only `(0,1)`, `(0,2)`, `(1,2)` are exhibited. -/
theorem preservesAndReflects_transport_three [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {f g : Fin 3 → V}
    (hprof : ∀ i, binaryVertexProfile M (f i) = binaryVertexProfile M (g i))
    (h01 : binaryPairPalette M (f 0) (f 1) = binaryPairPalette M (g 0) (g 1))
    (h02 : binaryPairPalette M (f 0) (f 2) = binaryPairPalette M (g 0) (g 2))
    (h12 : binaryPairPalette M (f 1) (f 2) = binaryPairPalette M (g 1) (g 2)) :
    PreservesAndReflects P M f ↔ PreservesAndReflects P M g := by
  refine preservesAndReflects_transport hprof ?_
  have hswap : ∀ a b : Fin 3,
      binaryPairPalette M (f a) (f b) = binaryPairPalette M (g a) (g b) →
      binaryPairPalette M (f b) (f a) = binaryPairPalette M (g b) (g a) := by
    intro a b h
    rw [binaryPairPalette_swap M (f a) (f b), binaryPairPalette_swap M (g a) (g b), h]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact h01
    | exact h02
    | exact h12
    | exact hswap 0 1 h01
    | exact hswap 0 2 h02
    | exact hswap 1 2 h12

/-! ### Box-restricted induced counts -/

variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-- Induced embeddings landing in a prescribed box `A : W → Finset V`. -/
def inducedEmbeddingCountOn (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    (A : W → Finset V) : ℕ :=
  ((Fintype.piFinset A).filter fun f =>
    Function.Injective f ∧ PreservesAndReflects P M f).card

/-- On a finite carrier, the count over the full box `fun _ ↦ univ` is `inducedEmbeddingCount`. -/
theorem inducedEmbeddingCountOn_univ (P : FiniteRelModel L W) (M : FiniteRelModel L V) :
    inducedEmbeddingCountOn P M (fun _ : W => Finset.univ) = inducedEmbeddingCount P M := by
  rw [inducedEmbeddingCountOn, inducedEmbeddingCount, Fintype.piFinset_univ]

omit [Fintype V] in
/-- **The restricted falling-factorial ceiling.** Induced embeddings into the box `fun _ ↦ s` are
injective tuples through `s`, so their number is at most `(|s|)_{|W|}`
(`card_injectiveTuplesOn`). This is the `c ≤ (|s|)_k` hypothesis of the normalization
conversion `div_descFactorial_sub_div_pow_le`. -/
theorem inducedEmbeddingCountOn_le_descFactorial (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    (s : Finset V) :
    inducedEmbeddingCountOn P M (fun _ => s) ≤ s.card.descFactorial (Fintype.card W) := by
  rw [inducedEmbeddingCountOn, ← card_injectiveTuplesOn (ι := W) s]
  exact Finset.card_le_card fun f hf => by
    rw [Finset.mem_filter] at hf
    exact Finset.mem_filter.mpr ⟨hf.1, hf.2.1⟩

omit [Fintype V] in
/-- Box monotonicity. -/
theorem inducedEmbeddingCountOn_mono (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    {A B : W → Finset V} (h : ∀ w, A w ⊆ B w) :
    inducedEmbeddingCountOn P M A ≤ inducedEmbeddingCountOn P M B := by
  refine Finset.card_le_card fun g hg => ?_
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hg ⊢
  exact ⟨fun w => h w (hg.1 w), hg.2⟩

omit [Fintype V] in
/-- On pairwise-disjoint boxes, injectivity is automatic, so the induced count is the
count of preservation-and-reflection maps. -/
theorem inducedEmbeddingCountOn_of_disjoint (P : FiniteRelModel L W)
    (M : FiniteRelModel L V) {A : W → Finset V}
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    inducedEmbeddingCountOn P M A
      = ((Fintype.piFinset A).filter fun f => PreservesAndReflects P M f).card := by
  refine congrArg Finset.card (Finset.filter_congr fun g hg => ?_)
  rw [Fintype.mem_piFinset] at hg
  rw [and_iff_right_iff_imp]
  intro _ i j hij
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj i j hne) (hg i) (hij ▸ hg j)

omit [Fintype V] in
/-- A nullary incompatibility forces the induced count to zero. -/
theorem inducedEmbeddingCountOn_eq_zero_of_not_nullaryCompatible [AtMostBinary L]
    {P : FiniteRelModel L W} {M : FiniteRelModel L V} {A : W → Finset V}
    (h : ¬NullaryCompatible P M) : inducedEmbeddingCountOn P M A = 0 := by
  rw [inducedEmbeddingCountOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g hg ⟨hinj, hpar⟩
  exact h ((preservesAndReflects_iff_profiles_palettes).mp hpar).1

omit [Fintype V] in
/-- A vertex-profile mismatch forces the induced count to zero. -/
theorem inducedEmbeddingCountOn_eq_zero_of_profile_mismatch [AtMostBinary L]
    {P : FiniteRelModel L W} {M : FiniteRelModel L V} {A : W → Finset V} {i : W}
    (h : ∀ v ∈ A i, binaryVertexProfile P i ≠ binaryVertexProfile M v) :
    inducedEmbeddingCountOn P M A = 0 := by
  rw [inducedEmbeddingCountOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g hg ⟨hinj, hpar⟩
  rw [Fintype.mem_piFinset] at hg
  exact h (g i) (hg i)
    (((preservesAndReflects_iff_profiles_palettes).mp hpar).2.1 i)

/-! ### Tests and adversarial examples -/

instance : AtMostBinary (singleRelLang 2) :=
  ⟨fun _n hn => isEmpty_relations_of_lt _ hn⟩

instance (K : ℕ) : AtMostBinary (coloredRelLang 2 K) :=
  ⟨fun _n hn => isEmpty_relations_of_lt _ hn⟩

instance : AtMostBinary FirstOrder.Language.empty :=
  ⟨fun _n _ => inferInstance⟩

section Tests

open FiniteRelModel

/-- A one-binary-symbol test model. -/
private def binModel {V : Type*} [DecidableEq V] (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- A profile mismatch (loop differs) forces the induced count to zero.
example :
    inducedEmbeddingCountOn (binModel (V := Fin 1) fun a b => decide (a = b))
      (binModel (V := Fin 1) fun _ _ => false) (fun _ => Finset.univ) = 0 := by
  refine inducedEmbeddingCountOn_eq_zero_of_profile_mismatch (i := 0) ?_
  decide

-- The reduction, as a statement-level instance.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3))
    (M : FiniteRelModel (singleRelLang 2) (Fin 5)) (f : Fin 3 → Fin 5) :
    PreservesAndReflects P M f ↔ NullaryCompatible P M ∧
      (∀ i, binaryVertexProfile P i = binaryVertexProfile M (f i)) ∧
      (∀ i j, i ≠ j →
        binaryPairPalette P i j = binaryPairPalette M (f i) (f j)) :=
  preservesAndReflects_iff_profiles_palettes

/-! #### Same-host transport -/

/-- A SYMMETRIC palette: `a ≠ b` in both directions. -/
private abbrev symModel : FiniteRelModel (singleRelLang 2) (Fin 4) :=
  binModel fun a b => decide (a ≠ b)

/-- A NON-SYMMETRIC palette: the strict order, the adversarial case. -/
private abbrev ordModel : FiniteRelModel (singleRelLang 2) (Fin 6) :=
  binModel fun a b => decide (a < b)

-- Transport applies to a SYMMETRIC palette: nothing in the lemma asks for asymmetry.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P symModel ![0, 1, 2] ↔ PreservesAndReflects P symModel ![1, 2, 3] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- …and to a NON-SYMMETRIC one, where it reproduces the orientation probe's positive result
-- (`Relational/OrientationProbe.lean`) for EVERY pattern at once, rather than one pattern
-- at a time by `decide`.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P ordModel ![0, 1, 2] ↔ PreservesAndReflects P ordModel ![3, 4, 5] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

-- The adversarial reversed orientation is excluded at the hypothesis: the forward palette
-- disagrees, so transport does not apply — which is exactly the right failure mode.
example :
    binaryPairPalette ordModel (![0, 1, 2] 0) (![0, 1, 2] 1)
      ≠ binaryPairPalette ordModel (![5, 4, 3] 0) (![5, 4, 3] 1) := by decide

-- Transport needs no injectivity: a constant map transports against itself, and against
-- any other map agreeing on profiles and (vacuously distinct-index) palettes.
example (P : FiniteRelModel (singleRelLang 2) (Fin 3)) :
    PreservesAndReflects P symModel ![0, 0, 0] ↔ PreservesAndReflects P symModel ![1, 1, 1] :=
  preservesAndReflects_transport_three (by decide) (by decide) (by decide) (by decide)

end Tests

end RegularityLemmata
