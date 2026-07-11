/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.PatternCounts
import RegularityLemmata.Hypergraph.Copies

/-!
# Uniform and colored hypergraph adapters

Phase 8 unit 7b (design freeze in `ARCHITECTURE.md`): the point where ordered
first-order tuples meet unordered hyperedges. The relational core stays ordered;
these adapters make every noninjective tuple false.

* `FiniteRelModel.ofUniformHypergraph` interprets the single symbol of
  `singleRelLang r` as `H.orderedRel`, giving the visible count chain
  `injectiveRelationCount = relationCount = tupleCount H.orderedRel … = r!·#edges`
  (via `UniformHypergraph.orderedCount_eq`).
* `coloredRelLang r K` has one arity-`r` relation symbol per color;
  `FiniteRelModel.ofColoredHypergraph` interprets color `c` as
  `(H.colorClass c).orderedRel`. Every injective tuple satisfies exactly one color;
  no noninjective tuple satisfies any; and both pattern bridges to
  `ColoredHypergraph.copyCount` hold (`injectiveHomCount_ofColoredHypergraph`,
  `inducedEmbeddingCount_ofColoredHypergraph`) — kept separate so the reason for
  the coincidence (totality forces color equality; reflection follows from
  uniqueness) is explicit.
-/

namespace RegularityLemmata

open FirstOrder UniformHypergraph

variable {V W : Type*}

namespace FiniteRelModel

/-! ### Uniform hypergraphs -/

/-- A uniform hypergraph as a relational model over `singleRelLang r`: the unique
relation is the ordered realization (so every noninjective tuple is false). -/
def ofUniformHypergraph [DecidableEq V] {r : ℕ} (H : UniformHypergraph r V) :
    FiniteRelModel (singleRelLang r) V where
  rel {n} _ x :=
    if h : n = r then decide (H.orderedRel fun i : Fin r => x (Fin.cast h.symm i))
    else false

@[simp] theorem ofUniformHypergraph_holds [DecidableEq V] {r : ℕ}
    (H : UniformHypergraph r V) (x : Fin r → V) :
    (ofUniformHypergraph H).Holds (singleRelSymbol r) x ↔ H.orderedRel x := by
  show (if h : r = r then decide (H.orderedRel fun i => x (Fin.cast h.symm i))
    else false) = true ↔ _
  rw [dif_pos rfl, decide_eq_true_eq]
  exact Iff.rfl

theorem not_ofUniformHypergraph_holds_of_not_injective [DecidableEq V] {r : ℕ}
    (H : UniformHypergraph r V) {x : Fin r → V} (hx : ¬Function.Injective x) :
    ¬(ofUniformHypergraph H).Holds (singleRelSymbol r) x := fun h =>
  hx ((ofUniformHypergraph_holds H x).mp h).1

variable [Fintype V] [DecidableEq V] {r : ℕ}

/-- The ordered relational count is the ordered realization count. -/
theorem relationCount_ofUniformHypergraph (H : UniformHypergraph r V) :
    relationCount (ofUniformHypergraph H) (singleRelSymbol r)
      = tupleCount H.orderedRel fun _ => Finset.univ := by
  rw [relationCount, relationCountOn, tupleCount, tupleCount]
  exact congrArg Finset.card
    (Finset.filter_congr fun v _ => ofUniformHypergraph_holds H v)

/-- The adapter falsifies every noninjective tuple, so the full ordered count
equals the injective count. -/
theorem relationCount_eq_injective_ofUniformHypergraph (H : UniformHypergraph r V) :
    relationCount (ofUniformHypergraph H) (singleRelSymbol r)
      = injectiveRelationCount (ofUniformHypergraph H) (singleRelSymbol r) :=
  relationCount_eq_injective_of_forall _ _ fun x hx =>
    ((ofUniformHypergraph_holds H x).mp hx).1

/-- **The visible count chain**: `injectiveRelationCount = r!·#edges`. -/
theorem injectiveRelationCount_ofUniformHypergraph (H : UniformHypergraph r V) :
    injectiveRelationCount (ofUniformHypergraph H) (singleRelSymbol r)
      = r.factorial * H.edges.card :=
  calc injectiveRelationCount (ofUniformHypergraph H) (singleRelSymbol r)
      = relationCount (ofUniformHypergraph H) (singleRelSymbol r) :=
        (relationCount_eq_injective_ofUniformHypergraph H).symm
    _ = tupleCount H.orderedRel (fun _ => Finset.univ) :=
        relationCount_ofUniformHypergraph H
    _ = r.factorial * H.edges.card := H.orderedCount_eq

/-- The injective relational density bridge. -/
theorem injectiveRelationDensity_ofUniformHypergraph (H : UniformHypergraph r V) :
    injectiveRelationDensity (ofUniformHypergraph H) (singleRelSymbol r)
      = (r.factorial : ℝ) * (H.edges.card : ℝ)
          / ((Fintype.card V).descFactorial r : ℝ) := by
  rw [injectiveRelationDensity, injectiveRelationCount_ofUniformHypergraph]
  push_cast
  ring

end FiniteRelModel

/-! ### Tests and adversarial examples (uniform) -/

section UniformTests

open FiniteRelModel

-- Complete 2-uniform hypergraph on Fin 3: both counts 6 (all ordered pairs of
-- distinct vertices).
example :
    injectiveRelationCount (ofUniformHypergraph (complete 2 (Fin 3)))
      (singleRelSymbol 2) = 6 := by
  rw [injectiveRelationCount_ofUniformHypergraph]
  decide

example :
    relationCount (ofUniformHypergraph (complete 2 (Fin 3))) (singleRelSymbol 2)
      = 6 := by
  rw [relationCount_eq_injective_ofUniformHypergraph,
    injectiveRelationCount_ofUniformHypergraph]
  decide

-- A 3-uniform hypergraph on Fin 2: both counts 0 (no 3-subset of a 2-set).
example :
    injectiveRelationCount (ofUniformHypergraph (complete 3 (Fin 2)))
      (singleRelSymbol 3) = 0 := by
  rw [injectiveRelationCount_ofUniformHypergraph]
  decide

-- An explicitly noninjective tuple never satisfies the adapter relation.
example :
    ¬(ofUniformHypergraph (complete 2 (Fin 3))).Holds (singleRelSymbol 2)
      (fun _ => 0) := by
  apply not_ofUniformHypergraph_holds_of_not_injective
  intro hinj
  exact absurd (@hinj 0 1 rfl) (by decide)

end UniformTests

/-! ### Colored hypergraphs -/

/-- The relational language with one arity-`r` relation symbol per color, encoded
as a color paired with a proof of the arity (so no arity below `r` and none above
carries a symbol, without any `cast`). -/
def coloredRelLang (r K : ℕ) : FirstOrder.Language :=
  ⟨fun _ => Empty, fun n => {_c : Fin K // n = r}⟩

instance (r K : ℕ) : FiniteRelational (coloredRelLang r K) where
  arityBound := r
  functionsEmpty := fun _ => inferInstanceAs (IsEmpty Empty)
  relationsFintype := fun n => inferInstanceAs (Fintype {_c : Fin K // n = r})
  relationsDecidableEq := fun n => inferInstanceAs (DecidableEq {_c : Fin K // n = r})
  relationsEmptyAbove := fun n hn => ⟨fun R => absurd R.2 (by omega)⟩

/-- The relation symbol for color `c`. -/
def coloredRelSymbol (r K : ℕ) (c : Fin K) : (coloredRelLang r K).Relations r :=
  ⟨c, rfl⟩

/-- The color carried by a symbol. -/
def colorOfSymbol {r K n : ℕ} (R : (coloredRelLang r K).Relations n) : Fin K :=
  R.1

@[simp] theorem colorOfSymbol_coloredRelSymbol {r K : ℕ} (c : Fin K) :
    colorOfSymbol (coloredRelSymbol r K c) = c := rfl

theorem coloredRelSymbol_colorOfSymbol {r K : ℕ}
    (R : (coloredRelLang r K).Relations r) :
    coloredRelSymbol r K (colorOfSymbol R) = R := rfl

theorem isEmpty_coloredRel_of_ne {r K n : ℕ} (h : n ≠ r) :
    IsEmpty ((coloredRelLang r K).Relations n) :=
  ⟨fun R => h R.2⟩

namespace FiniteRelModel

/-- A colored hypergraph as a relational model: color `c` is the ordered
realization of the color-`c` class (so every noninjective tuple is false). The
arity proof carried by the symbol removes any `cast`. -/
def ofColoredHypergraph [Fintype V] [DecidableEq V] {r K : ℕ}
    (H : ColoredHypergraph r K V) : FiniteRelModel (coloredRelLang r K) V where
  rel {_n} R x :=
    decide ((H.colorClass R.1).orderedRel fun i : Fin r => x (Fin.cast R.2.symm i))

@[simp] theorem ofColoredHypergraph_holds [Fintype V] [DecidableEq V] {r K : ℕ}
    (H : ColoredHypergraph r K V) (c : Fin K) (x : Fin r → V) :
    (ofColoredHypergraph H).Holds (coloredRelSymbol r K c) x
      ↔ (H.colorClass c).orderedRel x := by
  show decide ((H.colorClass c).orderedRel fun i => x (Fin.cast rfl i)) = true ↔ _
  rw [decide_eq_true_eq]
  exact Iff.rfl

theorem not_ofColoredHypergraph_holds_of_not_injective [Fintype V] [DecidableEq V]
    {r K : ℕ} (H : ColoredHypergraph r K V) (c : Fin K) {x : Fin r → V}
    (hx : ¬Function.Injective x) :
    ¬(ofColoredHypergraph H).Holds (coloredRelSymbol r K c) x := fun h =>
  hx ((ofColoredHypergraph_holds H c x).mp h).1

end FiniteRelModel

namespace FiniteRelModel

variable [Fintype V] [DecidableEq V] {r K : ℕ}

/-- The ordered relational count of color `c` is the ordered realization count of
its color class. -/
theorem relationCount_ofColoredHypergraph (H : ColoredHypergraph r K V) (c : Fin K) :
    relationCount (ofColoredHypergraph H) (coloredRelSymbol r K c)
      = tupleCount (H.colorClass c).orderedRel fun _ => Finset.univ := by
  rw [relationCount, relationCountOn, tupleCount, tupleCount]
  exact congrArg Finset.card
    (Finset.filter_congr fun v _ => ofColoredHypergraph_holds H c v)

/-- **Per-color count**: color `c` has `r!·#(color-c edges)` injective realizations,
and (no noninjective tuple realizes it) the same ordered count. -/
theorem injectiveRelationCount_ofColoredHypergraph (H : ColoredHypergraph r K V)
    (c : Fin K) :
    injectiveRelationCount (ofColoredHypergraph H) (coloredRelSymbol r K c)
      = r.factorial * (H.colorClass c).edges.card :=
  calc injectiveRelationCount (ofColoredHypergraph H) (coloredRelSymbol r K c)
      = relationCount (ofColoredHypergraph H) (coloredRelSymbol r K c) :=
        (relationCount_eq_injective_of_forall _ _ fun x hx =>
          ((ofColoredHypergraph_holds H c x).mp hx).1).symm
    _ = tupleCount (H.colorClass c).orderedRel (fun _ => Finset.univ) :=
        relationCount_ofColoredHypergraph H c
    _ = r.factorial * (H.colorClass c).edges.card := (H.colorClass c).orderedCount_eq

/-- **Partition of the injective tuples over colors**: summing the per-color
injective counts recovers the total injective-tuple count. -/
theorem sum_injectiveRelationCount_ofColoredHypergraph
    (H : ColoredHypergraph r K V) :
    ∑ c : Fin K,
        injectiveRelationCount (ofColoredHypergraph H) (coloredRelSymbol r K c)
      = injectiveTupleCount V r := by
  rw [Finset.sum_congr rfl fun c _ => injectiveRelationCount_ofColoredHypergraph H c,
    ← Finset.mul_sum, H.sum_card_colorClass, injectiveTupleCount_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]

end FiniteRelModel

/-! ### The colored pattern bridges -/

namespace FiniteRelModel

variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {r K : ℕ}

omit [Fintype W] [Fintype V] in
private theorem tupleRange_comp {f : W → V} {x : Fin r → W} :
    tupleRange (f ∘ x) = (tupleRange x).image f := by
  rw [tupleRange, tupleRange, Finset.image_image]

/-- `Preserves` between colored adapters means every color transports along `f`. -/
theorem preserves_ofColoredHypergraph_iff (P : ColoredHypergraph r K W)
    (H : ColoredHypergraph r K V) (f : W → V) :
    Preserves (ofColoredHypergraph P) (ofColoredHypergraph H) f
      ↔ ∀ (c : Fin K) (x : Fin r → W),
          (P.colorClass c).orderedRel x → (H.colorClass c).orderedRel (f ∘ x) := by
  constructor
  · intro hp c x hx
    have hh := (preserves_iff_forall _ _ _).mp hp (coloredRelSymbol r K c) x
    rw [ofColoredHypergraph_holds, ofColoredHypergraph_holds] at hh
    exact hh hx
  · intro hall
    rw [preserves_iff_forall]
    intro n R y hR
    by_cases h : n = r
    · subst h
      rw [← coloredRelSymbol_colorOfSymbol R] at hR ⊢
      rw [ofColoredHypergraph_holds] at hR
      rw [ofColoredHypergraph_holds]
      exact hall _ y hR
    · exact absurd R.2 h

/-- `PreservesAndReflects` between colored adapters means every color transports in
both directions. -/
theorem preservesAndReflects_ofColoredHypergraph_iff (P : ColoredHypergraph r K W)
    (H : ColoredHypergraph r K V) (f : W → V) :
    PreservesAndReflects (ofColoredHypergraph P) (ofColoredHypergraph H) f
      ↔ ∀ (c : Fin K) (x : Fin r → W),
          (P.colorClass c).orderedRel x ↔ (H.colorClass c).orderedRel (f ∘ x) := by
  constructor
  · intro hp c x
    have hh := (preservesAndReflects_iff_forall _ _ _).mp hp (coloredRelSymbol r K c) x
    rw [ofColoredHypergraph_holds, ofColoredHypergraph_holds] at hh
    exact hh
  · intro hall
    rw [preservesAndReflects_iff_forall]
    intro n R y
    by_cases h : n = r
    · subst h
      rw [← coloredRelSymbol_colorOfSymbol R, ofColoredHypergraph_holds,
        ofColoredHypergraph_holds]
      exact hall _ y
    · exact absurd R.2 h

/-- The copy-count condition: the `H`-color of every `f`-image equals the `P`-color
of its source `r`-set. -/
private def CopyCond (P : ColoredHypergraph r K W) (H : ColoredHypergraph r K V)
    (f : W → V) : Prop :=
  ∀ (e : RSet r W) (h : (e.1.image f).card = r),
    H.coloring ⟨e.1.image f, h⟩ = P.coloring e

/-- Color preservation is the copy-count condition (for injective `f`). Totality of
the coloring is what makes preservation determine every color. -/
theorem preservesColors_iff_copyCond {P : ColoredHypergraph r K W}
    {H : ColoredHypergraph r K V} {f : W → V} (hinj : Function.Injective f) :
    (∀ (c : Fin K) (x : Fin r → W),
        (P.colorClass c).orderedRel x → (H.colorClass c).orderedRel (f ∘ x))
      ↔ CopyCond P H f := by
  constructor
  · intro hpres e he
    obtain ⟨x, hxinj, hxrange⟩ :
        ∃ x : Fin r → W, Function.Injective x ∧ tupleRange x = e.1 := by
      have hpos : 0 < ((Finset.univ : Finset (Fin r → W)).filter
          fun v => Function.Injective v ∧ tupleRange v = e.1).card := by
        rw [card_injective_tuples_range_eq e.2]
        exact Nat.factorial_pos r
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hx
      exact ⟨x, hx.2⟩
    have hcard_x : (tupleRange x).card = r := by rw [hxrange]; exact e.2
    have hx_ord : (P.colorClass (P.coloring e)).orderedRel x := by
      refine ⟨hxinj, ?_⟩
      rw [ColoredHypergraph.mem_colorClass]
      refine ⟨hcard_x, ?_⟩
      rw [show (⟨tupleRange x, hcard_x⟩ : RSet r W) = e from Subtype.ext hxrange]
    obtain ⟨-, hfx_mem⟩ := hpres (P.coloring e) x hx_ord
    rw [ColoredHypergraph.mem_colorClass] at hfx_mem
    obtain ⟨hcard_fx, hcolor_fx⟩ := hfx_mem
    have himg : tupleRange (f ∘ x) = e.1.image f := by rw [tupleRange_comp, hxrange]
    rw [show (⟨e.1.image f, he⟩ : RSet r V) = ⟨tupleRange (f ∘ x), hcard_fx⟩ from
      Subtype.ext himg.symm]
    exact hcolor_fx
  · intro hcopy c x hx
    obtain ⟨hxinj, hxmem⟩ := hx
    rw [ColoredHypergraph.mem_colorClass] at hxmem
    obtain ⟨hcard_x, hcolor_x⟩ := hxmem
    refine ⟨hinj.comp hxinj, ?_⟩
    rw [ColoredHypergraph.mem_colorClass]
    have hcard_fx : (tupleRange (f ∘ x)).card = r := by
      rw [tupleRange_comp, Finset.card_image_of_injective _ hinj, hcard_x]
    refine ⟨hcard_fx, ?_⟩
    have he : ((tupleRange x).image f).card = r := by
      rw [Finset.card_image_of_injective _ hinj, hcard_x]
    have hcopy' := hcopy ⟨tupleRange x, hcard_x⟩ he
    rw [hcolor_x] at hcopy'
    rw [show (⟨tupleRange (f ∘ x), hcard_fx⟩ : RSet r V) = ⟨(tupleRange x).image f, he⟩
      from Subtype.ext tupleRange_comp]
    exact hcopy'

/-- Color preservation-and-reflection is the copy-count condition (for injective
`f`). Reflection is free from uniqueness of the transported color. -/
theorem reflectsColors_iff_copyCond {P : ColoredHypergraph r K W}
    {H : ColoredHypergraph r K V} {f : W → V} (hinj : Function.Injective f) :
    (∀ (c : Fin K) (x : Fin r → W),
        (P.colorClass c).orderedRel x ↔ (H.colorClass c).orderedRel (f ∘ x))
      ↔ CopyCond P H f := by
  constructor
  · intro hrefl
    exact (preservesColors_iff_copyCond hinj).mp fun c x hx => (hrefl c x).mp hx
  · intro hcopy c x
    refine ⟨(preservesColors_iff_copyCond hinj).mpr hcopy c x, ?_⟩
    intro hfx
    obtain ⟨hfxinj, hfxmem⟩ := hfx
    have hxinj : Function.Injective x := hfxinj.of_comp
    rw [ColoredHypergraph.mem_colorClass] at hfxmem
    obtain ⟨hcard_fx, hcolor_fx⟩ := hfxmem
    refine ⟨hxinj, ?_⟩
    rw [ColoredHypergraph.mem_colorClass]
    have hcard_x : (tupleRange x).card = r := card_tupleRange_of_injective hxinj
    refine ⟨hcard_x, ?_⟩
    have he : ((tupleRange x).image f).card = r := by
      rw [Finset.card_image_of_injective _ hinj, hcard_x]
    have hcopy' := hcopy ⟨tupleRange x, hcard_x⟩ he
    rw [show (⟨(tupleRange x).image f, he⟩ : RSet r V) = ⟨tupleRange (f ∘ x), hcard_fx⟩
      from Subtype.ext tupleRange_comp.symm, hcolor_fx] at hcopy'
    exact hcopy'.symm

/-- **The copy-count bridge (injective homomorphisms).** For total colorings,
preserving every color already forces color equality. -/
theorem injectiveHomCount_ofColoredHypergraph (P : ColoredHypergraph r K W)
    (H : ColoredHypergraph r K V) :
    injectiveHomCount (ofColoredHypergraph P) (ofColoredHypergraph H)
      = ColoredHypergraph.copyCount P H := by
  rw [injectiveHomCount, ColoredHypergraph.copyCount]
  refine congrArg Finset.card
    (Finset.filter_congr fun f _ => and_congr_right fun hinj => ?_)
  rw [preserves_ofColoredHypergraph_iff]
  exact preservesColors_iff_copyCond hinj

/-- **The copy-count bridge (induced embeddings).** Reflection follows from
uniqueness, so the induced count coincides with the copy count. -/
theorem inducedEmbeddingCount_ofColoredHypergraph (P : ColoredHypergraph r K W)
    (H : ColoredHypergraph r K V) :
    inducedEmbeddingCount (ofColoredHypergraph P) (ofColoredHypergraph H)
      = ColoredHypergraph.copyCount P H := by
  rw [inducedEmbeddingCount, ColoredHypergraph.copyCount]
  refine congrArg Finset.card
    (Finset.filter_congr fun f _ => and_congr_right fun hinj => ?_)
  rw [preservesAndReflects_ofColoredHypergraph_iff]
  exact reflectsColors_iff_copyCond hinj

end FiniteRelModel

/-! ### Tests and adversarial examples (colored) -/

section ColoredTests

open FiniteRelModel

-- A model for a language with no relation symbols (K = 0).
example : FiniteRelModel (coloredRelLang 3 0) (Fin 2) :=
  ofColoredHypergraph (⟨fun e => absurd e.2 (by
    have := Finset.card_le_card (Finset.subset_univ e.1)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega)⟩ : ColoredHypergraph 3 0 (Fin 2))

-- On the parity pair-coloring of Fin 3, an injective tuple realizes exactly one of
-- the two colors.
example :
    (ofColoredHypergraph (⟨fun e => if 2 ∣ e.1.sum (fun x => (x : ℕ)) then 0 else 1⟩ :
        ColoredHypergraph 2 2 (Fin 3))).Holds (coloredRelSymbol 2 2 0) ![0, 2]
      ∧ ¬(ofColoredHypergraph (⟨fun e => if 2 ∣ e.1.sum (fun x => (x : ℕ)) then 0
        else 1⟩ : ColoredHypergraph 2 2 (Fin 3))).Holds (coloredRelSymbol 2 2 1)
        ![0, 2] := by
  refine ⟨by decide, by decide⟩

-- A noninjective tuple realizes no color.
example :
    ¬(ofColoredHypergraph (⟨fun e => if 2 ∣ e.1.sum (fun x => (x : ℕ)) then 0 else 1⟩ :
      ColoredHypergraph 2 2 (Fin 3))).Holds (coloredRelSymbol 2 2 0) ![0, 0] := by
  decide

-- A small colored copy-count bridge closes by decide: colored copies of the
-- edge-graph of ⊤ on Fin 2 into ⊤ on Fin 3 number 6, through the induced count.
example :
    inducedEmbeddingCount
        (ofColoredHypergraph (ColoredHypergraph.ofSimpleGraph (⊤ : SimpleGraph (Fin 2))))
        (ofColoredHypergraph (ColoredHypergraph.ofSimpleGraph (⊤ : SimpleGraph (Fin 3))))
      = 6 := by
  rw [inducedEmbeddingCount_ofColoredHypergraph, ColoredHypergraph.copyCount_ofSimpleGraph]
  decide

end ColoredTests

end RegularityLemmata
