/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.PatternCounts
import RegularityLemmata.Hypergraph.Copies
import RegularityLemmata.Finite.PairDensity
import Mathlib.ModelTheory.Graph

/-!
# The simple-graph adapter

Phase 8 unit 7a (design freeze in `ARCHITECTURE.md`): mathlib's graph language
(`FirstOrder.Language.graph`, `Mathlib.ModelTheory.Graph`) — no second graph
language is introduced — made finite relational, with `FiniteRelModel.ofSimpleGraph`
interpreting the adjacency symbol Boolean-computably. Relation truth is exactly
adjacency (`ofSimpleGraph_holds_adj`); the explicit structure agrees pointwise with
mathlib's `SimpleGraph.structure` (`ofSimpleGraph_toStructure_relMap`); diagonal
tuples are false by looplessness; the ordered adjacency count is the existing
`pairCount`; and induced relational embeddings agree with the existing induced
graph-copy notion (`inducedEmbeddingCount_ofSimpleGraph`).
-/

namespace RegularityLemmata

open FirstOrder

/-- Mathlib's graph language is finite relational (bound `2`). -/
instance : FiniteRelational FirstOrder.Language.graph where
  arityBound := 2
  functionsEmpty := fun _ => inferInstanceAs (IsEmpty Empty)
  relationsFintype := fun n =>
    match n with
    | 0 => ⟨∅, fun r => nomatch r⟩
    | 1 => ⟨∅, fun r => nomatch r⟩
    | 2 => ⟨{FirstOrder.Language.graphRel.adj}, fun r => by
        cases r
        exact Finset.mem_singleton_self _⟩
    | (_ + 3) => ⟨∅, fun r => nomatch r⟩
  relationsDecidableEq := fun n =>
    inferInstanceAs (DecidableEq (FirstOrder.Language.graphRel n))
  relationsEmptyAbove := fun n hn =>
    ⟨fun r => by cases r; omega⟩

namespace FiniteRelModel

variable {V W : Type*}

/-- A simple graph as a computable relational model over mathlib's graph
language. -/
def ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    FiniteRelModel FirstOrder.Language.graph V :=
  ⟨fun {_} R x =>
    match R with
    | .adj => decide (G.Adj (x 0) (x 1))⟩

@[simp] theorem ofSimpleGraph_holds_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Fin 2 → V) :
    (ofSimpleGraph G).Holds FirstOrder.Language.adj x ↔ G.Adj (x 0) (x 1) := by
  show decide (G.Adj (x 0) (x 1)) = true ↔ _
  exact decide_eq_true_iff

/-- Pointwise compatibility with mathlib's `SimpleGraph.structure`. -/
theorem ofSimpleGraph_toStructure_relMap (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (R : FirstOrder.Language.graph.Relations n) (x : Fin n → V) :
    @FirstOrder.Language.Structure.RelMap _ V (ofSimpleGraph G).toStructure n R x
      ↔ @FirstOrder.Language.Structure.RelMap _ V G.structure n R x := by
  cases R
  show (ofSimpleGraph G).Holds FirstOrder.Language.adj x ↔ G.Adj (x 0) (x 1)
  exact ofSimpleGraph_holds_adj G x

/-- Diagonal tuples are false, by looplessness. -/
theorem not_ofSimpleGraph_holds_diagonal (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) :
    ¬(ofSimpleGraph G).Holds FirstOrder.Language.adj fun _ => v := by
  rw [ofSimpleGraph_holds_adj]
  exact fun h => G.irrefl h

/-- The ordered adjacency count is the existing `pairCount`. -/
theorem relationCount_ofSimpleGraph [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    relationCount (ofSimpleGraph G) FirstOrder.Language.adj
      = pairCount G.Adj Finset.univ Finset.univ := by
  rw [relationCount, relationCountOn, tupleCount, card_filter_piFinset_two,
    pairCount]
  refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
  rw [ofSimpleGraph_holds_adj]
  exact Iff.rfl

/-! ### The induced-copy bridge -/

private theorem tupleRange_two {α : Type*} [DecidableEq α] (x : Fin 2 → α) :
    tupleRange x = {x 0, x 1} := by
  rw [tupleRange]
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem mem_ofSimpleGraph_pair [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V} (hab : a ≠ b) :
    {a, b} ∈ (UniformHypergraph.ofSimpleGraph G).edges ↔ G.Adj a b := by
  rw [UniformHypergraph.mem_ofSimpleGraph]
  constructor
  · rintro ⟨c, d, hcd, he⟩
    have ha : a ∈ ({c, d} : Finset V) := he ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ ({c, d} : Finset V) :=
      he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hcd
    · exact hcd.symm
    · exact absurd rfl hab
  · intro h
    exact ⟨a, b, h, rfl⟩

/-- **The induced-copy bridge**: induced relational embeddings between graph
adapters are exactly the induced graph copies of the edge hypergraphs. -/
theorem inducedEmbeddingCount_ofSimpleGraph [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G₁ : SimpleGraph W) [DecidableRel G₁.Adj]
    (G₂ : SimpleGraph V) [DecidableRel G₂.Adj] :
    inducedEmbeddingCount (ofSimpleGraph G₁) (ofSimpleGraph G₂)
      = UniformHypergraph.inducedCopyCount (UniformHypergraph.ofSimpleGraph G₁)
          (UniformHypergraph.ofSimpleGraph G₂) := by
  classical
  rw [inducedEmbeddingCount, UniformHypergraph.inducedCopyCount]
  refine congrArg Finset.card
    (Finset.filter_congr fun f _ => and_congr_right fun hinj => ?_)
  constructor
  · intro h e he
    have he2 := (Finset.mem_powersetCard.mp he).2
    obtain ⟨x, hxinj, hxrange⟩ :
        ∃ x : Fin 2 → W, Function.Injective x ∧ tupleRange x = e := by
      have hpos : 0 < ((Finset.univ : Finset (Fin 2 → W)).filter
          fun v => Function.Injective v ∧ tupleRange v = e).card := by
        rw [UniformHypergraph.card_injective_tuples_range_eq he2]
        exact Nat.factorial_pos 2
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hx
      exact ⟨x, hx.2⟩
    have hne : x 0 ≠ x 1 := fun hx01 => absurd (hxinj hx01) (by decide)
    have hs : (ofSimpleGraph G₁).Holds FirstOrder.Language.adj x
        ↔ (ofSimpleGraph G₂).Holds FirstOrder.Language.adj (f ∘ x) :=
      h (RelSymbol.mk' FirstOrder.Language.adj) x
    rw [ofSimpleGraph_holds_adj, ofSimpleGraph_holds_adj] at hs
    have himg : e.image f = {f (x 0), f (x 1)} := by
      rw [← hxrange, tupleRange_two, Finset.image_insert, Finset.image_singleton]
    rw [himg, ← hxrange, tupleRange_two, mem_ofSimpleGraph_pair hne,
      mem_ofSimpleGraph_pair fun hf => hne (hinj hf)]
    exact hs
  · intro h s x
    obtain ⟨⟨n, hn⟩, R⟩ := s
    cases R
    show (ofSimpleGraph G₁).Holds FirstOrder.Language.adj x
      ↔ (ofSimpleGraph G₂).Holds FirstOrder.Language.adj (f ∘ x)
    rw [ofSimpleGraph_holds_adj, ofSimpleGraph_holds_adj]
    by_cases hx : x 0 = x 1
    · constructor
      · intro hadj
        exact absurd (hx ▸ hadj) G₁.irrefl
      · intro hadj
        rw [show (f ∘ x) 0 = (f ∘ x) 1 from congrArg f hx] at hadj
        exact absurd hadj G₂.irrefl
    · have he : ({x 0, x 1} : Finset W) ∈ Finset.univ.powersetCard 2 :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hx⟩
      have hiff := h {x 0, x 1} he
      rw [Finset.image_insert, Finset.image_singleton,
        mem_ofSimpleGraph_pair hx,
        mem_ofSimpleGraph_pair fun hf => hx (hinj hf)] at hiff
      exact hiff

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- The one-edge graph on Fin 2: adjacency holds on (0, 1) and not on (0, 0),
-- through both Holds and the explicit RelMap bridge.
example :
    (ofSimpleGraph (⊤ : SimpleGraph (Fin 2))).Holds FirstOrder.Language.adj
      ![0, 1] := by decide

example :
    ¬(ofSimpleGraph (⊤ : SimpleGraph (Fin 2))).Holds FirstOrder.Language.adj
      ![0, 0] := by decide

example :
    @FirstOrder.Language.Structure.RelMap _ (Fin 2)
      (ofSimpleGraph (⊤ : SimpleGraph (Fin 2))).toStructure 2
      FirstOrder.Language.adj ![0, 1] := by
  rw [ofSimpleGraph_toStructure_relMap]
  show (⊤ : SimpleGraph (Fin 2)).Adj 0 1
  decide

-- The ordered adjacency count of the complete graph on Fin 3 is 6 (all ordered
-- pairs of distinct vertices), matching pairCount.
example :
    relationCount (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
      FirstOrder.Language.adj = 6 := by decide

end Tests

end RegularityLemmata
