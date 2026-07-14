/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.DiagonalGate
import RegularityLemmata.Relational.GraphAdapter
import RegularityLemmata.Graph.PathCounting
import RegularityLemmata.Graph.TriangleCounting
import RegularityLemmata.Hypergraph.Uniform
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Phase 10 unit 9: graph bridges

Exact bridges from the relational counting machinery to simple graphs via
`FiniteRelModel.ofSimpleGraph` (mathlib's graph language, one binary adjacency symbol). No removal
theorem enters this file.

* **Symmetric palettes as adjacency and nonadjacency.** The graph language has four binary
  palettes; on the symmetric adapter `ofSimpleGraph G`, the all-adjacent palette `adjPalette`
  realizes exactly the adjacency relation (`hasBinaryPairPalette_adjPalette_eq`) and the
  all-nonadjacent palette `nonadjPalette` realizes exactly nonadjacency
  (`hasBinaryPairPalette_nonadjPalette_eq`); every graph-adapter pair carries one of the two
  (`binaryPairPalette_ofSimpleGraph`), making the induced nature — edges *and* nonedges —
  visible.
* **Ordered edge and length-two-path counts.** The palette pair count is the graph edge count
  (`pairCount G.Adj`); the palette directed-path count is the graph length-two-path count.
* **Ordered triangle count and the `3! = 6` clique conversion.** The palette directed-triangle
  count is `directedTriangleCount G.Adj G.Adj G.Adj`, which over the full carrier is
  `6 · #(G.cliqueFinset 3)`.
* **Induced graph copies.** On disjoint cells the induced relational count of a pattern graph is
  the directed-triangle count of adjacency/nonadjacency relations
  (`inducedEmbeddingCountOn_three_ofSimpleGraph_adj`); over the full carrier it is the existing
  induced graph-copy count (`inducedEmbeddingCountOn_univ_ofSimpleGraph`).
* **Corollary specialization.** The global strong-counting corollary specializes to
  `ofSimpleGraph G` (nullary compatibility is automatic; the graph language is `AtMostBinary`).
-/

namespace RegularityLemmata

open FirstOrder

/-- Mathlib's graph language has no relation symbols above arity two. -/
instance : AtMostBinary FirstOrder.Language.graph where
  relationsEmptyAboveTwo := fun _ _ => ⟨fun r => by cases r; omega⟩

namespace FiniteRelModel

variable {V : Type*}

/-! ### Symmetric graph palettes as adjacency / nonadjacency -/

/-- The graph palette recording adjacency in both directions. -/
def adjPalette : BinaryPairPalette FirstOrder.Language.graph := fun _ => (true, true)

/-- The graph palette recording nonadjacency in both directions. -/
def nonadjPalette : BinaryPairPalette FirstOrder.Language.graph := fun _ => (false, false)

/-- The adapter interprets the adjacency symbol as `decide ∘ Adj`. -/
theorem rel_ofSimpleGraph_adj (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    (ofSimpleGraph G).rel FirstOrder.Language.adj ![a, b] = decide (G.Adj a b) := rfl

/-- **Adjacency is the all-adjacent palette.** On the symmetric adapter, a pair carries the
all-adjacent palette exactly when the two vertices are adjacent. -/
theorem hasBinaryPairPalette_adjPalette_iff (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    HasBinaryPairPalette (ofSimpleGraph G) adjPalette a b ↔ G.Adj a b := by
  rw [HasBinaryPairPalette]
  constructor
  · intro h
    have h2 := congrFun h FirstOrder.Language.adj
    rw [binaryPairPalette, adjPalette, rel_ofSimpleGraph_adj, Prod.mk.injEq] at h2
    exact of_decide_eq_true h2.1
  · intro h
    funext R
    cases R
    rw [binaryPairPalette, adjPalette, rel_ofSimpleGraph_adj, rel_ofSimpleGraph_adj]
    exact Prod.ext (decide_eq_true h) (decide_eq_true h.symm)

/-- **Adjacency as a relation is the all-adjacent palette.** -/
theorem hasBinaryPairPalette_adjPalette_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasBinaryPairPalette (ofSimpleGraph G) adjPalette = G.Adj := by
  ext a b; exact hasBinaryPairPalette_adjPalette_iff G a b

/-- **Nonadjacency is the all-nonadjacent palette.** On the symmetric adapter, a pair carries the
all-nonadjacent palette exactly when the two vertices are not adjacent. -/
theorem hasBinaryPairPalette_nonadjPalette_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) :
    HasBinaryPairPalette (ofSimpleGraph G) nonadjPalette a b ↔ ¬ G.Adj a b := by
  rw [HasBinaryPairPalette]
  constructor
  · intro h
    have h2 := congrFun h FirstOrder.Language.adj
    rw [binaryPairPalette, nonadjPalette, rel_ofSimpleGraph_adj, Prod.mk.injEq] at h2
    exact of_decide_eq_false h2.1
  · intro h
    funext R
    cases R
    rw [binaryPairPalette, nonadjPalette, rel_ofSimpleGraph_adj, rel_ofSimpleGraph_adj]
    exact Prod.ext (decide_eq_false h) (decide_eq_false fun h' => h h'.symm)

/-- **Nonadjacency as a relation is the all-nonadjacent palette.** -/
theorem hasBinaryPairPalette_nonadjPalette_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasBinaryPairPalette (ofSimpleGraph G) nonadjPalette = fun a b => ¬ G.Adj a b := by
  ext a b; exact hasBinaryPairPalette_nonadjPalette_iff G a b

/-- **Palette classification on graph adapters.** Every ordered pair of a graph adapter carries
the all-adjacent or the all-nonadjacent palette, according to adjacency; the induced nature of the
count — edges *and* nonedges — is therefore visible at the palette level. -/
theorem binaryPairPalette_ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    binaryPairPalette (ofSimpleGraph G) a b
      = if G.Adj a b then adjPalette else nonadjPalette := by
  by_cases h : G.Adj a b
  · rw [if_pos h]
    exact (hasBinaryPairPalette_adjPalette_iff G a b).mpr h
  · rw [if_neg h]
    exact (hasBinaryPairPalette_nonadjPalette_iff G a b).mpr h

/-- The palette relation required by a pattern pair is adjacency on a pattern edge and
nonadjacency on a pattern nonedge. -/
theorem hasBinaryPairPalette_binaryPairPalette_ofSimpleGraph {W : Type*} (P : SimpleGraph W)
    [DecidableRel P.Adj] (G : SimpleGraph V) [DecidableRel G.Adj] (i j : W) :
    HasBinaryPairPalette (ofSimpleGraph G) (binaryPairPalette (ofSimpleGraph P) i j)
      = if P.Adj i j then G.Adj else fun a b => ¬ G.Adj a b := by
  rw [binaryPairPalette_ofSimpleGraph]
  by_cases h : P.Adj i j
  · rw [if_pos h, if_pos h, hasBinaryPairPalette_adjPalette_eq]
  · rw [if_neg h, if_neg h, hasBinaryPairPalette_nonadjPalette_eq]

/-! ### Ordered edge and length-two-path counts -/

/-- **Edge count.** The all-adjacent palette pair count is the graph edge count. -/
theorem pairCount_adjPalette (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    pairCount (HasBinaryPairPalette (ofSimpleGraph G) adjPalette) A B = pairCount G.Adj A B := by
  rw [pairCount, pairCount]
  exact congrArg Finset.card
    (Finset.filter_congr fun p _ => hasBinaryPairPalette_adjPalette_iff G p.1 p.2)

/-- **Length-two-path count.** The all-adjacent palette directed-path count is the graph
length-two-path count. -/
theorem directedPathCount_adjPalette (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V) :
    directedPathCount (HasBinaryPairPalette (ofSimpleGraph G) adjPalette)
        (HasBinaryPairPalette (ofSimpleGraph G) adjPalette) A B C
      = directedPathCount G.Adj G.Adj A B C := by
  rw [directedPathCount, directedPathCount, tupleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f _ => ?_)
  rw [directedPathObs, directedPathObs, hasBinaryPairPalette_adjPalette_iff,
    hasBinaryPairPalette_adjPalette_iff]

/-! ### Ordered triangle count and the `6 · #cliqueFinset 3` conversion -/

/-- **Ordered triangle count.** The all-adjacent palette directed-triangle count is the graph
directed-triangle count over adjacency. -/
theorem directedTriangleCount_adjPalette (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) :
    directedTriangleCount (HasBinaryPairPalette (ofSimpleGraph G) adjPalette)
        (HasBinaryPairPalette (ofSimpleGraph G) adjPalette)
        (HasBinaryPairPalette (ofSimpleGraph G) adjPalette) A B C
      = directedTriangleCount G.Adj G.Adj G.Adj A B C := by
  rw [directedTriangleCount, directedTriangleCount, tupleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f _ => ?_)
  rw [directedTriangleObs, directedTriangleObs, hasBinaryPairPalette_adjPalette_iff,
    hasBinaryPairPalette_adjPalette_iff, hasBinaryPairPalette_adjPalette_iff]

variable [DecidableEq V]

/-- The range of a `Fin 3`-tuple is its three-element image. -/
private theorem tupleRange_three (f : Fin 3 → V) : tupleRange f = {f 0, f 1, f 2} := by
  rw [tupleRange]
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- **The `3! = 6` conversion.** Over the full carrier the graph directed-triangle count is six
times the number of triangles (`3`-cliques): each unordered triangle has `3! = 6` orderings, and
adjacency forces the three vertices distinct. -/
theorem directedTriangleCount_adj_eq_six_mul_cliqueFinset [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    directedTriangleCount G.Adj G.Adj G.Adj Finset.univ Finset.univ Finset.univ
      = 6 * (G.cliqueFinset 3).card := by
  rw [← UniformHypergraph.orderedCount_triangles G, directedTriangleCount,
    show (![Finset.univ, Finset.univ, Finset.univ] : Fin 3 → Finset V) = fun _ => Finset.univ from by
      funext i; fin_cases i <;> rfl,
    tupleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f _ => ?_)
  show (G.Adj (f 0) (f 1) ∧ G.Adj (f 0) (f 2) ∧ G.Adj (f 1) (f 2))
      ↔ Function.Injective f ∧ tupleRange f ∈ G.cliqueFinset 3
  rw [tupleRange_three, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
  constructor
  · rintro ⟨h01, h02, h12⟩
    refine ⟨?_, h01, h02, h12⟩
    by_contra hne
    rw [not_injective_fin_three] at hne
    rcases hne with h | h | h
    · exact G.ne_of_adj h01 h
    · exact G.ne_of_adj h02 h
    · exact G.ne_of_adj h12 h
  · rintro ⟨_, h01, h02, h12⟩
    exact ⟨h01, h02, h12⟩

/-! ### Induced relational counts versus induced graph copies -/

omit [DecidableEq V] in
/-- Nullary compatibility is automatic in the graph language (no nullary symbols). -/
theorem nullaryCompatible_graph (P : FiniteRelModel FirstOrder.Language.graph (Fin 3))
    (M : FiniteRelModel FirstOrder.Language.graph V) : NullaryCompatible P M :=
  fun R => nomatch R

omit [DecidableEq V] in
/-- All vertices of a graph adapter carry the same binary profile (there are no arity-`1` symbols
and the adjacency symbol is irreflexive), so profile matching across graph adapters is automatic. -/
theorem binaryVertexProfile_ofSimpleGraph {W : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : V) (w : W) :
    binaryVertexProfile (ofSimpleGraph G) v = binaryVertexProfile (ofSimpleGraph H) w := by
  rw [binaryVertexProfile, binaryVertexProfile]
  refine Prod.ext (funext fun U => nomatch U) (funext fun R => ?_)
  cases R
  show (ofSimpleGraph G).rel FirstOrder.Language.adj ![v, v]
      = (ofSimpleGraph H).rel FirstOrder.Language.adj ![w, w]
  rw [rel_ofSimpleGraph_adj, rel_ofSimpleGraph_adj, decide_eq_decide]
  exact ⟨fun h => absurd h G.irrefl, fun h => absurd h H.irrefl⟩

/-- **Three-vertex induced graph copies.** On disjoint cells, the induced relational count of a
pattern graph `P` inside a host graph `G` is the directed-triangle count of the three palettes
`P` requires — profile matching and nullary compatibility are automatic for graph adapters. -/
theorem inducedEmbeddingCountOn_three_ofSimpleGraph (P : SimpleGraph (Fin 3)) [DecidableRel P.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B C : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    inducedEmbeddingCountOn (ofSimpleGraph P) (ofSimpleGraph G) ![A, B, C]
      = directedTriangleCount
          (HasBinaryPairPalette (ofSimpleGraph G) (binaryPairPalette (ofSimpleGraph P) 0 1))
          (HasBinaryPairPalette (ofSimpleGraph G) (binaryPairPalette (ofSimpleGraph P) 0 2))
          (HasBinaryPairPalette (ofSimpleGraph G) (binaryPairPalette (ofSimpleGraph P) 1 2))
          A B C :=
  inducedEmbeddingCountOn_three (nullaryCompatible_graph _ _)
    (fun v _ => binaryVertexProfile_ofSimpleGraph G P v 0)
    (fun v _ => binaryVertexProfile_ofSimpleGraph G P v 1)
    (fun v _ => binaryVertexProfile_ofSimpleGraph G P v 2) hAB hAC hBC

/-- A pointwise `if` between two decidable relations is decidable. -/
instance {α : Type*} {p : Prop} [Decidable p] (R S : α → α → Prop) [hR : DecidableRel R]
    [hS : DecidableRel S] : DecidableRel (if p then R else S) := by
  split
  · exact hR
  · exact hS

/-- **Three-vertex induced graph copies, graph-facing form.** The three required palette
relations of `inducedEmbeddingCountOn_three_ofSimpleGraph` rewritten through the palette
classification: adjacency on pattern edges, nonadjacency on pattern nonedges. -/
theorem inducedEmbeddingCountOn_three_ofSimpleGraph_adj (P : SimpleGraph (Fin 3))
    [DecidableRel P.Adj] (G : SimpleGraph V) [DecidableRel G.Adj] {A B C : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    inducedEmbeddingCountOn (ofSimpleGraph P) (ofSimpleGraph G) ![A, B, C]
      = directedTriangleCount
          (if P.Adj 0 1 then G.Adj else fun a b => ¬ G.Adj a b)
          (if P.Adj 0 2 then G.Adj else fun a b => ¬ G.Adj a b)
          (if P.Adj 1 2 then G.Adj else fun a b => ¬ G.Adj a b) A B C := by
  rw [inducedEmbeddingCountOn_three_ofSimpleGraph P G hAB hAC hBC, directedTriangleCount,
    directedTriangleCount, tupleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f _ => ?_)
  rw [directedTriangleObs, directedTriangleObs,
    hasBinaryPairPalette_binaryPairPalette_ofSimpleGraph,
    hasBinaryPairPalette_binaryPairPalette_ofSimpleGraph,
    hasBinaryPairPalette_binaryPairPalette_ofSimpleGraph]

/-- **Full-carrier bridge to induced graph copies.** Over the whole carrier, the box-restricted
induced relational count between graph adapters is the existing induced graph-copy count of the
edge hypergraphs. -/
theorem inducedEmbeddingCountOn_univ_ofSimpleGraph [Fintype V] (P : SimpleGraph (Fin 3))
    [DecidableRel P.Adj] (G : SimpleGraph V) [DecidableRel G.Adj] :
    inducedEmbeddingCountOn (ofSimpleGraph P) (ofSimpleGraph G) (fun _ : Fin 3 => Finset.univ)
      = UniformHypergraph.inducedCopyCount (UniformHypergraph.ofSimpleGraph P)
          (UniformHypergraph.ofSimpleGraph G) := by
  rw [← inducedEmbeddingCount_ofSimpleGraph, inducedEmbeddingCountOn, inducedEmbeddingCount,
    Fintype.piFinset_univ]

end FiniteRelModel

open FiniteRelModel

/-! ### Specialization of the global strong-counting corollary -/

/-- **Global strong three-vertex counting for simple graphs.** The global strong-counting
corollary (`abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le`) specialized to the graph
adapter `ofSimpleGraph G`: the actual induced count over the whole carrier is within
`(10·τ + 3·η + 3·δ/η²)·|s|³ + 3·m·|s|²` of the coarse estimate. Nullary compatibility is
automatic. -/
theorem BinaryPaletteStrongWitness.abs_inducedEmbeddingCountOn_ofSimpleGraph_sub_coarseInducedEstimate_le
    {V : Type*} [DecidableEq V] {s : Finset V} {δ : ℝ} {G : SimpleGraph V} [DecidableRel G.Adj]
    {E : ErrorSchedule} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongWitness (ofSimpleGraph G) E δ P₀)
    (P : FiniteRelModel FirstOrder.Language.graph (Fin 3))
    (hτ1 : E w.coarse.parts.card ≤ 1) {η : ℝ} (hη : 0 < η)
    {m : ℕ} (hm : ∀ C ∈ w.coarse.parts, C.card ≤ m) :
    |(inducedEmbeddingCountOn P (ofSimpleGraph G) (fun _ : Fin 3 => s) : ℝ)
        - coarseInducedEstimate P (ofSimpleGraph G) w.coarse|
      ≤ (10 * E w.coarse.parts.card + 3 * η + 3 * (δ / η ^ 2)) * (s.card : ℝ) ^ 3
        + 3 * m * (s.card : ℝ) ^ 2 :=
  w.abs_inducedEmbeddingCountOn_sub_coarseInducedEstimate_le P
    (nullaryCompatible_graph P (ofSimpleGraph G)) hτ1 hη hm

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- **Adjacency is the all-adjacent palette** (statement level).
example {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    HasBinaryPairPalette (ofSimpleGraph G) adjPalette a b ↔ G.Adj a b :=
  hasBinaryPairPalette_adjPalette_iff G a b

-- The two symmetric graph palettes are distinct (adjacent vs nonadjacent).
example : (adjPalette : BinaryPairPalette FirstOrder.Language.graph) ≠ nonadjPalette := by decide

-- **Nonadjacency is the all-nonadjacent palette** (statement level).
example {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    HasBinaryPairPalette (ofSimpleGraph G) nonadjPalette a b ↔ ¬ G.Adj a b :=
  hasBinaryPairPalette_nonadjPalette_iff G a b

-- **Concrete: the all-nonadjacent palette holds exactly on a nonedge** — it holds on the
-- pair (0, 1) in the empty graph and fails on the same pair in the complete graph.
example :
    HasBinaryPairPalette (ofSimpleGraph (⊥ : SimpleGraph (Fin 3))) nonadjPalette 0 1 := by decide

example :
    ¬ HasBinaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) nonadjPalette 0 1 := by
  decide

-- Adversarial: the diagonal pair carries the all-nonadjacent palette even in the complete
-- graph (looplessness) — "nonedge" includes the diagonal.
example :
    HasBinaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) nonadjPalette 0 0 := by decide

-- **Pattern palettes classify as adjacency/nonadjacency** (statement level).
example {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    binaryPairPalette (ofSimpleGraph G) a b = if G.Adj a b then adjPalette else nonadjPalette :=
  binaryPairPalette_ofSimpleGraph G a b

-- **Edge count is the graph pair count** (statement level).
example {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    pairCount (HasBinaryPairPalette (ofSimpleGraph G) adjPalette) A B = pairCount G.Adj A B :=
  pairCount_adjPalette G A B

-- **Ordered triangles are six per clique** (statement level).
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    directedTriangleCount G.Adj G.Adj G.Adj Finset.univ Finset.univ Finset.univ
      = 6 * (G.cliqueFinset 3).card :=
  directedTriangleCount_adj_eq_six_mul_cliqueFinset G

-- **Concrete: the empty graph on `Fin 3` has no triangles**, so the ordered triangle count is `0`.
example : directedTriangleCount (⊥ : SimpleGraph (Fin 3)).Adj (⊥ : SimpleGraph (Fin 3)).Adj
    (⊥ : SimpleGraph (Fin 3)).Adj Finset.univ Finset.univ Finset.univ = 0 := by
  rw [directedTriangleCount_adj_eq_six_mul_cliqueFinset]
  decide

-- **Concrete: the complete graph on `Fin 3` is one triangle**, with `3! = 6` orderings.
example : directedTriangleCount (⊤ : SimpleGraph (Fin 3)).Adj (⊤ : SimpleGraph (Fin 3)).Adj
    (⊤ : SimpleGraph (Fin 3)).Adj Finset.univ Finset.univ Finset.univ = 6 := by
  rw [directedTriangleCount_adj_eq_six_mul_cliqueFinset]
  decide

-- **Full-carrier induced copies** (statement level).
example {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph (Fin 3)) [DecidableRel P.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    inducedEmbeddingCountOn (ofSimpleGraph P) (ofSimpleGraph G) (fun _ : Fin 3 => Finset.univ)
      = UniformHypergraph.inducedCopyCount (UniformHypergraph.ofSimpleGraph P)
          (UniformHypergraph.ofSimpleGraph G) :=
  inducedEmbeddingCountOn_univ_ofSimpleGraph P G

-- **Concrete: the complete pattern has six induced copies in the complete host** on `Fin 3`
-- (the six bijections).
example : inducedEmbeddingCountOn (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
    (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) (fun _ : Fin 3 => Finset.univ) = 6 := by decide

-- **Concrete: a noncomplete pattern has no induced copies in the complete host** — induced
-- counts see nonedges, unlike homomorphism counts.
example : inducedEmbeddingCountOn (ofSimpleGraph (⊥ : SimpleGraph (Fin 3)))
    (ofSimpleGraph (⊤ : SimpleGraph (Fin 3))) (fun _ : Fin 3 => Finset.univ) = 0 := by decide

end Tests

end RegularityLemmata
