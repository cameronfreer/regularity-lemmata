/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Edit
import RegularityLemmata.Finite.PairDensity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Triangle counting/removal bridges

Mathlib's triangle counting and removal lemmas, re-exported, together with the count
and edit conversions that connect their vocabulary (`edgeFinset`, `cliqueFinset`) to
the library's finite calculus:

* `pairCount_adj_eq_two_mul_card_edgeFinset` — ordered adjacent pairs are twice the
  edges;
* `editDistance_adj_of_le` — for a subgraph `G' ≤ G`, the adjacency edit distance on
  the full box is twice the number of removed edges (and its normalized form
  `relativeEditDistance_adj_of_le`).

The remaining conversion — injective ordered triangle count `= 6 · #cliqueFinset 3` —
belongs to the deferred strong-witness counting stage (see `ARCHITECTURE.md`).
This file is kept separate from `Graph/Bridge.lean` because the triangle-removal import
is heavy; import it only where the removal results are consumed.
-/

namespace RegularityLemmata

variable {α : Type*} [Fintype α] [DecidableEq α] {ε : ℝ}

/-- Ordered adjacent pairs over the full box are twice the edges. -/
theorem pairCount_adj_eq_two_mul_card_edgeFinset (G : SimpleGraph α)
    [DecidableRel G.Adj] :
    pairCount G.Adj Finset.univ Finset.univ = 2 * G.edgeFinset.card := by
  rw [SimpleGraph.two_mul_card_edgeFinset, pairCount, Finset.univ_product_univ]

/-- For a subgraph `G' ≤ G`, the adjacency edit distance on the full box is twice the
number of removed edges. -/
theorem editDistance_adj_of_le {G G' : SimpleGraph α} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G' ≤ G) :
    editDistance (fun x : Fin 2 → α => G.Adj (x 0) (x 1))
        (fun x => G'.Adj (x 0) (x 1)) (fun _ => Finset.univ)
      = 2 * G.edgeFinset.card - 2 * G'.edgeFinset.card := by
  classical
  have hbox : editDistance (fun x : Fin 2 → α => G.Adj (x 0) (x 1))
      (fun x => G'.Adj (x 0) (x 1)) (fun _ => Finset.univ)
      = ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : α × α => ¬ (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2))).card := by
    rw [editDistance, editSet]
    exact card_filter_piFinset_two _ _
  have hiff : ∀ p : α × α, (¬ (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2))
      ↔ (G.Adj p.1 p.2 ∧ ¬ G'.Adj p.1 p.2) := by
    intro p
    have := @h p.1 p.2
    tauto
  have hsplit : ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : α × α => G'.Adj p.1 p.2)).card
      + ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : α × α => G.Adj p.1 p.2 ∧ ¬ G'.Adj p.1 p.2)).card
      = ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : α × α => G.Adj p.1 p.2)).card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
    · refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
      have := @h p.1 p.2
      tauto
    · rw [Finset.disjoint_filter]
      tauto
  have hG : ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : α × α => G.Adj p.1 p.2)).card = 2 * G.edgeFinset.card :=
    (pairCount_adj_eq_two_mul_card_edgeFinset G).symm ▸ rfl
  have hG' : ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : α × α => G'.Adj p.1 p.2)).card = 2 * G'.edgeFinset.card :=
    (pairCount_adj_eq_two_mul_card_edgeFinset G').symm ▸ rfl
  have hfe : (Finset.univ ×ˢ Finset.univ).filter
      (fun p : α × α => ¬ (G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2))
      = (Finset.univ ×ˢ Finset.univ).filter
          (fun p : α × α => G.Adj p.1 p.2 ∧ ¬ G'.Adj p.1 p.2) :=
    Finset.filter_congr fun p _ => hiff p
  rw [hbox, hfe]
  omega

/-- Normalized form: the relative adjacency edit distance is the removed-edge fraction. -/
theorem relativeEditDistance_adj_of_le {G G' : SimpleGraph α} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G' ≤ G) :
    relativeEditDistance (fun x : Fin 2 → α => G.Adj (x 0) (x 1))
        (fun x => G'.Adj (x 0) (x 1)) (fun _ => Finset.univ)
      = ((2 * G.edgeFinset.card - 2 * G'.edgeFinset.card : ℕ) : ℝ)
          / (Fintype.card α : ℝ) ^ 2 := by
  rw [relativeEditDistance_eq, editDistance_adj_of_le h]
  congr 1
  have hcard : (Fintype.piFinset fun _ : Fin 2 => (Finset.univ : Finset α)).card
      = Fintype.card α ^ 2 := by
    rw [Fintype.card_piFinset, Fin.prod_univ_two, Finset.card_univ, sq]
  exact_mod_cast congrArg (Nat.cast (R := ℝ)) hcard

/-! ### Mathlib triangle results, re-exported -/

/-- Mathlib's **triangle counting lemma**: a graph far from triangle-free has many
triangles. Wrapped, not reproved. -/
theorem farFromTriangleFree_le_card_cliqueFinset {G : SimpleGraph α} [DecidableRel G.Adj]
    (hG : G.FarFromTriangleFree ε) :
    SimpleGraph.triangleRemovalBound ε * Fintype.card α ^ 3 ≤ (G.cliqueFinset 3).card :=
  hG.le_card_cliqueFinset

/-- Mathlib's **triangle removal lemma**: few triangles can all be removed by deleting
few edges. Combined with `editDistance_adj_of_le`, the edge conclusion reads as an
adjacency edit-distance bound. Wrapped, not reproved. -/
theorem triangle_removal_of_card_cliqueFinset_lt {G : SimpleGraph α} [DecidableRel G.Adj]
    (hG : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * Fintype.card α ^ 3) :
    ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
      ((G.edgeFinset.card : ℝ) - G'.edgeFinset.card) < ε * (Fintype.card α ^ 2 : ℕ)
        ∧ G'.CliqueFree 3 :=
  SimpleGraph.triangle_removal hG

/-! ### Tests and adversarial examples -/

-- Ordered pairs vs edges on the complete graph on 3 vertices: 6 = 2 · 3.
example : pairCount (⊤ : SimpleGraph (Fin 3)).Adj Finset.univ Finset.univ = 6 := by
  decide

example : 2 * ((⊤ : SimpleGraph (Fin 3)).edgeFinset.card) = 6 := by decide

-- Edit distance from the complete graph to the empty graph on Fin 2: both ordered
-- pairs of the single edge, i.e. 2 · 1 − 2 · 0 = 2.
example :
    editDistance (fun x : Fin 2 → Fin 2 => (⊤ : SimpleGraph (Fin 2)).Adj (x 0) (x 1))
      (fun x => (⊥ : SimpleGraph (Fin 2)).Adj (x 0) (x 1)) (fun _ => Finset.univ)
      = 2 := by
  rw [editDistance_adj_of_le bot_le]
  decide

end RegularityLemmata
