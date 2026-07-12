/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryEnergy
import RegularityLemmata.Relational.BinaryProfile
import RegularityLemmata.Relational.GraphAdapter

/-!
# Binary-palette bridges and falsification gates

Phase 9 unit 7 (design freeze in `ARCHITECTURE.md`): how the palette machinery
specializes on the graph language, and why the two-way palette is genuinely stronger
than one-way colors on a general directed relation.

For `FiniteRelModel.ofSimpleGraph G`:
* vertex profiles are constant — there are no unary symbols and every loop is false
  by looplessness (`binaryVertexProfile_ofSimpleGraph_eq`), so the vertex-profile
  partition is trivial (`binaryProfilePartition_ofSimpleGraph_le_one`);
* only the symmetric palettes are realized — the palette is invariant under reversal
  (`binaryPairPalette_ofSimpleGraph_symm`), so its two coordinates always agree
  (`binaryPairPalette_ofSimpleGraph_coords_eq`) and the asymmetric palettes are never
  realized (`not_hasBinaryPairPalette_ofSimpleGraph_of_asymm`).

A directed relation, by contrast, realizes asymmetric palettes — so palette
regularity strictly refines one-way adjacency data (the falsification test).
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {V : Type*}

/-! ### The graph language: constant profiles -/

theorem ofSimpleGraph_rel_loop {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : FirstOrder.Language.graph.Relations 2) (v : V) :
    (ofSimpleGraph G).rel R ![v, v] = false := by
  cases R
  show decide (G.Adj v v) = false
  simp only [decide_eq_false_iff_not]
  exact fun h => h.ne rfl

/-- Graph vertex profiles are constant: no unary symbols, and loops are false. -/
theorem binaryVertexProfile_ofSimpleGraph_eq {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) :
    binaryVertexProfile (ofSimpleGraph G) a = binaryVertexProfile (ofSimpleGraph G) b := by
  refine Prod.ext ?_ ?_
  · funext U
    exact nomatch U
  · funext R
    show (ofSimpleGraph G).rel R ![a, a] = (ofSimpleGraph G).rel R ![b, b]
    rw [ofSimpleGraph_rel_loop, ofSimpleGraph_rel_loop]

/-- The graph vertex-profile partition is trivial (at most one cell). -/
theorem binaryProfilePartition_ofSimpleGraph_le_one [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) :
    (binaryProfilePartition (ofSimpleGraph G) s).parts.card ≤ 1 := by
  rw [binaryProfilePartition_parts]
  have hcell : ∀ a ∈ s,
      {b ∈ s | binaryVertexProfile (ofSimpleGraph G) a
        = binaryVertexProfile (ofSimpleGraph G) b} = s :=
    fun a _ => Finset.filter_true_of_mem
      fun b _ => binaryVertexProfile_ofSimpleGraph_eq _ a b
  have hsub : (s.image fun a =>
      {b ∈ s | binaryVertexProfile (ofSimpleGraph G) a
        = binaryVertexProfile (ofSimpleGraph G) b}) ⊆ {s} := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [Finset.mem_singleton]
    exact hcell a ha
  exact le_trans (Finset.card_le_card hsub) (by rw [Finset.card_singleton])

/-! ### The graph language: only symmetric palettes -/

/-- Graph palettes are invariant under reversal (adjacency is symmetric). -/
theorem binaryPairPalette_ofSimpleGraph_symm {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) :
    binaryPairPalette (ofSimpleGraph G) a b
      = binaryPairPalette (ofSimpleGraph G) b a := by
  funext R
  cases R
  have hsymm : decide (G.Adj a b) = decide (G.Adj b a) := by
    rw [decide_eq_decide]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  show (decide (G.Adj a b), decide (G.Adj b a))
    = (decide (G.Adj b a), decide (G.Adj a b))
  rw [hsymm]

/-- The two coordinates of a graph palette always agree. -/
theorem binaryPairPalette_ofSimpleGraph_coords_eq {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (R : FirstOrder.Language.graph.Relations 2) :
    (binaryPairPalette (ofSimpleGraph G) a b R).1
      = (binaryPairPalette (ofSimpleGraph G) a b R).2 := by
  cases R
  show decide (G.Adj a b) = decide (G.Adj b a)
  rw [decide_eq_decide]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Asymmetric palettes are never realized** on a graph. -/
theorem not_hasBinaryPairPalette_ofSimpleGraph_of_asymm {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] {c : BinaryPairPalette FirstOrder.Language.graph}
    (R : FirstOrder.Language.graph.Relations 2) (hc : (c R).1 ≠ (c R).2) (a b : V) :
    ¬HasBinaryPairPalette (ofSimpleGraph G) c a b := by
  intro h
  rw [HasBinaryPairPalette] at h
  apply hc
  rw [← h]
  exact binaryPairPalette_ofSimpleGraph_coords_eq G a b R

/-! ### Tests and adversarial examples -/

section Tests

/-- A directed one-binary-symbol test model. -/
private def dirModel {V : Type*} [DecidableEq V] (p : V → V → Bool) :
    FiniteRelModel (singleRelLang 2) V :=
  ⟨fun {n} _ x =>
    if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- **Palette regularity is strictly stronger than one-way data.** The directed
-- relation `a < b` on `Fin 2` realizes the asymmetric palette `(true, false)` on
-- `(0, 1)`; the complete graph on `Fin 2` realizes no asymmetric palette.
example :
    (0 < pairCount (HasBinaryPairPalette
        (dirModel (V := Fin 2) fun a b => decide ((a : ℕ) < b))
        fun _ => (true, false)) Finset.univ Finset.univ)
      ∧ (pairCount (HasBinaryPairPalette
        (ofSimpleGraph (⊤ : SimpleGraph (Fin 2))) fun _ => (true, false))
        Finset.univ Finset.univ = 0) := by decide

-- The complete graph on `Fin 3` realizes only the symmetric palettes: the two-way
-- color count concentrates on `(true, true)` (edges) and `(false, false)`.
example :
    pairCount (HasBinaryPairPalette (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
        fun _ => (false, true)) Finset.univ Finset.univ = 0 := by decide

-- The graph vertex-profile partition of a nonempty host is a single cell.
example :
    (binaryProfilePartition (ofSimpleGraph (⊤ : SimpleGraph (Fin 3)))
      Finset.univ).parts.card ≤ 1 :=
  binaryProfilePartition_ofSimpleGraph_le_one _ _

end Tests

end RegularityLemmata
