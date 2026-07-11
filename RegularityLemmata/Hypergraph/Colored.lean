/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Uniform
import Mathlib.Algebra.BigOperators.Field

/-!
# Colored total uniform hypergraphs

A `ColoredHypergraph r K V` assigns one of `K` colors to **every** `r`-element vertex
set (a total coloring — "no edge" is itself a color, by convention color `0` in the
graph adapter). Color classes are uniform hypergraphs; their densities are
nonnegative and sum to `1` on nontrivial hosts (`sum_density_colorClass`), degrading
to `0` under the zero-denominator convention.

The `r = 2` adapter encodes a simple graph as a `2`-coloring (non-edge/edge); the
arity-3 abbreviations fix `r = 3` for the triadic development.
-/

namespace RegularityLemmata

variable {V : Type*} {r K : ℕ}

/-- A total `K`-coloring of the `r`-element vertex sets. -/
structure ColoredHypergraph (r K : ℕ) (V : Type*) where
  /-- The color of each `r`-set (values on other finsets are irrelevant). -/
  coloring : Finset V → Fin K

namespace ColoredHypergraph

variable [Fintype V] [DecidableEq V]

/-- The color class of `c`: the `r`-uniform hypergraph of `r`-sets colored `c`. -/
def colorClass (H : ColoredHypergraph r K V) (c : Fin K) : UniformHypergraph r V :=
  ⟨(Finset.univ.powersetCard r).filter (fun e => H.coloring e = c),
    fun _ he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2⟩

omit [DecidableEq V] in
@[simp] theorem mem_colorClass {H : ColoredHypergraph r K V} {c : Fin K}
    {e : Finset V} :
    e ∈ (H.colorClass c).edges ↔ e ∈ Finset.univ.powersetCard r ∧ H.coloring e = c := by
  rw [colorClass]
  exact Finset.mem_filter

omit [DecidableEq V] in
/-- Color classes partition the complete hypergraph: totality of the coloring. -/
theorem sum_card_colorClass (H : ColoredHypergraph r K V) :
    ∑ c : Fin K, (H.colorClass c).edges.card = (Fintype.card V).choose r := by
  classical
  rw [show (Fintype.card V).choose r = (Finset.univ.powersetCard r : Finset (Finset V)).card
      from by rw [Finset.card_powersetCard, Finset.card_univ]]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun e => H.coloring e) (t := Finset.univ) (fun e _ => Finset.mem_univ _)]
  rfl

omit [DecidableEq V] in
/-- **Partition of unity.** On a host with `r ≤ |V|`, the color-class densities sum
to `1`; the zero-denominator convention gives `0` otherwise. -/
theorem sum_density_colorClass (H : ColoredHypergraph r K V) (hr : r ≤ Fintype.card V) :
    ∑ c : Fin K, (H.colorClass c).density = 1 := by
  have hpos : (0 : ℝ) < ((Fintype.card V).choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hr
  unfold UniformHypergraph.density
  rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast H.sum_card_colorClass

/-! ### The graph adapter (`r = 2`, `K = 2`) -/

/-- A simple graph as a total `2`-coloring of pairs: color `1` on edges, `0` off. -/
def ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ColoredHypergraph 2 2 V :=
  ⟨fun e => if e ∈ (UniformHypergraph.ofSimpleGraph G).edges then 1 else 0⟩

theorem ofSimpleGraph_colorClass_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((ofSimpleGraph G).colorClass 1).edges = (UniformHypergraph.ofSimpleGraph G).edges := by
  ext e
  rw [mem_colorClass]
  have hcol : (ofSimpleGraph G).coloring e
      = if e ∈ (UniformHypergraph.ofSimpleGraph G).edges then 1 else 0 := rfl
  by_cases he : e ∈ (UniformHypergraph.ofSimpleGraph G).edges
  · rw [hcol, if_pos he]
    exact ⟨fun _ => he, fun _ =>
      ⟨(UniformHypergraph.ofSimpleGraph G).edges_subset_powersetCard he, rfl⟩⟩
  · rw [hcol, if_neg he]
    constructor
    · rintro ⟨-, hc⟩
      exact absurd hc (by decide)
    · intro h
      exact absurd h he

/-! ### Arity-3 convenience API -/

/-- Colored triadic hypergraphs: the arity fixed to `3`. -/
abbrev ColoredTriadic (K : ℕ) (V : Type*) := ColoredHypergraph 3 K V

/-- Triadic color-class density. -/
noncomputable def triadicDensity {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
    (H : ColoredTriadic K V) (c : Fin K) : ℝ :=
  (H.colorClass c).density

end ColoredHypergraph

/-! ### Tests and adversarial examples -/

open ColoredHypergraph UniformHypergraph

-- A concrete 2-coloring of pairs over Fin 3 (color by parity of the sum).
-- Its classes partition the 3 pairs.
example :
    ∑ c : Fin 2,
      ((⟨fun e => if 2 ∣ e.sum (fun x => (x : ℕ)) then 0 else 1⟩ :
        ColoredHypergraph 2 2 (Fin 3)).colorClass c).edges.card = 3 := by
  rw [sum_card_colorClass]
  decide

-- Partition of unity on a nontrivial host.
example (H : ColoredHypergraph 2 3 (Fin 4)) :
    ∑ c : Fin 3, (H.colorClass c).density = 1 :=
  H.sum_density_colorClass (by norm_num)

-- Adversarial: with r > |V| every class is empty and the density sum is 0, not 1.
example (H : ColoredHypergraph 3 2 (Fin 2)) :
    ∑ c : Fin 2, (H.colorClass c).density = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  unfold UniformHypergraph.density
  rw [show ((Fintype.card (Fin 2)).choose 3) = 0 from by decide]
  norm_num

-- The graph adapter's edge class is the graph's edge set.
example :
    ((ColoredHypergraph.ofSimpleGraph (⊤ : SimpleGraph (Fin 3))).colorClass 1).edges.card
      = 3 := by
  rw [ofSimpleGraph_colorClass_one]
  decide

end RegularityLemmata
