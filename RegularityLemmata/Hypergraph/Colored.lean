/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Uniform
import Mathlib.Algebra.BigOperators.Field

/-!
# Colored total uniform hypergraphs

A `ColoredHypergraph r K V` assigns one of `K` colors to **every** `r`-element vertex
set — the domain is the subtype `{e : Finset V // e.card = r}`, so colorings carry no
junk data on other finsets: two colorings agreeing on all `r`-sets are equal
(`ColoredHypergraph.ext`), and when there are no `r`-sets a `0`-color coloring exists.
"No edge" is itself a color (color `0` in the graph adapter).

Color classes are uniform hypergraphs; their densities sum to `1` on hosts with
`r ≤ |V|` (`sum_density_colorClass`), degrading to `0` under the zero-denominator
convention. The `r = 2` graph adapter has both classes characterized: color `1` is the
edge set, color `0` the non-edges among pairs. The arity-3 abbreviations fix `r = 3`
for the triadic development.
-/

namespace RegularityLemmata

variable {V : Type*} {r K : ℕ}

/-- An `r`-element vertex set. -/
abbrev RSet (r : ℕ) (V : Type*) := {e : Finset V // e.card = r}

/-- A total `K`-coloring of the `r`-element vertex sets. Extensional: the domain is
exactly the `r`-sets, so there is no irrelevant data. -/
@[ext] structure ColoredHypergraph (r K : ℕ) (V : Type*) where
  /-- The color of each `r`-set. -/
  coloring : RSet r V → Fin K

namespace ColoredHypergraph

variable [Fintype V] [DecidableEq V]

/-- The color class of `c`: the `r`-uniform hypergraph of `r`-sets colored `c`. -/
def colorClass (H : ColoredHypergraph r K V) (c : Fin K) : UniformHypergraph r V :=
  ⟨(Finset.univ.filter fun e : RSet r V => H.coloring e = c).image Subtype.val,
    fun e he => by
      rw [Finset.mem_image] at he
      obtain ⟨e', _, rfl⟩ := he
      exact e'.2⟩

theorem mem_colorClass {H : ColoredHypergraph r K V} {c : Fin K} {e : Finset V} :
    e ∈ (H.colorClass c).edges ↔ ∃ h : e.card = r, H.coloring ⟨e, h⟩ = c := by
  rw [colorClass]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨e', he'⟩, hc, rfl⟩
    exact ⟨he', hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨e, h⟩, hc, rfl⟩

/-- Color classes partition the `r`-sets: totality of the coloring. -/
theorem sum_card_colorClass (H : ColoredHypergraph r K V) :
    ∑ c : Fin K, (H.colorClass c).edges.card = (Fintype.card V).choose r := by
  classical
  have himg : ∀ c : Fin K, (H.colorClass c).edges.card
      = ((Finset.univ : Finset (RSet r V)).filter fun e => H.coloring e = c).card := by
    intro c
    rw [colorClass]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  rw [Finset.sum_congr rfl fun c _ => himg c]
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun e : RSet r V => H.coloring e) (t := Finset.univ)
    (fun e _ => Finset.mem_univ _)]
  rw [Finset.card_univ, Fintype.card_subtype]
  rw [show ((Finset.univ : Finset (Finset V)).filter fun e => e.card = r)
      = Finset.univ.powersetCard r from ?_]
  · rw [Finset.card_powersetCard, Finset.card_univ]
  · ext e
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨Finset.subset_univ _, h.2⟩, fun h => ⟨Finset.mem_univ _, h.2⟩⟩

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
  ⟨fun e => if (e : Finset V) ∈ (UniformHypergraph.ofSimpleGraph G).edges then 1 else 0⟩

/-- Color `1` is exactly the edge set. -/
theorem ofSimpleGraph_colorClass_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((ofSimpleGraph G).colorClass 1).edges = (UniformHypergraph.ofSimpleGraph G).edges := by
  ext e
  rw [mem_colorClass]
  have hcol : ∀ h : e.card = 2, (ofSimpleGraph G).coloring ⟨e, h⟩
      = if e ∈ (UniformHypergraph.ofSimpleGraph G).edges then 1 else 0 := fun _ => rfl
  constructor
  · rintro ⟨h, hc⟩
    rw [hcol h] at hc
    by_contra hne
    rw [if_neg hne] at hc
    exact absurd hc (by decide)
  · intro he
    refine ⟨(UniformHypergraph.ofSimpleGraph G).card_eq e he, ?_⟩
    rw [hcol, if_pos he]

/-- Color `0` is exactly the non-edges among the pairs. -/
theorem ofSimpleGraph_colorClass_zero (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((ofSimpleGraph G).colorClass 0).edges
      = (UniformHypergraph.complete 2 V).edges
          \ (UniformHypergraph.ofSimpleGraph G).edges := by
  ext e
  rw [mem_colorClass, Finset.mem_sdiff]
  have hcol : ∀ h : e.card = 2, (ofSimpleGraph G).coloring ⟨e, h⟩
      = if e ∈ (UniformHypergraph.ofSimpleGraph G).edges then 1 else 0 := fun _ => rfl
  constructor
  · rintro ⟨h, hc⟩
    rw [hcol h] at hc
    by_cases he : e ∈ (UniformHypergraph.ofSimpleGraph G).edges
    · rw [if_pos he] at hc
      exact absurd hc (by decide)
    · refine ⟨?_, he⟩
      rw [UniformHypergraph.complete, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, h⟩
  · rintro ⟨hmem, hne⟩
    rw [UniformHypergraph.complete, Finset.mem_powersetCard] at hmem
    refine ⟨hmem.2, ?_⟩
    rw [hcol, if_neg hne]

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

-- Extensionality: colorings live exactly on r-sets (no junk data), so with no r-sets
-- at all a 0-color coloring exists.
example : ColoredHypergraph 3 0 (Fin 2) :=
  ⟨fun e => absurd e.2 (by
    have := Finset.card_le_card (Finset.subset_univ e.1)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega)⟩

-- A concrete 2-coloring of pairs over Fin 3 (color by parity of the sum): its classes
-- partition the 3 pairs.
example :
    ∑ c : Fin 2,
      ((⟨fun e => if 2 ∣ e.1.sum (fun x => (x : ℕ)) then 0 else 1⟩ :
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

-- The graph adapter's two classes: edges and non-edges.
example :
    ((ColoredHypergraph.ofSimpleGraph (⊤ : SimpleGraph (Fin 3))).colorClass 1).edges.card
      = 3 := by
  rw [ofSimpleGraph_colorClass_one]
  decide

example :
    ((ColoredHypergraph.ofSimpleGraph (⊤ : SimpleGraph (Fin 3))).colorClass 0).edges.card
      = 0 := by
  rw [ofSimpleGraph_colorClass_zero]
  decide

end RegularityLemmata
