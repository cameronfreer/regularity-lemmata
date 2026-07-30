/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.ProxyEventIndex
import RegularityLemmata.Relational.RepresentativeSelection

/-!
# Route (b) ladder step 2: the two aggregate mass reindexings

`ARCHITECTURE.md` route (b) ladder step 2. The selection rebuild sums each mass over ALL
ordered distinct proxy pairs FIRST and bounds the aggregate once per palette; the `9n²`
cardinality envelope multiplies nothing. This file proves the two reindexings that make
that possible, and stops there: no channel routing, no constants, no summit.

* `sum_proxyPair_nonuniform_le` — the nonuniform fine-fibre mass, summed over every ordered
  distinct proxy pair, is bounded ONCE by the diagonal-inclusive bad mass of the fine
  partition. The point is disjointness: a fine cell lies in AT MOST one proxy, so distinct
  proxy pairs contribute disjoint sets of fine-cell pairs and the double sum collapses to a
  single sum over a subset of all fine pairs. No factor of the proxy-pair count appears.
* `sum_proxyPair_deviant_le` — the `η`-deviant fine-fibre mass, summed over every ordered
  distinct proxy pair, is bounded ONCE per palette by the witness's `deviant_mass_le`,
  because the proxy pairs are a subset of all coarse pairs.

Sibling pairs need no special treatment in either: they are ordinary distinct proxy pairs
inside the same aggregate.

**Not done here.** Routing nonuniformity through the forbidden-event channel and deviation
through the cost channel, the candidate-weight constants, and the summit. Rounding,
cleaning and `Recolor.lean` stay closed; profile homogenization remains the later rounding
obligation, and `ARCHITECTURE.md` waits for the completed theorem and its actual constants.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### Disjointness of the proxy fibres -/

/-- Distinct proxy pairs contribute DISJOINT sets of fine-cell pairs: a fine cell sits in
at most one proxy, so it cannot be a fibre member of two. This is what makes the aggregate
a single sum rather than a per-pair bound multiplied by the pair count.

No refinement hypothesis is needed: the fibre filter `(· ⊆ pd.1)` already forces the
containment that the argument uses. -/
theorem proxyFibre_pairwiseDisjoint {F Q : Finpartition s}
    (f : Finset V × Finset V → Prop) [DecidablePred f] :
    (↑(proxyPairEvents Q) : Set (Finset V × Finset V)).PairwiseDisjoint
      (fun pd => ((F.parts.filter (· ⊆ pd.1)) ×ˢ
        (F.parts.filter (· ⊆ pd.2))).filter f) := by
  intro pd hpd pd' hpd' hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro p hp hp'
  rw [Finset.mem_coe, mem_proxyPairEvents] at hpd hpd'
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp hp'
  refine hne (Prod.ext ?_ ?_)
  · obtain ⟨x, hx⟩ := F.nonempty_of_mem_parts hp.1.1.1
    exact Q.eq_of_mem_parts hpd.1 hpd'.1 (hp.1.1.2 hx) (hp'.1.1.2 hx)
  · obtain ⟨x, hx⟩ := F.nonempty_of_mem_parts hp.1.2.1
    exact Q.eq_of_mem_parts hpd.2.1 hpd'.2.1 (hp.1.2.2 hx) (hp'.1.2.2 hx)

/-! ### The nonuniform aggregate -/

open Classical in
/-- **Aggregate nonuniform-mass reindexing.** Summed over EVERY ordered distinct proxy
pair, the nonuniform fine-fibre-pair mass is bounded ONCE by the diagonal-inclusive bad
mass of the fine partition — no factor of the proxy-pair count. -/
theorem sum_proxyPair_nonuniform_le (R : V → V → Prop) [DecidableRel R] {ε : ℝ}
    (F : Finpartition s) (Q : Finpartition s) :
    ∑ pd ∈ proxyPairEvents Q,
        ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
          (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card)
      ≤ badMassDiagNum R ε F := by
  classical
  rw [← Finset.sum_biUnion (proxyFibre_pairwiseDisjoint (F := F) (Q := Q)
    (fun p => ¬ IsUniformPair R p.1 p.2 ε)), badMassDiagNum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
    (fun p _ _ => by positivity)
  rw [Finset.mem_biUnion] at hp
  obtain ⟨pd, -, hp⟩ := hp
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩

/-! ### The deviant aggregate -/

section Deviant

variable {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
  {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

open Classical in
/-- **Aggregate deviant-mass reindexing.** Summed over EVERY ordered distinct proxy pair,
the `η`-deviant fine-fibre-pair mass is bounded ONCE per palette by the witness's total
deviant mass — the proxy pairs being a subset of all coarse pairs. Again no factor of the
proxy-pair count. -/
theorem BinaryPaletteStrongDiagWitness.sum_proxyPair_deviant_le
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) (c : BinaryPairPalette L) {η : ℝ}
    (hη : 0 < η) :
    ∑ pd ∈ proxyPairEvents w.coarse,
        ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ
            (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
            - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
          ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun pd hpd => ?_)
    (fun pd _ _ => Finset.sum_nonneg fun p _ => by positivity)) (w.deviant_mass_le c hη)
  rw [mem_proxyPairEvents] at hpd
  exact Finset.mem_product.mpr ⟨hpd.1, hpd.2.1⟩

end Deviant

/-! ### Tests -/

section Tests

-- Sibling pairs are inside the aggregate, not exceptions to it.
example {Q : Finpartition s} {A B : Finset V} (hA : A ∈ Q.parts) (hB : B ∈ Q.parts)
    (hAB : A ≠ B) : (A, B) ∈ proxyPairEvents Q :=
  mem_proxyPairEvents.mpr ⟨hA, hB, hAB⟩

-- A proxy against itself is not an event, so the aggregate is genuinely off-diagonal at
-- proxy level even though it covers siblings.
example {Q : Finpartition s} {A : Finset V} : (A, A) ∉ proxyPairEvents Q :=
  notMem_proxyPairEvents_self

end Tests

end RegularityLemmata
