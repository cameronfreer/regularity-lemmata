/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Weak
import RegularityLemmata.Partition.AlmostRefines
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Bridges to mathlib's graph regularity

Mathlib's regularity development is wrapped, not reproved. The `ℚ → ℝ` boundary is
crossed by exactly one cast equation per notion (`pairDensity_eq_edgeDensity_cast`),
never a pervasive cast layer. `IsUniformPair` translates to and from
`SimpleGraph.IsUniform` with the honest quantifiers: mathlib's strict `< ε` gives our
`≤ ε` directly, while the converse trades `ε` for any `ε' > ε`.

Mathlib's effective Szemerédi regularity lemma (`szemeredi_regularity`), triangle
counting (`SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`), and triangle removal
(`SimpleGraph.triangle_removal`) are re-exported in library vocabulary; see Y. Dillies
and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022, for the
underlying development.

The section's own theorem is the **almost-refining weakly regular equipartition**: a
weakly regular exact refinement `Q ≤ P₀` (from `Graph/Weak.lean`) together with an
equipartition `E` almost-refining both `Q` and `P₀` — the combination Phase 3's
`AlmostRefines` API was frozen for. (An equipartition that is itself weakly regular
*and* almost-refining requires equitabilisation inside the increment loop and is
deferred; see `ARCHITECTURE.md`.)
-/

namespace RegularityLemmata

variable {α : Type*} {s A B : Finset α} {ε : ℝ}

/-! ### The ℚ → ℝ boundary -/

theorem pairCount_eq_card_interedges (R : α → α → Prop) [DecidableRel R] :
    pairCount R A B = (Rel.interedges R A B).card := rfl

/-- The single cast equation for densities: our real-valued `pairDensity` is the cast
of mathlib's rational `Rel.edgeDensity`. -/
theorem pairDensity_eq_edgeDensity_cast (R : α → α → Prop) [DecidableRel R] :
    pairDensity R A B = ((Rel.edgeDensity R A B : ℚ) : ℝ) := by
  rw [pairDensity_eq_count_div, pairCount_eq_card_interedges R, Rel.edgeDensity]
  push_cast
  rfl

/-- Specialization to a simple graph's adjacency. -/
theorem pairDensity_adj_eq_edgeDensity (G : SimpleGraph α) [DecidableRel G.Adj] :
    pairDensity G.Adj A B = ((G.edgeDensity A B : ℚ) : ℝ) :=
  pairDensity_eq_edgeDensity_cast _

/-! ### Uniformity bridges -/

/-- Mathlib uniformity (strict `< ε`) implies library uniformity (`≤ ε`). -/
theorem IsUniformPair.of_isUniform {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : G.IsUniform ε A B) : IsUniformPair G.Adj A B ε := by
  intro A' hA' B' hB' hAc hBc
  rw [pairDensity_adj_eq_edgeDensity, pairDensity_adj_eq_edgeDensity]
  exact (h hA' hB' (by rwa [mul_comm]) (by rwa [mul_comm])).le

/-- Library uniformity at `ε` gives mathlib uniformity at any `ε' > ε`. -/
theorem isUniform_of_isUniformPair {G : SimpleGraph α} [DecidableRel G.Adj] {ε' : ℝ}
    (h : IsUniformPair G.Adj A B ε) (hεε' : ε < ε') : G.IsUniform ε' A B := by
  intro A' hA' B' hB' hAc hBc
  have hA'' : ε * (A.card : ℝ) ≤ A'.card := by
    calc ε * (A.card : ℝ) ≤ ε' * A.card :=
          mul_le_mul_of_nonneg_right hεε'.le (Nat.cast_nonneg _)
      _ = (A.card : ℝ) * ε' := mul_comm _ _
      _ ≤ A'.card := hAc
  have hB'' : ε * (B.card : ℝ) ≤ B'.card := by
    calc ε * (B.card : ℝ) ≤ ε' * B.card :=
          mul_le_mul_of_nonneg_right hεε'.le (Nat.cast_nonneg _)
      _ = (B.card : ℝ) * ε' := mul_comm _ _
      _ ≤ B'.card := hBc
  have := h hA' hB' hA'' hB''
  rw [pairDensity_adj_eq_edgeDensity, pairDensity_adj_eq_edgeDensity] at this
  exact lt_of_le_of_lt this hεε'

/-! ### Mathlib regularity and triangle results, re-exported -/

section FintypeHost

variable [DecidableEq α] [Fintype α]

/-- Mathlib's effective **Szemerédi regularity lemma**: a bounded-size `ε`-uniform
equipartition, with a host-independent bound. Wrapped, not reproved. -/
theorem exists_equipartition_isUniform (G : SimpleGraph α) [DecidableRel G.Adj]
    {l : ℕ} (hε : 0 < ε) (hl : l ≤ Fintype.card α) :
    ∃ P : Finpartition (Finset.univ : Finset α),
      P.IsEquipartition ∧ l ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound ε l ∧ P.IsUniform G ε :=
  szemeredi_regularity G hε hl

/-- Mathlib's **triangle counting lemma**: a graph far from triangle-free has many
triangles. Wrapped, not reproved. -/
theorem farFromTriangleFree_le_card_cliqueFinset {G : SimpleGraph α} [DecidableRel G.Adj]
    (hG : G.FarFromTriangleFree ε) :
    SimpleGraph.triangleRemovalBound ε * Fintype.card α ^ 3 ≤ (G.cliqueFinset 3).card :=
  hG.le_card_cliqueFinset

/-- Mathlib's **triangle removal lemma**: few triangles can all be removed by deleting
few edges. Wrapped, not reproved. -/
theorem triangle_removal_of_card_cliqueFinset_lt {G : SimpleGraph α} [DecidableRel G.Adj]
    (hG : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * Fintype.card α ^ 3) :
    ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
      ((G.edgeFinset.card : ℝ) - G'.edgeFinset.card) < ε * (Fintype.card α ^ 2 : ℕ)
        ∧ G'.CliqueFree 3 :=
  SimpleGraph.triangle_removal hG

end FintypeHost

/-! ### The almost-refining weakly regular equipartition -/

/-- **Almost-refining weakly regular equipartition.** For any starting partition `P₀`,
tolerance `ε > 0`, and admissible equipartition size `t`, there are a weakly
`ε`-regular exact refinement `Q ≤ P₀` with the host-independent part bound and an
equipartition `E` with exactly `t` parts almost-refining both `Q` and `P₀` at `ε` —
provided `t` is fine enough (`⌊|s|/t⌋ · weakBound ⌈1/ε⁵⌉ #P₀.parts ≤ ε·|s|`). -/
theorem exists_weakRegular_and_almostRefining_equipartition [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (P₀ : Finpartition s) (hε : 0 < ε)
    {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hbound : ((s.card / t : ℕ) : ℝ) * weakBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card
      ≤ ε * s.card) :
    ∃ Q E : Finpartition s, Q ≤ P₀ ∧ IsWeakRegular R ε Q ∧
      Q.parts.card ≤ weakBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card ∧
      E.IsEquipartition ∧ E.parts.card = t ∧
      AlmostRefines E Q ε ∧ AlmostRefines E P₀ ε := by
  obtain ⟨Q, hQP, hQreg, hQcard⟩ := exists_weak_regular_refinement R P₀ hε
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_equipartition_almostRefinesAt Q ht hts
  have hEQ : AlmostRefines E Q ε := by
    refine almostRefines_of_almostRefinesAt hE3 (le_trans ?_ hbound)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQcard) (Nat.cast_nonneg _)
  have hEP₀ : AlmostRefines E P₀ ε := by
    have := hEQ.trans (almostRefines_of_le hQP le_rfl)
    simpa using this
  exact ⟨Q, E, hQP, hQreg, hQcard, hE1, hE2, hEQ, hEP₀⟩

/-! ### Tests and adversarial examples -/

-- The cast equation on a concrete instance.
example :
    pairDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
      = ((Rel.edgeDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ : ℚ) : ℝ) :=
  pairDensity_eq_edgeDensity_cast _

-- Everything is 1-uniform in the library sense, so mathlib-uniform at any ε' > 1.
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : G.IsUniform (2 : ℝ)
    Finset.univ Finset.univ :=
  isUniform_of_isUniformPair isUniformPair_one one_lt_two

end RegularityLemmata
