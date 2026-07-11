/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Regularity
import RegularityLemmata.Partition.AlmostRefines
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# Bridges to mathlib's graph regularity

Mathlib's regularity development is wrapped, not reproved. The `ℚ → ℝ` boundary is
crossed by exactly one cast equation per notion (`pairDensity_eq_edgeDensity_cast`),
never a pervasive cast layer. `IsUniformPair` translates to and from
`SimpleGraph.IsUniform` with the honest quantifiers: mathlib's strict `< ε` gives our
`≤ ε` directly, while the converse trades `ε` for any `ε' > ε` (the same-`ε` converse
is FALSE — see the strictness counterexample in the test section).

The **partition-level bridge** (`isRegularPartition_of_isUniform`) turns a
mathlib-uniform equipartition into a library-regular partition at `4ε`, via
`badMassNum ≤ #nonUniforms · (max part size)²` and the equipartition size bound. With
mathlib's effective Szemerédi regularity lemma (re-exported as
`exists_equipartition_isUniform`), this makes the wrapper an actual bridge into the
library's calculus. See Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity
Lemma in Lean*, ITP 2022, for the underlying development. Triangle counting/removal
bridges live in `Graph/RemovalBridge.lean`.

The section's own theorem, `exists_regular_refinement_and_almostRefining_equipartition`,
produces **two** partitions: an `ε`-regular exact refinement `Q ≤ P₀`, and a separate
equipartition `E` almost-refining both `Q` and `P₀` — the combination Phase 3's
`AlmostRefines` API was frozen for. It does NOT produce one partition that is
simultaneously regular and equitable; that stronger statement requires
equitabilisation inside the increment loop and is deferred (see `ARCHITECTURE.md`).
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

/-- Library uniformity at `ε` gives mathlib uniformity at any `ε' > ε`. (Trading `ε`
for a strictly larger `ε'` is unavoidable: see the strictness counterexample below.) -/
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

/-! ### The partition-level bridge -/

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

/-- **Partition-level bridge.** A mathlib-uniform equipartition is library-regular at
`4ε`: the bad mass is at most `#nonUniforms · (max part size)²`, and the equipartition
size bound `|C| ≤ ⌊n/k⌋ + 1` with `k ≤ n` turns mathlib's pair-counting bound into the
mass bound. -/
theorem isRegularPartition_of_isUniform {G : SimpleGraph α} [DecidableRel G.Adj]
    {P : Finpartition (Finset.univ : Finset α)}
    (hequi : P.IsEquipartition) (hunif : P.IsUniform G ε) (hε : 0 ≤ ε)
    (hk : P.parts.card ≤ Fintype.card α) :
    IsRegularPartition G.Adj (4 * ε) P := by
  classical
  set n := Fintype.card α with hn
  set k := P.parts.card with hkdef
  set M : ℝ := ((n / k : ℕ) : ℝ) + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  have hsub : (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair G.Adj ε uv.1 uv.2)
      ⊆ P.nonUniforms G ε := by
    rintro ⟨C, D⟩ huv
    rw [Finset.mem_filter, Finset.mem_product] at huv
    obtain ⟨⟨hC, hD⟩, hne, hnu⟩ := huv
    rw [Finpartition.mk_mem_nonUniforms]
    exact ⟨hC, hD, hne, fun hu => hnu (IsUniformPair.of_isUniform hu)⟩
  have hpart : ∀ C ∈ P.parts, (C.card : ℝ) ≤ M := by
    intro C hC
    have h := hequi.card_part_le_average_add_one hC
    rw [Finset.card_univ] at h
    rw [hM]
    exact_mod_cast h
  have hbmn : badMassNum G.Adj ε P ≤ ((P.nonUniforms G ε).card : ℝ) * M ^ 2 := by
    rw [badMassNum]
    calc ∑ uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair G.Adj ε uv.1 uv.2),
          ((uv.1.card : ℝ) * uv.2.card)
        ≤ ∑ _uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair G.Adj ε uv.1 uv.2),
            M ^ 2 := by
          refine Finset.sum_le_sum ?_
          rintro ⟨C, D⟩ huv
          rw [Finset.mem_filter, Finset.mem_product] at huv
          rw [sq]
          exact mul_le_mul (hpart C huv.1.1) (hpart D huv.1.2) (Nat.cast_nonneg _) hM0
      _ = (((P.parts ×ˢ P.parts).filter
            (fun uv => IsBadPair G.Adj ε uv.1 uv.2)).card : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((P.nonUniforms G ε).card : ℝ) * M ^ 2 := by
          have hc : ((((P.parts ×ˢ P.parts).filter
              (fun uv => IsBadPair G.Adj ε uv.1 uv.2)).card : ℝ))
              ≤ ((P.nonUniforms G ε).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hnu : ((P.nonUniforms G ε).card : ℝ) ≤ (k : ℝ) ^ 2 * ε := by
    refine le_trans hunif ?_
    have : ((k * (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hle : k * (k - 1) ≤ k ^ 2 := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · simp [h0]
        · calc k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (by omega)
            _ = k ^ 2 := (sq k).symm
      exact_mod_cast hle
    exact mul_le_mul_of_nonneg_right this hε
  have hkM : (k : ℝ) * M ≤ 2 * n := by
    have h1 : (k : ℕ) * (n / k) ≤ n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self n k
    have h1' : (k : ℝ) * ((n / k : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    have h2 : (k : ℝ) ≤ n := by exact_mod_cast hk
    rw [hM]
    nlinarith
  have hfinal : badMassNum G.Adj ε P ≤ 4 * ε * (n : ℝ) ^ 2 := by
    calc badMassNum G.Adj ε P
        ≤ ((P.nonUniforms G ε).card : ℝ) * M ^ 2 := hbmn
      _ ≤ ((k : ℝ) ^ 2 * ε) * M ^ 2 := by
          refine mul_le_mul_of_nonneg_right hnu ?_
          positivity
      _ = ε * ((k : ℝ) * M) ^ 2 := by ring
      _ ≤ ε * (2 * n) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hε
          have := hkM
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hM0]
      _ = 4 * ε * (n : ℝ) ^ 2 := by ring
  rw [IsRegularPartition, badMass]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hzero : ((Finset.univ : Finset α).card : ℝ) ^ 2 = 0 := by
      rw [Finset.card_univ]
      rw [show Fintype.card α = 0 from hn0]
      norm_num
    rw [hzero, div_zero]
    positivity
  · have hpos : (0 : ℝ) < ((Finset.univ : Finset α).card : ℝ) ^ 2 := by
      rw [Finset.card_univ]
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      positivity
    have h4 : badMassNum G.Adj (4 * ε) P ≤ badMassNum G.Adj ε P :=
      badMassNum_anti G.Adj (by linarith)
    rw [div_le_iff₀ hpos, Finset.card_univ, ← hn]
    exact le_trans h4 hfinal

end FintypeHost

/-! ### The regular refinement plus almost-refining equipartition -/

/-- **Regular refinement + almost-refining equipartition.** This produces **two**
partitions: an `ε`-regular exact refinement `Q ≤ P₀` with the host-independent part
bound, and a *separate* equipartition `E` with exactly `t` parts almost-refining both
`Q` and `P₀` at `ε` — provided `t` is fine enough
(`⌊|s|/t⌋ · regularityBound ⌈1/ε⁵⌉ #P₀.parts ≤ ε·|s|`). It does NOT assert that `E`
itself is regular (deferred; see `ARCHITECTURE.md`). -/
theorem exists_regular_refinement_and_almostRefining_equipartition [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (P₀ : Finpartition s) (hε : 0 < ε)
    {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hbound : ((s.card / t : ℕ) : ℝ) * regularityBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card
      ≤ ε * s.card) :
    ∃ Q E : Finpartition s, Q ≤ P₀ ∧ IsRegularPartition R ε Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card ∧
      E.IsEquipartition ∧ E.parts.card = t ∧
      AlmostRefines E Q ε ∧ AlmostRefines E P₀ ε := by
  obtain ⟨Q, hQP, hQreg, hQcard⟩ := exists_regular_refinement R P₀ hε
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_equipartition_almostRefinesAt Q ht hts
  have hEQ : AlmostRefines E Q ε := by
    refine almostRefines_of_almostRefinesAt hE3 (le_trans ?_ hbound)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQcard) (Nat.cast_nonneg _)
  have hEP₀ : AlmostRefines E P₀ ε := by
    have := hEQ.trans (almostRefines_of_le hQP le_rfl)
    simpa using this
  exact ⟨Q, E, hQP, hQreg, hQcard, hE1, hE2, hEQ, hEP₀⟩

/-- User-facing arithmetic corollary: the cleaner sufficient condition
`regularityBound ⌈1/ε⁵⌉ #P₀.parts ≤ ε · t` implies the floor inequality. -/
theorem exists_regular_refinement_and_almostRefining_equipartition_of_bound_le
    [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (P₀ : Finpartition s)
    (hε : 0 < ε) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hbound : (regularityBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card : ℝ) ≤ ε * t) :
    ∃ Q E : Finpartition s, Q ≤ P₀ ∧ IsRegularPartition R ε Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card ∧
      E.IsEquipartition ∧ E.parts.card = t ∧
      AlmostRefines E Q ε ∧ AlmostRefines E P₀ ε := by
  refine exists_regular_refinement_and_almostRefining_equipartition R P₀ hε ht hts ?_
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : ((s.card / t : ℕ) : ℝ) ≤ (s.card : ℝ) / t := Nat.cast_div_le
  calc ((s.card / t : ℕ) : ℝ) * regularityBound ⌈1 / ε ^ 5⌉₊ P₀.parts.card
      ≤ ((s.card : ℝ) / t) * (ε * t) := by
        refine mul_le_mul h1 hbound (Nat.cast_nonneg _) ?_
        positivity
    _ = ε * s.card := by field_simp

/-! ### Tests and adversarial examples -/

-- The cast equation on a concrete instance, and on an empty side (both sides 0).
example :
    pairDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
      = ((Rel.edgeDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ : ℚ) : ℝ) :=
  pairDensity_eq_edgeDensity_cast _

example :
    ((Rel.edgeDensity (fun a b : Fin 3 => a < b) ∅ Finset.univ : ℚ) : ℝ) = 0 := by
  rw [← pairDensity_eq_edgeDensity_cast]
  exact pairDensity_of_left_card_eq_zero _ _ rfl

-- Everything is 1-uniform in the library sense, so mathlib-uniform at any ε' > 1.
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : G.IsUniform (2 : ℝ)
    Finset.univ Finset.univ :=
  isUniform_of_isUniformPair isUniformPair_one one_lt_two

-- STRICTNESS COUNTEREXAMPLE: the same-ε converse is false. For the complete graph on
-- `Fin 2`, `A = univ`, `B = {1}`, `ε = 1/2`: the library `≤ ε` predicate holds (the
-- parent density is exactly 1/2, and every density lies in [0,1]), while mathlib's
-- `< ε` predicate fails (the qualifying sub-pair `({0}, {1})` realizes deviation
-- exactly 1/2).
example :
    IsUniformPair (⊤ : SimpleGraph (Fin 2)).Adj Finset.univ {1} (1 / 2) := by
  intro A' _ B' _ _ _
  have hbase : pairDensity (⊤ : SimpleGraph (Fin 2)).Adj Finset.univ {1} = 1 / 2 := by
    rw [pairDensity_eq_count_div,
      show pairCount (⊤ : SimpleGraph (Fin 2)).Adj Finset.univ {1} = 1 from by decide,
      show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
      show ({1} : Finset (Fin 2)).card = 1 from by decide]
    norm_num
  rw [hbase]
  have h1 := pairDensity_le_one (R := (⊤ : SimpleGraph (Fin 2)).Adj) (A := A') (B := B')
  have h2 := pairDensity_nonneg (R := (⊤ : SimpleGraph (Fin 2)).Adj) (A := A') (B := B')
  rw [abs_le]
  constructor <;> linarith

example :
    ¬ (⊤ : SimpleGraph (Fin 2)).IsUniform (1 / 2 : ℝ) Finset.univ {1} := by
  intro h
  have hdev := h (show ({0} : Finset (Fin 2)) ⊆ Finset.univ from Finset.subset_univ _)
    (Finset.Subset.refl ({1} : Finset (Fin 2)))
    (by rw [show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
          show ({0} : Finset (Fin 2)).card = 1 from by decide]
        norm_num)
    (by rw [show ({1} : Finset (Fin 2)).card = 1 from by decide]
        norm_num)
  have e1 : ((⊤ : SimpleGraph (Fin 2)).edgeDensity {0} {1} : ℝ) = 1 := by
    rw [← pairDensity_adj_eq_edgeDensity, pairDensity_eq_count_div,
      show pairCount (⊤ : SimpleGraph (Fin 2)).Adj {0} {1} = 1 from by decide,
      show ({0} : Finset (Fin 2)).card = 1 from by decide,
      show ({1} : Finset (Fin 2)).card = 1 from by decide]
    norm_num
  have e2 : ((⊤ : SimpleGraph (Fin 2)).edgeDensity Finset.univ {1} : ℝ) = 1 / 2 := by
    rw [← pairDensity_adj_eq_edgeDensity, pairDensity_eq_count_div,
      show pairCount (⊤ : SimpleGraph (Fin 2)).Adj Finset.univ {1} = 1 from by decide,
      show (Finset.univ : Finset (Fin 2)).card = 2 from by decide,
      show ({1} : Finset (Fin 2)).card = 1 from by decide]
    norm_num
  rw [e1, e2] at hdev
  norm_num at hdev

-- Equitabilisation edge cases: t = 1 (one part, remainder ≤ |s|) and t = |s|
-- (singletons, remainder ≤ 1).
example (P : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    ∃ E : Finpartition ({0, 1, 2} : Finset (Fin 3)),
      E.IsEquipartition ∧ E.parts.card = 1 ∧ AlmostRefinesAt E P 3 := by
  obtain ⟨E, h1, h2, h3⟩ := exists_equipartition_almostRefinesAt P one_pos
    (show 1 ≤ ({0, 1, 2} : Finset (Fin 3)).card from by decide)
  refine ⟨E, h1, h2, ?_⟩
  rwa [show ({0, 1, 2} : Finset (Fin 3)).card / 1 = 3 from by decide] at h3

example (P : Finpartition ({0, 1, 2} : Finset (Fin 3))) :
    ∃ E : Finpartition ({0, 1, 2} : Finset (Fin 3)),
      E.IsEquipartition ∧ E.parts.card = 3 ∧ AlmostRefinesAt E P 1 := by
  obtain ⟨E, h1, h2, h3⟩ := exists_equipartition_almostRefinesAt P (t := 3)
    (by norm_num) (show 3 ≤ ({0, 1, 2} : Finset (Fin 3)).card from by decide)
  refine ⟨E, h1, h2, ?_⟩
  rwa [show ({0, 1, 2} : Finset (Fin 3)).card / 3 = 1 from by decide] at h3

end RegularityLemmata
