/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.RegularDegree
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Inequalities

/-!
# Directed two-step path counting

Phase 10 unit 4 (design freeze in `ARCHITECTURE.md`): counting directed two-step paths
`a → b → c` with `R₀₁ a b` and `R₁₂ b c`, over ordered boxes `A × B × C`. The path
density is within `6·ε` of the product `pairDensity R₀₁ A B · pairDensity R₁₂ B C` once
`(A, B)` is `ε`-uniform for `R₀₁` and `(B, C)` is `ε`-uniform for `R₁₂`
(`abs_directedPathDensity_sub_le`), with the raw box-scaled form
(`abs_directedPathCount_sub_le`).

The count is organized by the middle vertex `b ∈ B`: the number of paths through `b` is
the incoming degree from `A` times the outgoing degree into `C`
(`directedPathCount_eq_sum`), so the density is the `B`-average of the product of the two
one-vertex degrees (`directedPathDensity_eq`) — the incoming degree is a `swapRel R₀₁`
out-degree, which is why the transpose calculus is needed. The `6 = 2 + 4` splits as: on
non-exceptional middle vertices the product error is at most `2·ε` (two-factor
perturbation), and the exceptional middle vertices carry mass at most `4·ε·|B|` (two
two-sided degree-exceptional tails). No disjointness of `A`, `B`, `C` is assumed; that is
supplied only when translating to induced embeddings.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]
  (R₀₁ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₁₂]
  {A B C : Finset α} {ε : ℝ}

/-- The two-step directed path predicate on an ordered triple `(x 0, x 1, x 2)`. -/
def directedPathObs (R₀₁ R₁₂ : α → α → Prop) (x : Fin 3 → α) : Prop :=
  R₀₁ (x 0) (x 1) ∧ R₁₂ (x 1) (x 2)

instance (R₀₁ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₁₂] :
    DecidablePred (directedPathObs R₀₁ R₁₂) :=
  fun x => inferInstanceAs (Decidable (R₀₁ (x 0) (x 1) ∧ R₁₂ (x 1) (x 2)))

/-- The number of directed two-step paths with vertices in `A`, `B`, `C`. -/
def directedPathCount (R₀₁ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₁₂]
    (A B C : Finset α) : ℕ :=
  tupleCount (directedPathObs R₀₁ R₁₂) ![A, B, C]

/-- The directed two-step path density (guard-free). -/
noncomputable def directedPathDensity (R₀₁ R₁₂ : α → α → Prop)
    [DecidableRel R₀₁] [DecidableRel R₁₂] (A B C : Finset α) : ℝ :=
  tupleDensity (directedPathObs R₀₁ R₁₂) ![A, B, C]

/-! ### The middle-vertex fiber identities -/

/-- **Raw middle-fiber identity.** Paths are organized by their middle vertex: through
`b` there are (incoming degree from `A`) × (outgoing degree into `C`) paths. -/
theorem directedPathCount_eq_sum (A B C : Finset α) :
    directedPathCount R₀₁ R₁₂ A B C
      = ∑ b ∈ B, (A.filter fun a => R₀₁ a b).card * (C.filter fun c => R₁₂ b c).card := by
  rw [directedPathCount, tupleCount]
  have hmem : ∀ f ∈ (Fintype.piFinset ![A, B, C]).filter (directedPathObs R₀₁ R₁₂),
      f 1 ∈ B := by
    intro f hf
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    simpa using hf.1 1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun f _ => (f 0, f 2)) (fun p _ => ![p.1, b, p.2]) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset] at hf
    obtain ⟨⟨hpi, hobs1, hobs2⟩, hf1⟩ := hf
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨hpi 0, by rw [← hf1]; exact hobs1⟩, hpi 2, by rw [← hf1]; exact hobs2⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hp1A, hp1R⟩, hp2C, hp2R⟩ := hp
    rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨fun i => ?_, hp1R, hp2R⟩, rfl⟩
    fin_cases i
    · exact hp1A
    · exact hb
    · exact hp2C
  · intro f hf
    have hf1 : f 1 = b := (Finset.mem_filter.mp hf).2
    funext i
    fin_cases i
    · rfl
    · exact hf1.symm
    · rfl
  · intro p _
    rfl

/-- **Normalized middle-fiber identity** (guard-free): the path density is the `B`-average
of the product of the incoming (`swapRel R₀₁`) and outgoing (`R₁₂`) middle-vertex
degrees. -/
theorem directedPathDensity_eq (A B C : Finset α) :
    directedPathDensity R₀₁ R₁₂ A B C
      = (∑ b ∈ B, degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C) / B.card := by
  have hpi : ((Fintype.piFinset ![A, B, C]).card : ℝ) = A.card * B.card * C.card := by
    rw [Fintype.card_piFinset, Fin.prod_univ_three]
    push_cast
    rfl
  have hdeg : ∀ b, degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
      = ((A.filter fun a => R₀₁ a b).card * (C.filter fun c => R₁₂ b c).card : ℝ)
          / (A.card * C.card) := by
    intro b
    rw [degreeDensity_eq, degreeDensity_eq, div_mul_div_comm]
    rfl
  rw [directedPathDensity, tupleDensity_eq_count_div,
    show tupleCount (directedPathObs R₀₁ R₁₂) ![A, B, C] = directedPathCount R₀₁ R₁₂ A B C
      from rfl,
    directedPathCount_eq_sum, hpi, Finset.sum_congr rfl fun b _ => hdeg b]
  rw [← Finset.sum_div, Nat.cast_sum]
  push_cast
  rcases eq_or_ne (A.card : ℝ) 0 with hA | hA
  · simp [hA]
  rcases eq_or_ne (C.card : ℝ) 0 with hC | hC
  · simp [hC]
  rcases eq_or_ne (B.card : ℝ) 0 with hB | hB
  · simp [hB]
  · field_simp

/-! ### The path-counting approximation -/

/-- **Path-density approximation.** Under `ε`-uniformity of `(A, B)` for `R₀₁` and
`(B, C)` for `R₁₂`, the path density is within `6·ε = (2 + 4)·ε` of the product of the
two pair densities. The `2` is the two-factor perturbation on good middle vertices; the
`4` is the two-sided exceptional mass of the two middle-degree tails. -/
theorem abs_directedPathDensity_sub_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h12 : IsUniformPair R₁₂ B C ε) :
    |directedPathDensity R₀₁ R₁₂ A B C
        - pairDensity R₀₁ A B * pairDensity R₁₂ B C| ≤ 6 * ε := by
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · rw [directedPathDensity_eq]
    have h1 : pairDensity R₀₁ A ∅ = 0 := by rw [pairDensity_eq_count_div]; simp
    rw [h1, zero_mul]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_div, sub_zero, abs_zero]
    linarith
  have hBcard : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hBne
  have hswapU : IsUniformPair (swapRel R₀₁) B A ε := isUniformPair_swapRel R₀₁ h01
  set E := degreeExceptional (swapRel R₀₁) B A ε ∪ degreeExceptional R₁₂ B C ε with hEdef
  have hEsub : E ⊆ B := by
    rw [hEdef]
    exact Finset.union_subset (degreeExceptional_subset (swapRel R₀₁))
      (degreeExceptional_subset R₁₂)
  have hE : (E.card : ℝ) ≤ 4 * ε * B.card := by
    have h1 := card_degreeExceptional_le (swapRel R₀₁) hε0 hε1 hswapU
    have h2 := card_degreeExceptional_le R₁₂ hε0 hε1 h12
    have hu : (E.card : ℝ)
        ≤ ((degreeExceptional (swapRel R₀₁) B A ε).card : ℝ)
          + (degreeExceptional R₁₂ B C ε).card := by
      rw [hEdef]; exact_mod_cast Finset.card_union_le _ _
    linarith
  have hbad : ∀ b ∈ E, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
      - pairDensity R₀₁ A B * pairDensity R₁₂ B C| ≤ 1 := by
    intro b _
    have hu1 : degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C ≤ 1 := by
      nlinarith [degreeDensity_nonneg (swapRel R₀₁) b A, degreeDensity_le_one (swapRel R₀₁) b A,
        degreeDensity_nonneg R₁₂ b C, degreeDensity_le_one R₁₂ b C]
    have hu0 : 0 ≤ degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C :=
      mul_nonneg (degreeDensity_nonneg _ _ _) (degreeDensity_nonneg _ _ _)
    have hv1 : pairDensity R₀₁ A B * pairDensity R₁₂ B C ≤ 1 := by
      nlinarith [pairDensity_nonneg (R := R₀₁) (A := A) (B := B),
        pairDensity_le_one (R := R₀₁) (A := A) (B := B),
        pairDensity_nonneg (R := R₁₂) (A := B) (B := C),
        pairDensity_le_one (R := R₁₂) (A := B) (B := C)]
    have hv0 : 0 ≤ pairDensity R₀₁ A B * pairDensity R₁₂ B C :=
      mul_nonneg pairDensity_nonneg pairDensity_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hgood : ∀ b ∈ B \ E, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
      - pairDensity R₀₁ A B * pairDensity R₁₂ B C| ≤ 2 * ε := by
    intro b hb
    rw [Finset.mem_sdiff] at hb
    obtain ⟨hbB, hbE⟩ := hb
    rw [hEdef, Finset.mem_union, not_or] at hbE
    obtain ⟨hb1, hb2⟩ := hbE
    have hgA : |degreeDensity (swapRel R₀₁) b A - pairDensity R₀₁ A B| ≤ ε := by
      have hthis := abs_degreeDensity_sub_le_of_not_mem (swapRel R₀₁) hbB hb1
      rwa [pairDensity_swapRel] at hthis
    have hgC : |degreeDensity R₁₂ b C - pairDensity R₁₂ B C| ≤ ε :=
      abs_degreeDensity_sub_le_of_not_mem R₁₂ hbB hb2
    have hx1 : |degreeDensity (swapRel R₀₁) b A| ≤ 1 := by
      rw [abs_of_nonneg (degreeDensity_nonneg _ _ _)]; exact degreeDensity_le_one _ _ _
    have he1 : |pairDensity R₁₂ B C| ≤ 1 := by
      rw [abs_of_nonneg pairDensity_nonneg]; exact pairDensity_le_one
    calc |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
          - pairDensity R₀₁ A B * pairDensity R₁₂ B C|
        ≤ |degreeDensity (swapRel R₀₁) b A - pairDensity R₀₁ A B|
          + |degreeDensity R₁₂ b C - pairDensity R₁₂ B C| := abs_mul_sub_mul_le hx1 he1
      _ ≤ 2 * ε := by linarith
  have hsum : ∑ b ∈ B, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
      - pairDensity R₀₁ A B * pairDensity R₁₂ B C| ≤ 6 * ε * B.card := by
    have hcard : ((B \ E).card : ℝ) ≤ B.card :=
      by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    calc ∑ b ∈ B, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
          - pairDensity R₀₁ A B * pairDensity R₁₂ B C|
        = ∑ b ∈ B \ E, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
              - pairDensity R₀₁ A B * pairDensity R₁₂ B C|
          + ∑ b ∈ E, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
              - pairDensity R₀₁ A B * pairDensity R₁₂ B C| :=
          (Finset.sum_sdiff hEsub).symm
      _ ≤ ∑ _b ∈ B \ E, 2 * ε + ∑ _b ∈ E, (1 : ℝ) :=
          add_le_add (Finset.sum_le_sum hgood) (Finset.sum_le_sum hbad)
      _ = 2 * ε * (B \ E).card + E.card := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
      _ ≤ 2 * ε * B.card + 4 * ε * B.card := by
          have hmul : 2 * ε * ((B \ E).card : ℝ) ≤ 2 * ε * B.card :=
            mul_le_mul_of_nonneg_left hcard (by linarith)
          linarith
      _ = 6 * ε * B.card := by ring
  have hrw : (∑ b ∈ B, degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C) / (B.card : ℝ)
      - pairDensity R₀₁ A B * pairDensity R₁₂ B C
      = (∑ b ∈ B, (degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
          - pairDensity R₀₁ A B * pairDensity R₁₂ B C)) / B.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [directedPathDensity_eq, hrw, abs_div, abs_of_pos hBcard, div_le_iff₀ hBcard]
  calc |∑ b ∈ B, (degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
        - pairDensity R₀₁ A B * pairDensity R₁₂ B C)|
      ≤ ∑ b ∈ B, |degreeDensity (swapRel R₀₁) b A * degreeDensity R₁₂ b C
          - pairDensity R₀₁ A B * pairDensity R₁₂ B C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ 6 * ε * B.card := hsum

/-- **Raw box-scaled path-count approximation.** -/
theorem abs_directedPathCount_sub_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h12 : IsUniformPair R₁₂ B C ε) :
    |(directedPathCount R₀₁ R₁₂ A B C : ℝ)
        - pairDensity R₀₁ A B * pairDensity R₁₂ B C * A.card * B.card * C.card|
      ≤ 6 * ε * A.card * B.card * C.card := by
  have hM : (0 : ℝ) ≤ A.card * B.card * C.card := by positivity
  have hpicard : ((Fintype.piFinset ![A, B, C]).card : ℝ) = A.card * B.card * C.card := by
    rw [Fintype.card_piFinset, Fin.prod_univ_three]; push_cast; rfl
  have hden : (directedPathCount R₀₁ R₁₂ A B C : ℝ)
      = directedPathDensity R₀₁ R₁₂ A B C * (A.card * B.card * C.card) := by
    rw [directedPathDensity, tupleDensity_eq_count_div, ← hpicard,
      show tupleCount (directedPathObs R₀₁ R₁₂) ![A, B, C] = directedPathCount R₀₁ R₁₂ A B C
        from rfl]
    rcases eq_or_ne ((Fintype.piFinset ![A, B, C]).card : ℝ) 0 with h0 | h0
    · rw [h0, div_zero, zero_mul]
      have hpiempty : Fintype.piFinset ![A, B, C] = ∅ := by
        rw [← Finset.card_eq_zero]; exact_mod_cast h0
      rw [directedPathCount, tupleCount, hpiempty]
      simp
    · rw [div_mul_cancel₀ _ h0]
  have hd := abs_directedPathDensity_sub_le R₀₁ R₁₂ hε0 hε1 h01 h12
  rw [hden,
    show pairDensity R₀₁ A B * pairDensity R₁₂ B C * ↑A.card * ↑B.card * ↑C.card
      = pairDensity R₀₁ A B * pairDensity R₁₂ B C * (↑A.card * ↑B.card * ↑C.card) from by ring,
    ← sub_mul, abs_mul, abs_of_nonneg hM,
    show 6 * ε * ↑A.card * ↑B.card * ↑C.card = 6 * ε * (↑A.card * ↑B.card * ↑C.card) from by ring]
  exact mul_le_mul_of_nonneg_right hd hM

/-! ### Tests and adversarial examples -/

section Tests

-- Each empty coordinate separately kills the count.
example : directedPathCount (fun a b : Fin 2 => (a : ℕ) ≤ b) (fun a b => (a : ℕ) ≤ b)
    ∅ {0} {0} = 0 := by decide

example : directedPathCount (fun a b : Fin 2 => (a : ℕ) ≤ b) (fun a b => (a : ℕ) ≤ b)
    {0} ∅ {0} = 0 := by decide

example : directedPathCount (fun a b : Fin 2 => (a : ℕ) ≤ b) (fun a b => (a : ℕ) ≤ b)
    {0} {0} ∅ = 0 := by decide

-- Both relations complete: every one of the `2·2·2` ordered triples is a path.
example : directedPathCount (fun _ _ : Fin 2 => True) (fun _ _ => True)
    {0, 1} {0, 1} {0, 1} = 8 := by decide

-- One relation empty: no paths.
example : directedPathCount (fun _ _ : Fin 2 => True) (fun _ _ => False)
    {0, 1} {0, 1} {0, 1} = 0 := by decide

-- A concrete nontrivial count: `a ≤ b ≤ c` through `b = 1` reaching `{1, 2}` gives two
-- paths `(0,1,1)` and `(0,1,2)`.
example : directedPathCount (fun a b : Fin 3 => (a : ℕ) ≤ b) (fun a b => (a : ℕ) ≤ b)
    {0} {1} {1, 2} = 2 := by decide

-- **Direction test.** The middle vertex's contribution uses the *incoming* degree
-- `degreeDensity (swapRel R₀₁) b A` (vertices of `A` pointing into `b`), not the forward
-- `degreeDensity R₀₁ b A`. For `R₀₁ = (· < ·)` and `b = 1`, `A = {0}`: the incoming
-- degree is `1` (since `0 < 1`) while the forward degree is `0` (since `¬ 1 < 0`) — using
-- the forward degree would give the wrong (zero) middle contribution.
example :
    degreeDensity (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) 1 {0} = 1
      ∧ degreeDensity (fun a b : Fin 3 => (a : ℕ) < b) 1 {0} = 0 := by
  refine ⟨?_, ?_⟩
  · show pairDensity (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) {1} {0} = 1
    rw [pairDensity_eq_count_div,
      show pairCount (swapRel (fun a b : Fin 3 => (a : ℕ) < b)) {1} {0} = 1 from by decide,
      show ({1} : Finset (Fin 3)).card = 1 from by decide,
      show ({0} : Finset (Fin 3)).card = 1 from by decide]
    norm_num
  · show pairDensity (fun a b : Fin 3 => (a : ℕ) < b) {1} {0} = 0
    rw [pairDensity_eq_count_div,
      show pairCount (fun a b : Fin 3 => (a : ℕ) < b) {1} {0} = 0 from by decide]
    simp

-- Statement-level: any two `DecidableRel` relations feed the approximation. Palette-color
-- relations `HasBinaryPairPalette M c` are such relations, so this specializes to colored
-- path counting; that instantiation lives in the relational bridge (`Relational/*`), which
-- depends on `Graph/*`, so it cannot be stated here without a cyclic import.
example (R₀₁ R₁₂ : Fin 5 → Fin 5 → Prop) [DecidableRel R₀₁] [DecidableRel R₁₂]
    (A B C : Finset (Fin 5)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h12 : IsUniformPair R₁₂ B C ε) :
    |directedPathDensity R₀₁ R₁₂ A B C
        - pairDensity R₀₁ A B * pairDensity R₁₂ B C| ≤ 6 * ε :=
  abs_directedPathDensity_sub_le R₀₁ R₁₂ hε0 hε1 h01 h12

end Tests

end RegularityLemmata
