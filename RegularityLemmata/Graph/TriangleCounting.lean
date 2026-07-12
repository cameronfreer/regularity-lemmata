/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.RegularDegree
import RegularityLemmata.Graph.PathCounting
import RegularityLemmata.Finite.Density
import RegularityLemmata.Finite.Inequalities

/-!
# Directed triangle counting

Phase 10 unit 5 (design freeze in `ARCHITECTURE.md`): counting directed triangles
`a → b, a → c, b → c` with three **unrelated** relations `R₀₁ a b`, `R₀₂ a c`,
`R₁₂ b c`, over ordered boxes `A × B × C`. Under `ε`-uniformity of *all three* pairs
`(A,B)` for `R₀₁`, `(A,C)` for `R₀₂`, `(B,C)` for `R₁₂`, the triangle count is within
`7·ε·|A||B||C|` of `d₀₁·d₀₂·d₁₂·|A||B||C|` (`abs_directedTriangleCount_sub_le`).

The count is organized by the apex vertex `a ∈ A`: the triangles through `a` are the
`R₁₂`-pairs inside the neighborhoods `N_B(a) = B ∩ {b | R₀₁ a b}` and `N_C(a) = C ∩
{c | R₀₂ a c}` (`directedTriangleCount_eq_sum`). The constant **`7 = 1 + 2 + 4`** is
derived, not chosen:
* `1·ε` — the *neighborhood-threshold* term: on each apex, `|pairCount R₁₂ N_B(a) N_C(a)
  − d₁₂·|N_B(a)|·|N_C(a)|| ≤ ε·|B||C|`. When both neighborhoods are `ε`-large, uniformity
  of `(B,C)` applies; when either is small, both quantities live in `[0, |N_B||N_C|] ⊆
  [0, ε|B||C|]`, so no positive-density hypothesis is needed (this is the low-density case).
* `2·ε + 4·ε` — the apex-degree *correlation* term: the apex wedges `b → a → c` are a
  directed path in `(swapRel R₀₁, R₀₂)`, so `|∑_a deg₀₁(a)·deg₀₂(a) − d₀₁·d₀₂·|A|| ≤
  6·ε·|A|` is exactly the Unit-4 path-counting bound (`abs_directedPathCount_sub_le`) applied
  to the transpose — reused, not re-proved (`2·ε` non-exceptional two-factor perturbation plus
  `4·ε·|A|` exceptional degree mass, established there).

The apex-neighborhood organization parallels the private counting architecture of
`Mathlib.Combinatorics.SimpleGraph.Triangle.Counting` (Y. Dillies, B. Mehta); this is an
independently authored directed, two-sided absolute-error generalization (mathlib's theorem
is a positive-density lower bound).

Generic in the three relations; palette colors are an application, instantiated in the
relational bridge (which depends on `Graph/*`).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]
  (R₀₁ R₀₂ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂]
  {A B C : Finset α} {ε : ℝ}

/-- The directed triangle predicate on an ordered triple `(x 0, x 1, x 2)`. -/
def directedTriangleObs (R₀₁ R₀₂ R₁₂ : α → α → Prop) (x : Fin 3 → α) : Prop :=
  R₀₁ (x 0) (x 1) ∧ R₀₂ (x 0) (x 2) ∧ R₁₂ (x 1) (x 2)

instance (R₀₁ R₀₂ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂] :
    DecidablePred (directedTriangleObs R₀₁ R₀₂ R₁₂) :=
  fun x => inferInstanceAs (Decidable (R₀₁ (x 0) (x 1) ∧ R₀₂ (x 0) (x 2) ∧ R₁₂ (x 1) (x 2)))

/-- The number of directed triangles with vertices in `A`, `B`, `C`. -/
def directedTriangleCount (R₀₁ R₀₂ R₁₂ : α → α → Prop)
    [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂] (A B C : Finset α) : ℕ :=
  tupleCount (directedTriangleObs R₀₁ R₀₂ R₁₂) ![A, B, C]

/-- The directed triangle density (guard-free). -/
noncomputable def directedTriangleDensity (R₀₁ R₀₂ R₁₂ : α → α → Prop)
    [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂] (A B C : Finset α) : ℝ :=
  tupleDensity (directedTriangleObs R₀₁ R₀₂ R₁₂) ![A, B, C]

/-! ### The apex-vertex fiber identity -/

/-- **Apex fiber identity.** Triangles are organized by their apex `a`: through `a` there
are the `R₁₂`-pairs inside its two out-neighborhoods. -/
theorem directedTriangleCount_eq_sum (A B C : Finset α) :
    directedTriangleCount R₀₁ R₀₂ R₁₂ A B C
      = ∑ a ∈ A, pairCount R₁₂ (B.filter (R₀₁ a ·)) (C.filter (R₀₂ a ·)) := by
  rw [directedTriangleCount, tupleCount]
  have hmem : ∀ f ∈ (Fintype.piFinset ![A, B, C]).filter (directedTriangleObs R₀₁ R₀₂ R₁₂),
      f 0 ∈ A := by
    intro f hf
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    simpa using hf.1 0
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [pairCount]
  refine Finset.card_bij' (fun f _ => (f 1, f 2)) (fun p _ => ![a, p.1, p.2]) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset] at hf
    obtain ⟨⟨hpi, hobs1, hobs2, hobs3⟩, hf0⟩ := hf
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨⟨hpi 1, by rw [← hf0]; exact hobs1⟩, hpi 2, by rw [← hf0]; exact hobs2⟩, hobs3⟩
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨⟨hp1B, hp1R⟩, hp2C, hp2R⟩, hp3R⟩ := hp
    rw [Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨fun i => ?_, hp1R, hp2R, hp3R⟩, rfl⟩
    fin_cases i
    · exact ha
    · exact hp1B
    · exact hp2C
  · intro f hf
    have hf0 : f 0 = a := (Finset.mem_filter.mp hf).2
    funext i
    fin_cases i
    · exact hf0.symm
    · rfl
    · rfl
  · intro p _
    rfl

/-! ### The neighborhood-threshold (apex-local) bound -/

omit [DecidableEq α] in
/-- **Neighborhood-threshold bound.** On each apex, the `R₁₂`-count inside the two
neighborhoods is within `ε·|B||C|` of `d₁₂·|N_B(a)|·|N_C(a)|`, with no positive-density
hypothesis (the small-neighborhood / low-density case is absorbed). -/
private theorem abs_pairCount_nbhd_sub_le (hε0 : 0 ≤ ε)
    (h12 : IsUniformPair R₁₂ B C ε) (a : α) :
    |(pairCount R₁₂ (B.filter (R₀₁ a ·)) (C.filter (R₀₂ a ·)) : ℝ)
        - pairDensity R₁₂ B C
            * ((B.filter (R₀₁ a ·)).card * (C.filter (R₀₂ a ·)).card)|
      ≤ ε * B.card * C.card := by
  set NB := B.filter (R₀₁ a ·) with hNB
  set NC := C.filter (R₀₂ a ·) with hNC
  have hNBsub : NB ⊆ B := Finset.filter_subset _ _
  have hNCsub : NC ⊆ C := Finset.filter_subset _ _
  have hNBcard : (NB.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hNBsub
  have hNCcard : (NC.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card hNCsub
  by_cases hlarge : ε * B.card ≤ NB.card ∧ ε * C.card ≤ NC.card
  · obtain ⟨hlB, hlC⟩ := hlarge
    have hu := h12 hNBsub hNCsub hlB hlC
    rw [pairCount_eq_pairDensity_mul,
      show pairDensity R₁₂ NB NC * (↑NB.card * ↑NC.card)
          - pairDensity R₁₂ B C * (↑NB.card * ↑NC.card)
        = (pairDensity R₁₂ NB NC - pairDensity R₁₂ B C) * (↑NB.card * ↑NC.card) from by ring,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ↑NB.card * ↑NC.card)]
    calc |pairDensity R₁₂ NB NC - pairDensity R₁₂ B C| * (↑NB.card * ↑NC.card)
        ≤ ε * (↑B.card * ↑C.card) :=
          mul_le_mul hu (mul_le_mul hNBcard hNCcard (by positivity) (by positivity))
            (by positivity) hε0
      _ = ε * B.card * C.card := by ring
  · have hsmall : (↑NB.card * ↑NC.card : ℝ) ≤ ε * B.card * C.card := by
      rcases not_and_or.mp hlarge with h | h
      · have hb : (NB.card : ℝ) ≤ ε * B.card := (not_le.mp h).le
        calc (↑NB.card * ↑NC.card : ℝ) ≤ (ε * B.card) * C.card :=
              mul_le_mul hb hNCcard (by positivity) (by positivity)
          _ = ε * B.card * C.card := by ring
      · have hc : (NC.card : ℝ) ≤ ε * C.card := (not_le.mp h).le
        calc (↑NB.card * ↑NC.card : ℝ) ≤ B.card * (ε * C.card) :=
              mul_le_mul hNBcard hc (by positivity) (by positivity)
          _ = ε * B.card * C.card := by ring
    have hpc1 : (pairCount R₁₂ NB NC : ℝ) ≤ ↑NB.card * ↑NC.card := by
      have hnat : pairCount R₁₂ NB NC ≤ NB.card * NC.card := by
        rw [pairCount, ← Finset.card_product]; exact Finset.card_filter_le _ _
      exact_mod_cast hnat
    have hpc0 : (0 : ℝ) ≤ pairCount R₁₂ NB NC := Nat.cast_nonneg _
    have hd12 : pairDensity R₁₂ B C ≤ 1 := pairDensity_le_one
    have hd12' : (0 : ℝ) ≤ pairDensity R₁₂ B C := pairDensity_nonneg
    have hM : (0 : ℝ) ≤ ↑NB.card * ↑NC.card := by positivity
    rw [abs_le]
    constructor
    · nlinarith [hpc1, hsmall, hM, hd12, hd12']
    · nlinarith [hpc0, hsmall, hM, hd12, hd12']

/-! ### The triangle-counting approximation -/

/-- **Triangle-count approximation.** Under `ε`-uniformity of all three pairs, the
directed triangle count is within `7·ε·|A||B||C|` of `d₀₁·d₀₂·d₁₂·|A||B||C|`, with
`7 = 1 + 2 + 4` derived (apex-neighborhood threshold + apex-degree correlation). -/
theorem abs_directedTriangleCount_sub_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    |(directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
        - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card := by
  have hfib : (directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
      = ∑ a ∈ A, (pairCount R₁₂ (B.filter (R₀₁ a ·)) (C.filter (R₀₂ a ·)) : ℝ) := by
    rw [directedTriangleCount_eq_sum, Nat.cast_sum]
  -- The apex wedges `b → a → c` form a directed path in `(swapRel R₀₁, R₀₂)`.
  have hW : (directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)
      = ∑ a ∈ A, ((B.filter (R₀₁ a ·)).card : ℝ) * (C.filter (R₀₂ a ·)).card := by
    rw [directedPathCount_eq_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    rfl
  have hstep1 : |(directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
      - pairDensity R₁₂ B C * (directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)|
      ≤ ε * A.card * B.card * C.card := by
    rw [hfib, hW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ a ∈ A, |(pairCount R₁₂ (B.filter (R₀₁ a ·)) (C.filter (R₀₂ a ·)) : ℝ)
            - pairDensity R₁₂ B C
                * ((B.filter (R₀₁ a ·)).card * (C.filter (R₀₂ a ·)).card)|
        ≤ ∑ _a ∈ A, ε * B.card * C.card :=
          Finset.sum_le_sum fun a _ => abs_pairCount_nbhd_sub_le R₀₁ R₀₂ R₁₂ hε0 h12 a
      _ = ε * A.card * B.card * C.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- The wedge count is `6·ε`-close to `d₀₁·d₀₂·|A||B||C|` — Unit 4 on the transpose.
  have hcorr : |(directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)
      - pairDensity R₀₁ A B * pairDensity R₀₂ A C * (A.card * B.card * C.card)|
      ≤ 6 * ε * (A.card * B.card * C.card) := by
    have hpath := abs_directedPathCount_sub_le (swapRel R₀₁) R₀₂ hε0 hε1
      (isUniformPair_swapRel R₀₁ h01) h02
    rw [pairDensity_swapRel] at hpath
    rw [show pairDensity R₀₁ A B * pairDensity R₀₂ A C * (↑A.card * ↑B.card * ↑C.card)
          = pairDensity R₀₁ A B * pairDensity R₀₂ A C * ↑B.card * ↑A.card * ↑C.card from by ring,
      show (6 : ℝ) * ε * (↑A.card * ↑B.card * ↑C.card) = 6 * ε * ↑B.card * ↑A.card * ↑C.card
        from by ring]
    exact hpath
  have hstep2 : |pairDensity R₁₂ B C * (directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)
      - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
          * A.card * B.card * C.card|
      ≤ 6 * ε * A.card * B.card * C.card := by
    rw [show pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
          * ↑A.card * ↑B.card * ↑C.card
        = pairDensity R₁₂ B C
            * (pairDensity R₀₁ A B * pairDensity R₀₂ A C * (↑A.card * ↑B.card * ↑C.card))
        from by ring,
      ← mul_sub, abs_mul, abs_of_nonneg pairDensity_nonneg]
    calc pairDensity R₁₂ B C
          * |(directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)
              - pairDensity R₀₁ A B * pairDensity R₀₂ A C * (↑A.card * ↑B.card * ↑C.card)|
        ≤ 1 * (6 * ε * (↑A.card * ↑B.card * ↑C.card)) :=
          mul_le_mul pairDensity_le_one hcorr (abs_nonneg _) (by norm_num)
      _ = 6 * ε * A.card * B.card * C.card := by ring
  calc |(directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
        - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
            * A.card * B.card * C.card|
      ≤ |(directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
            - pairDensity R₁₂ B C * (directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)|
        + |pairDensity R₁₂ B C * (directedPathCount (swapRel R₀₁) R₀₂ B A C : ℝ)
            - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
                * A.card * B.card * C.card| := abs_sub_le _ _ _
    _ ≤ ε * A.card * B.card * C.card + 6 * ε * A.card * B.card * C.card :=
        add_le_add hstep1 hstep2
    _ = 7 * ε * A.card * B.card * C.card := by ring

/-- **Density form** of the triangle-count approximation. -/
theorem abs_directedTriangleDensity_sub_le (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    |directedTriangleDensity R₀₁ R₀₂ R₁₂ A B C
        - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C| ≤ 7 * ε := by
  have hraw := abs_directedTriangleCount_sub_le R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  have hden : directedTriangleDensity R₀₁ R₀₂ R₁₂ A B C
      = (directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ) / (↑A.card * ↑B.card * ↑C.card) := by
    rw [directedTriangleDensity, tupleDensity_eq_count_div,
      show tupleCount (directedTriangleObs R₀₁ R₀₂ R₁₂) ![A, B, C]
        = directedTriangleCount R₀₁ R₀₂ R₁₂ A B C from rfl]
    congr 1
    rw [Fintype.card_piFinset, Fin.prod_univ_three]; push_cast; rfl
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ↑A.card * ↑B.card * ↑C.card by positivity) with hM | hM
  · rw [hden, ← hM, div_zero]
    have hprod : pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C = 0 := by
      have hM0 : (↑A.card : ℝ) * ↑B.card * ↑C.card = 0 := hM.symm
      rcases mul_eq_zero.mp hM0 with hAB | hC
      · rcases mul_eq_zero.mp hAB with hA | hB
        · have hAe : A = ∅ := by rw [← Finset.card_eq_zero]; exact_mod_cast hA
          subst hAe
          rw [show pairDensity R₀₁ ∅ B = 0 by rw [pairDensity_eq_count_div]; simp]; ring
        · have hBe : B = ∅ := by rw [← Finset.card_eq_zero]; exact_mod_cast hB
          subst hBe
          rw [show pairDensity R₀₁ A ∅ = 0 by rw [pairDensity_eq_count_div]; simp]; ring
      · have hCe : C = ∅ := by rw [← Finset.card_eq_zero]; exact_mod_cast hC
        subst hCe
        rw [show pairDensity R₀₂ A ∅ = 0 by rw [pairDensity_eq_count_div]; simp]; ring
    rw [hprod]; simp only [sub_zero, abs_zero]; linarith
  · have hkey : ∀ x y c M : ℝ, 0 < M → |x - y * M| ≤ c * M → |x / M - y| ≤ c := by
      intro x y c M hM hxy
      rw [show x / M - y = (x - y * M) / M by field_simp, abs_div, abs_of_pos hM,
        div_le_iff₀ hM]
      exact hxy
    rw [hden]
    refine hkey _ _ _ _ hM ?_
    rw [show pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
          * (↑A.card * ↑B.card * ↑C.card)
        = pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
            * ↑A.card * ↑B.card * ↑C.card by ring,
      show (7 : ℝ) * ε * (↑A.card * ↑B.card * ↑C.card) = 7 * ε * ↑A.card * ↑B.card * ↑C.card by ring]
    exact hraw

/-- **Positive lower bound.** The count is at least `(d₀₁·d₀₂·d₁₂ − 7·ε)·|A||B||C|`; in
particular it is positive once the three densities' product exceeds `7·ε`. -/
theorem directedTriangleCount_ge (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C * A.card * B.card * C.card
        - 7 * ε * A.card * B.card * C.card
      ≤ directedTriangleCount R₀₁ R₀₂ R₁₂ A B C := by
  have h := abs_directedTriangleCount_sub_le R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [abs_le] at h
  linarith [h.1]

/-! ### Tests and adversarial examples -/

section Tests

-- Complete relations: all `2·2·2` triangles present.
example : directedTriangleCount (fun _ _ : Fin 2 => True) (fun _ _ => True) (fun _ _ => True)
    {0, 1} {0, 1} {0, 1} = 8 := by decide

-- An empty box kills the count.
example : directedTriangleCount (fun _ _ : Fin 2 => True) (fun _ _ => True) (fun _ _ => True)
    ∅ {0} {0} = 0 := by decide

-- One missing color (a `False` relation) kills the count.
example : directedTriangleCount (fun _ _ : Fin 2 => True) (fun _ _ => True) (fun _ _ => False)
    {0, 1} {0, 1} {0, 1} = 0 := by decide

-- A concrete nontrivial triangle: `0 < 1`, `0 < 2`, `1 < 2` gives exactly one.
example : directedTriangleCount (fun a b : Fin 3 => (a : ℕ) < b) (fun a c => (a : ℕ) < c)
    (fun b c => (b : ℕ) < c) {0} {1} {2} = 1 := by decide

-- **Pairwise densities alone do not determine the triangle count.** Three relations each of
-- pairwise density `1/2` on `Fin 2`, but with *no* triangle: `a = b`, `a = c`, `b ≠ c` forces
-- `a = b = c` yet `b ≠ c`. The naive product estimate `d₀₁·d₀₂·d₁₂·|A||B||C| = (1/2)³·8 = 1`
-- is wrong (true count `0`); the three pairwise densities do not pin down the count. (This is
-- why the theorem's uniformity hypotheses are needed, beyond mere density values.)
example :
    directedTriangleCount (fun a b : Fin 2 => a = b) (fun a c => a = c) (fun b c => b ≠ c)
        {0, 1} {0, 1} {0, 1} = 0
      ∧ pairCount (fun a b : Fin 2 => a = b) {0, 1} {0, 1} = 2
      ∧ pairCount (fun a c : Fin 2 => a = c) {0, 1} {0, 1} = 2
      ∧ pairCount (fun b c : Fin 2 => b ≠ c) {0, 1} {0, 1} = 2 := by decide

-- **Reversing a relation changes the count.** Replacing `R₁₂` by its transpose turns the
-- single `0 < 1 < 2` triangle into none (`¬ 2 < 1`).
example :
    directedTriangleCount (fun a b : Fin 3 => (a : ℕ) < b) (fun a c => (a : ℕ) < c)
        (fun b c => (b : ℕ) < c) {0} {1} {2} = 1
      ∧ directedTriangleCount (fun a b : Fin 3 => (a : ℕ) < b) (fun a c => (a : ℕ) < c)
        (swapRel (fun b c : Fin 3 => (b : ℕ) < c)) {0} {1} {2} = 0 := by decide

-- Statement-level: three `DecidableRel` relations feed the approximation (palette colors
-- are such relations; that instantiation lives in the relational bridge).
example (R₀₁ R₀₂ R₁₂ : Fin 5 → Fin 5 → Prop)
    [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂]
    (A B C : Finset (Fin 5)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    |(directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
        - pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card :=
  abs_directedTriangleCount_sub_le R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12

end Tests

end RegularityLemmata
