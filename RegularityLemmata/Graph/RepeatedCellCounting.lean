/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.TriangleCounting

/-!
# Phase 11 unit 6: five-stratum repeated-cell counting

The placement combinatorics and injective counting bounds for triples whose boxes may
coincide (Phase 11 design freeze in `ARCHITECTURE.md`). Coarse-cell **coincidence** is
kept strictly separate from vertex **collision** throughout: the counted embeddings
are injective in every stratum; only the boxes repeat.

**Exact combinatorics first.** A triple of cells `T : Fin 3 → β` falls into exactly one
of FIVE placement classes (`PlacementClass`): all distinct, exactly `0 = 1`, exactly
`0 = 2`, exactly `1 = 2`, or all equal. The classifying map `placementClass` is total
(exhaustiveness) with disjoint fibers (a function has one value), each class is
characterized (`placementClass_eq_*_iff`), and any sum over triples decomposes
**exactly** over the five strata (`sum_placementClass_fiberwise`) — before any
inequality is stated.

**Analytic bounds second** (same file, second commit): box-restricted collision
estimates, then full-square-density lower bounds for the injective palette-realizing
count in each stratum.
-/

namespace RegularityLemmata

/-! ### The five placement classes -/

/-- The five placement classes of a triple: all coordinates distinct; exactly one of
the three coincidences `0 = 1`, `0 = 2`, `1 = 2`; or all equal. -/
inductive PlacementClass : Type
  /-- All three coordinates distinct. -/
  | allDistinct : PlacementClass
  /-- Exactly `0 = 1` (and both differ from `2`). -/
  | eq01 : PlacementClass
  /-- Exactly `0 = 2` (and both differ from `1`). -/
  | eq02 : PlacementClass
  /-- Exactly `1 = 2` (and both differ from `0`). -/
  | eq12 : PlacementClass
  /-- All three coordinates equal. -/
  | allEqual : PlacementClass
  deriving DecidableEq, Repr

instance : Fintype PlacementClass :=
  ⟨{.allDistinct, .eq01, .eq02, .eq12, .allEqual}, fun c => by cases c <;> decide⟩

variable {β : Type*} [DecidableEq β]

/-- The placement class of a triple. Totality of this map is the exhaustiveness of the
five strata; disjointness is automatic (a function takes one value). -/
def placementClass (T : Fin 3 → β) : PlacementClass :=
  if T 0 = T 1 then (if T 1 = T 2 then .allEqual else .eq01)
  else if T 0 = T 2 then .eq02
  else if T 1 = T 2 then .eq12
  else .allDistinct

/-! ### Characterizations (the disjointness content, made explicit) -/

omit [DecidableEq β] in
/-- Injectivity of a `Fin 3`-triple is the conjunction of the three disequalities
(the Graph-layer counterpart of the relational collision characterization). -/
theorem injective_fin_three_iff {T : Fin 3 → β} :
    Function.Injective T ↔ T 0 ≠ T 1 ∧ T 0 ≠ T 2 ∧ T 1 ≠ T 2 := by
  constructor
  · intro h
    exact ⟨fun e => absurd (h e) (by decide), fun e => absurd (h e) (by decide),
      fun e => absurd (h e) (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ a b hab
    fin_cases a <;> fin_cases b <;> simp_all

theorem placementClass_eq_allDistinct_iff {T : Fin 3 → β} :
    placementClass T = .allDistinct ↔ T 0 ≠ T 1 ∧ T 0 ≠ T 2 ∧ T 1 ≠ T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_allDistinct_iff_injective {T : Fin 3 → β} :
    placementClass T = .allDistinct ↔ Function.Injective T := by
  rw [placementClass_eq_allDistinct_iff, injective_fin_three_iff]

theorem placementClass_eq_allEqual_iff {T : Fin 3 → β} :
    placementClass T = .allEqual ↔ T 0 = T 1 ∧ T 1 = T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq01_iff {T : Fin 3 → β} :
    placementClass T = .eq01 ↔ T 0 = T 1 ∧ T 1 ≠ T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq02_iff {T : Fin 3 → β} :
    placementClass T = .eq02 ↔ T 0 = T 2 ∧ T 0 ≠ T 1 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq12_iff {T : Fin 3 → β} :
    placementClass T = .eq12 ↔ T 1 = T 2 ∧ T 0 ≠ T 1 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all
  exact fun h => h01 h.symm

/-- In the two one-coincidence strata that omit it, the third pair is automatically
distinct: `eq01` forces `T 0 ≠ T 2`, … -/
theorem ne_of_placementClass_eq_eq01 {T : Fin 3 → β}
    (h : placementClass T = .eq01) : T 0 ≠ T 2 := by
  rw [placementClass_eq_eq01_iff] at h
  exact fun h02 => h.2 (h.1.symm.trans h02)

/-- … and `eq12` forces `T 0 ≠ T 2`. -/
theorem ne_of_placementClass_eq_eq12 {T : Fin 3 → β}
    (h : placementClass T = .eq12) : T 0 ≠ T 2 := by
  rw [placementClass_eq_eq12_iff] at h
  exact fun h02 => h.2 (h02.trans h.1.symm)

/-! ### The exact five-stratum decomposition -/

/-- **The exact decomposition.** Any sum over a finite set of triples splits exactly
over the five placement strata — disjointness and exhaustiveness in one identity,
before any inequality. -/
theorem sum_placementClass_fiberwise {M : Type*} [AddCommMonoid M]
    (S : Finset (Fin 3 → β)) (f : (Fin 3 → β) → M) :
    ∑ c : PlacementClass, ∑ T ∈ S.filter (fun T => placementClass T = c), f T
      = ∑ T ∈ S, f T :=
  Finset.sum_fiberwise S placementClass f

/-! ### Injective counts with possibly coinciding boxes -/

variable {α : Type*} [DecidableEq α]
  (R₀₁ R₀₂ R₁₂ : α → α → Prop) [DecidableRel R₀₁] [DecidableRel R₀₂] [DecidableRel R₁₂]
  {ε : ℝ}

/-- The injective directed-triangle count: injective triples realizing all three
relations, with vertices in the (possibly coinciding) boxes `A`, `B`, `C`. Coarse-cell
coincidence is a property of the boxes; the counted tuples are injective in EVERY
stratum. -/
def injectiveTriangleCount (A B C : Finset α) : ℕ :=
  ((Fintype.piFinset ![A, B, C]).filter fun x =>
    directedTriangleObs R₀₁ R₀₂ R₁₂ x ∧ Function.Injective x).card

theorem injectiveTriangleCount_le_directedTriangleCount (A B C : Finset α) :
    injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B C ≤ directedTriangleCount R₀₁ R₀₂ R₁₂ A B C := by
  rw [injectiveTriangleCount, directedTriangleCount, tupleCount]
  refine Finset.card_le_card fun x hx => ?_
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

/-- **The exact injective/collision split** of the tuple count. -/
theorem directedTriangleCount_eq_injective_add_noninjective (A B C : Finset α) :
    directedTriangleCount R₀₁ R₀₂ R₁₂ A B C
      = injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B C
        + ((Fintype.piFinset ![A, B, C]).filter fun x =>
            directedTriangleObs R₀₁ R₀₂ R₁₂ x ∧ ¬ Function.Injective x).card := by
  rw [directedTriangleCount, tupleCount, injectiveTriangleCount,
    ← Finset.filter_filter (directedTriangleObs R₀₁ R₀₂ R₁₂) Function.Injective,
    ← Finset.filter_filter (directedTriangleObs R₀₁ R₀₂ R₁₂) (¬ Function.Injective ·)]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-! ### Box-restricted collision estimates -/

theorem card_filter_piFinset_zero_eq_one_le (A B C : Finset α) :
    ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1).card
      ≤ (A ∩ B).card * C.card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => (x 0, x 2)) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
    have h0 := hx.1 0
    have h1 := hx.1 1
    have h2 := hx.1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_inter.mpr ⟨h0, hx.2 ▸ h1⟩, by simpa using h2⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    rw [Prod.mk.injEq] at hxy
    have e0 : x 0 = y 0 := hxy.1
    have e2 : x 2 = y 2 := hxy.2
    have e1 : x 1 = y 1 := by rw [← hx.2, ← hy.2]; exact e0
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

theorem card_filter_piFinset_zero_eq_two_le (A B C : Finset α) :
    ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2).card
      ≤ (A ∩ C).card * B.card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => (x 0, x 1)) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
    have h0 := hx.1 0
    have h1 := hx.1 1
    have h2 := hx.1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_inter.mpr ⟨h0, hx.2 ▸ h2⟩, by simpa using h1⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    rw [Prod.mk.injEq] at hxy
    have e0 : x 0 = y 0 := hxy.1
    have e1 : x 1 = y 1 := hxy.2
    have e2 : x 2 = y 2 := by rw [← hx.2, ← hy.2]; exact e0
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

theorem card_filter_piFinset_one_eq_two_le (A B C : Finset α) :
    ((Fintype.piFinset ![A, B, C]).filter fun x => x 1 = x 2).card
      ≤ A.card * (B ∩ C).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => (x 0, x 1)) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
    have h0 := hx.1 0
    have h1 := hx.1 1
    have h2 := hx.1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨by simpa using h0, Finset.mem_inter.mpr ⟨h1, hx.2 ▸ h2⟩⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    rw [Prod.mk.injEq] at hxy
    have e0 : x 0 = y 0 := hxy.1
    have e1 : x 1 = y 1 := hxy.2
    have e2 : x 2 = y 2 := by rw [← hx.2, ← hy.2]; exact e1
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

/-- The non-injective mass is bounded by the three box-restricted collision terms. -/
theorem card_filter_noninjective_le (A B C : Finset α) :
    ((Fintype.piFinset ![A, B, C]).filter fun x =>
        directedTriangleObs R₀₁ R₀₂ R₁₂ x ∧ ¬ Function.Injective x).card
      ≤ (A ∩ B).card * C.card + (A ∩ C).card * B.card + A.card * (B ∩ C).card := by
  have hsub : (Fintype.piFinset ![A, B, C]).filter (fun x =>
        directedTriangleObs R₀₁ R₀₂ R₁₂ x ∧ ¬ Function.Injective x)
      ⊆ ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1)
        ∪ ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2)
        ∪ ((Fintype.piFinset ![A, B, C]).filter fun x => x 1 = x 2) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hcase : x 0 = x 1 ∨ x 0 = x 2 ∨ x 1 = x 2 := by
      by_contra hcon
      push Not at hcon
      exact hx.2.2 (injective_fin_three_iff.mpr ⟨hcon.1, hcon.2.1, hcon.2.2⟩)
    rw [Finset.mem_union, Finset.mem_union]
    rcases hcase with h | h | h
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hx.1, h⟩))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hx.1, h⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hx.1, h⟩)
  calc ((Fintype.piFinset ![A, B, C]).filter fun x =>
        directedTriangleObs R₀₁ R₀₂ R₁₂ x ∧ ¬ Function.Injective x).card
      ≤ (((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1)
          ∪ ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2)
          ∪ ((Fintype.piFinset ![A, B, C]).filter fun x => x 1 = x 2)).card :=
        Finset.card_le_card hsub
    _ ≤ (((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1)
          ∪ ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2)).card
        + ((Fintype.piFinset ![A, B, C]).filter fun x => x 1 = x 2).card :=
        Finset.card_union_le _ _
    _ ≤ ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1).card
        + ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2).card
        + ((Fintype.piFinset ![A, B, C]).filter fun x => x 1 = x 2).card := by
        have := Finset.card_union_le
          ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 1)
          ((Fintype.piFinset ![A, B, C]).filter fun x => x 0 = x 2)
        omega
    _ ≤ (A ∩ B).card * C.card + (A ∩ C).card * B.card + A.card * (B ∩ C).card :=
        add_le_add (add_le_add (card_filter_piFinset_zero_eq_one_le A B C)
          (card_filter_piFinset_zero_eq_two_le A B C))
          (card_filter_piFinset_one_eq_two_le A B C)

/-! ### The full-square-density lower bound, generic in the boxes -/

/-- **The generic injective lower bound** — "density product − regularity error −
collision slack", for arbitrary (possibly coinciding) boxes. Full-square densities
throughout; the collision slack is the exact box-restricted intersection mass. -/
theorem injectiveTriangleCount_ge {A B C : Finset α} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
        * A.card * B.card * C.card
      - 7 * ε * A.card * B.card * C.card
      - ((A ∩ B).card * C.card + (A ∩ C).card * B.card + A.card * (B ∩ C).card)
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ) := by
  have hdtc := directedTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  have hsplit := directedTriangleCount_eq_injective_add_noninjective R₀₁ R₀₂ R₁₂ A B C
  have hcoll := card_filter_noninjective_le R₀₁ R₀₂ R₁₂ A B C
  have hkey : (directedTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ)
        + ((A ∩ B).card * C.card + (A ∩ C).card * B.card + A.card * (B ∩ C).card) := by
    rw [hsplit]
    push_cast
    have := (Nat.cast_le (α := ℝ)).mpr hcoll
    push_cast at this
    linarith
  linarith

/-! ### The five stratum instances -/

/-- **Transversal stratum**: pairwise-disjoint boxes carry ZERO collision slack. -/
theorem injectiveTriangleCount_ge_of_disjoint {A B C : Finset α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A C ε)
    (h12 : IsUniformPair R₁₂ B C ε) :
    pairDensity R₀₁ A B * pairDensity R₀₂ A C * pairDensity R₁₂ B C
        * A.card * B.card * C.card
      - 7 * ε * A.card * B.card * C.card
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B C : ℝ) := by
  have h := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [Finset.disjoint_iff_inter_eq_empty.mp hAB, Finset.disjoint_iff_inter_eq_empty.mp hAC,
    Finset.disjoint_iff_inter_eq_empty.mp hBC] at h
  simpa using h

/-- **Stratum `0 = 1`** (boxes `(A, A, B)`, `A` and `B` disjoint): slack `|A|·|B|`.
The `R₀₁` uniformity hypothesis is on the DIAGONAL pair `(A, A)`. -/
theorem injectiveTriangleCount_ge_eq01 {A B : Finset α} (hAB : Disjoint A B)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A A ε) (h02 : IsUniformPair R₀₂ A B ε)
    (h12 : IsUniformPair R₁₂ A B ε) :
    pairDensity R₀₁ A A * pairDensity R₀₂ A B * pairDensity R₁₂ A B
        * A.card * A.card * B.card
      - 7 * ε * A.card * A.card * B.card
      - A.card * B.card
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A A B : ℝ) := by
  have h := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [Finset.inter_self, Finset.disjoint_iff_inter_eq_empty.mp hAB] at h
  simpa using h

/-- **Stratum `0 = 2`** (boxes `(A, B, A)`): slack `|A|·|B|`; `R₀₂` on the diagonal. -/
theorem injectiveTriangleCount_ge_eq02 {A B : Finset α} (hAB : Disjoint A B)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A A ε)
    (h12 : IsUniformPair R₁₂ B A ε) :
    pairDensity R₀₁ A B * pairDensity R₀₂ A A * pairDensity R₁₂ B A
        * A.card * B.card * A.card
      - 7 * ε * A.card * B.card * A.card
      - A.card * B.card
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B A : ℝ) := by
  have h := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [Finset.disjoint_iff_inter_eq_empty.mp hAB, Finset.inter_self,
    Finset.disjoint_iff_inter_eq_empty.mp hAB.symm] at h
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add] at h
  linarith

/-- **Stratum `1 = 2`** (boxes `(A, B, B)`): slack `|A|·|B|`; `R₁₂` on the diagonal. -/
theorem injectiveTriangleCount_ge_eq12 {A B : Finset α} (hAB : Disjoint A B)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A B ε) (h02 : IsUniformPair R₀₂ A B ε)
    (h12 : IsUniformPair R₁₂ B B ε) :
    pairDensity R₀₁ A B * pairDensity R₀₂ A B * pairDensity R₁₂ B B
        * A.card * B.card * B.card
      - 7 * ε * A.card * B.card * B.card
      - A.card * B.card
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A B B : ℝ) := by
  have h := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [Finset.disjoint_iff_inter_eq_empty.mp hAB, Finset.inter_self] at h
  simpa using h

/-- **Stratum all-equal** (boxes `(A, A, A)`): slack `3·|A|²`; ALL three uniformity
hypotheses are on the diagonal pair `(A, A)`. -/
theorem injectiveTriangleCount_ge_allEqual {A : Finset α}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair R₀₁ A A ε) (h02 : IsUniformPair R₀₂ A A ε)
    (h12 : IsUniformPair R₁₂ A A ε) :
    pairDensity R₀₁ A A * pairDensity R₀₂ A A * pairDensity R₁₂ A A
        * A.card * A.card * A.card
      - 7 * ε * A.card * A.card * A.card
      - 3 * (A.card * A.card)
      ≤ (injectiveTriangleCount R₀₁ R₀₂ R₁₂ A A A : ℝ) := by
  have h := injectiveTriangleCount_ge R₀₁ R₀₂ R₁₂ hε0 hε1 h01 h02 h12
  rw [Finset.inter_self] at h
  linarith

/-! ### Tests and adversarial examples -/

section Tests

-- The classifier is exhaustive and computes on the nose.
example : placementClass (![0, 1, 2] : Fin 3 → Fin 3) = .allDistinct := by decide
example : placementClass (![0, 0, 2] : Fin 3 → Fin 3) = .eq01 := by decide
example : placementClass (![0, 1, 0] : Fin 3 → Fin 3) = .eq02 := by decide
example : placementClass (![0, 1, 1] : Fin 3 → Fin 3) = .eq12 := by decide
example : placementClass (![1, 1, 1] : Fin 3 → Fin 3) = .allEqual := by decide

-- Disjointness, concretely: no triple lies in two strata (the classifier is a
-- function), and each characterization excludes the others.
example (T : Fin 3 → Fin 5) : ¬(placementClass T = .eq01 ∧ placementClass T = .eq02) :=
  fun ⟨h1, h2⟩ => by rw [h1] at h2; exact absurd h2 (by decide)

-- The exact decomposition on a concrete sum: counting all 27 triples of `Fin 3` by
-- stratum gives 6 + 6 + 6 + 6 + 3 = 27.
example :
    (((Finset.univ : Finset (Fin 3 → Fin 3))).filter
        (fun T => placementClass T = .allDistinct)).card = 6 ∧
      ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
        (fun T => placementClass T = .eq01)).card = 6 ∧
      ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
        (fun T => placementClass T = .allEqual)).card = 3 := by decide

example :
    ∑ c : PlacementClass, ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
      (fun T => placementClass T = c)).card = 27 := by decide

-- **Adversarial: coincident boxes.** With all three boxes equal to a two-element set
-- and the always-true relation, the tuple count is 8 but NO injective triple exists —
-- the collision slack (here `3·|A|² = 12 ≥ 8`) is genuinely needed, and an accidental
-- transversal assumption would wrongly report 8.
example : directedTriangleCount (fun _ _ : Fin 2 => True) (fun _ _ => True)
    (fun _ _ => True) {0, 1} {0, 1} {0, 1} = 8 := by decide

example : injectiveTriangleCount (fun _ _ : Fin 2 => True) (fun _ _ => True)
    (fun _ _ => True) {0, 1} {0, 1} {0, 1} = 0 := by decide

-- **Adversarial: repeated boxes still carry injective embeddings** — coarse-cell
-- coincidence is NOT vertex collision: the coincident three-element box has all 6
-- injective triples.
example : injectiveTriangleCount (fun _ _ : Fin 3 => True) (fun _ _ => True)
    (fun _ _ => True) {0, 1, 2} {0, 1, 2} {0, 1, 2} = 6 := by decide

-- **Adversarial: overlapping (unequal) boxes.** `A = {0,1}`, `B = {1,2}`, `C = {0,2}`:
-- 8 tuples, exactly 2 injective; the box-restricted slack
-- `|A∩B||C| + |A∩C||B| + |A||B∩C| = 2+2+2 = 6` makes the generic lower bound TIGHT
-- here (`8 − 6 = 2`).
example : directedTriangleCount (fun _ _ : Fin 3 => True) (fun _ _ => True)
    (fun _ _ => True) {0, 1} {1, 2} {0, 2} = 8 := by decide

example : injectiveTriangleCount (fun _ _ : Fin 3 => True) (fun _ _ => True)
    (fun _ _ => True) {0, 1} {1, 2} {0, 2} = 2 := by decide

-- The exact split, concretely: 8 = 2 injective + 6 collisions on the overlapping boxes.
example : ((Fintype.piFinset ![({0, 1} : Finset (Fin 3)), {1, 2}, {0, 2}]).filter
    fun x => (True ∧ True ∧ True) ∧ ¬ Function.Injective x).card = 6 := by decide

end Tests

end RegularityLemmata
