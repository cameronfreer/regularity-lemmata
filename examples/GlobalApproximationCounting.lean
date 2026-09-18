/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.RelationalApproximation
import RegularityLemmata.Relational.UniformPatternCounts
import RegularityLemmata.Relational.DiagonalLoopRegression

/-!
# Global approximation, then counting: the recipe and its diagonal boundary

One compiled consumer composing the global coordinate-defect approximation
(`exists_equitable_isIndivisibleFor`: majority rounding at an old partition, then transport
along an equitable representative map) with the released uniform counting transfers of
`RegularityLemmata/Relational/UniformPatternCounts.lean`.

**Positive half.** The composition gives, for every symbol of arity `n + 1` meeting the decency
hypotheses, `edit ≤ (n+1)·N^(n+1)·c + (n+1)·D·N^n` with `c = 2θ + γ/2 + λ/2`,
`D = (K−1)·⌊N/t⌋`, `N = |s|`. Since every arity is at most `A = arityBound L`, this is
`edit ≤ ε·N^arity` with the **uniform rate** `ε = A·c + A·D/N` (`globalRate`), the form the
transfers consume (`exists_equitable_model_uniformEdit`). Then, for a simple pattern on `k`
vertices:
* injective homomorphisms move by at most `patternAtomCoefficient L k · ε · N^k`;
* all homomorphisms move by at most that **plus the collision term `C(k,2)·N^(k−1)`**, which the
  released theorem `abs_homCountOn_sub_le_of_simple` carries and which is retained here, not
  discarded (`exists_hom_transfer`).
Nullary compatibility is explicit in the output. The binary instance (`recipe_binary`, the edge
pattern of the regression language: coefficient `4`, collision `1·N`) and the ternary instance
(`recipe_ternary`, the one-symbol language of arity `3` with the pattern of one atom on three
vertices: coefficient `27`, collision `3·N²`) display the full constants.

**Boundary.** The global approximation does **not** supply diagonal agreement: majority rounding
can change loops and repeated-entry tuples. The induced-count corollary
`abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement` is therefore invoked only with an
explicit `DiagonalAgreementOn` premise on the produced model
(`exists_induced_transfer_of_diagonalAgreement`); it is not inferred from simplicity of the
pattern. The three-vertex regression is reused by name (induced `6` vs `0`, injective `6` vs `6`,
all homomorphisms `6` vs `9`, the edge is simple, the hosts lack diagonal agreement). The
**precise negative statement** (`induced_transfer_fails_without_diagonalAgreement`) is a
counterexample, not a failed tactic: on six vertices, the loopless complete relation and the one
with loops added are nullary-compatible, the edge pattern is simple, and the edit bound holds at
`ε = 1/6` (exactly `6` edited tuples out of `36`), yet the induced counts differ by `30`, above
the would-be bound `4 · (1/6) · 36 = 24`. This uses the **actual** edit rate `1/6`; it says
nothing about an induced estimate at the potentially larger `globalRate`. Finally the boundary is
pinned to the rounding operation itself (`majorityRound_top_six_agrees_loops`,
`majorityRound_top_six_not_diagonalAgreement`): majority rounding of the loopless host at the
indiscrete partition **is** the loop-added host, relation by relation, so the rounding fails
diagonal agreement with its input.
-/

namespace RegularityLemmataExamples

open RegularityLemmata FirstOrder FiniteRelModel

section Recipe

variable {L : Language} [FiniteRelational L] {V : Type*} [DecidableEq V] {s : Finset V}

/-- Decency of `M` at `P` for a symbol of arity `n + 1`, with exceptional parts `E`. -/
def Decent (M : FiniteRelModel L V) (P : Finpartition s) {n : ℕ} (S : L.Relations (n + 1))
    (E : Finset (Finset V)) (θ γ : ℝ) : Prop :=
  ∀ (j : Fin (n + 1)), ∀ l ∈ P.parts, l ∉ E →
    (((Fintype.piFinset (fun _ : Fin n ↦ s)).filter fun rest ↦
        InclusiveMixed θ (densityOn l fun a ↦ M.Holds S (Fin.insertNth j a rest))).card : ℝ)
      ≤ γ * (Fintype.piFinset (fun _ : Fin n ↦ s)).card

/-- The uniform edit rate of the global approximation: `A·(2θ + γ/2 + λ/2) + A·D/N` with
`A = arityBound L`, `D = (K − 1)·⌊N/t⌋`. -/
noncomputable def globalRate (L : Language) [FiniteRelational L] (K t N : ℕ) (θ γ lam : ℝ) :
    ℝ :=
  (arityBound L : ℝ) * (2 * θ + γ / 2 + lam / 2)
    + (arityBound L : ℝ) * (((K - 1) * (N / t) : ℕ) : ℝ) / N

theorem globalRate_nonneg (L : Language) [FiniteRelational L] (K t N : ℕ) {θ γ lam : ℝ}
    (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) : 0 ≤ globalRate L K t N θ γ lam := by
  unfold globalRate; positivity

/-- **Step 1.** From the composition, one equipartition `Q` and one model `N`, indivisible for `Q`
and nullary-compatible with `M`, with the **uniform** per-symbol edit bound
`edit(S) ≤ globalRate · N^arity(S)` for every positive-arity symbol. -/
theorem exists_equitable_model_uniformEdit (M : FiniteRelModel L V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hs : 0 < s.card) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (E : Finset (Finset V))
    (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (n : ℕ) (S : L.Relations (n + 1)), Decent M P S E θ γ) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel L V), Q.IsEquipartition ∧ Q.parts.card = t ∧
      N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      ∀ S : RelSymbol L, 0 < (S.1 : ℕ) →
        (editDistance (M.Holds S.2) (N.Holds S.2) (fun _ ↦ s) : ℝ)
          ≤ globalRate L P.parts.card t s.card θ γ lam * (s.card : ℝ) ^ (S.1 : ℕ) := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, hbound⟩ :=
    exists_equitable_isIndivisibleFor M P ht₀ ht hts
  refine ⟨Q, N, hQ, hcard, hind, hnull, ?_⟩
  rintro ⟨⟨m, hm⟩, R⟩ hpos
  simp only at hpos R ⊢
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h := hbound R hθ hγ E hE hlam (hdec n R)
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hA : ((n + 1 : ℕ) : ℝ) ≤ arityBound L := by exact_mod_cast arity_le_arityBound L R
  have hlam0 : 0 ≤ lam := by
    have h0 : (0 : ℝ) ≤ ∑ l ∈ E, (l.card : ℝ) := Finset.sum_nonneg fun _ _ ↦ by positivity
    exact nonneg_of_mul_nonneg_left (h0.trans hlam) hN
  have hc : 0 ≤ 2 * θ + γ / 2 + lam / 2 := by positivity
  set D : ℝ := (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  calc (editDistance (M.Holds R) (N.Holds R) (fun _ ↦ s) : ℝ)
      ≤ (n + 1) * (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2)
          + (n + 1) * D * (s.card : ℝ) ^ n := h
    _ ≤ (arityBound L : ℝ) * (s.card : ℝ) ^ (n + 1) * (2 * θ + γ / 2 + lam / 2)
          + (arityBound L : ℝ) * D * (s.card : ℝ) ^ n := by
        push_cast at hA
        gcongr
    _ = globalRate L P.parts.card t s.card θ γ lam * (s.card : ℝ) ^ (n + 1) := by
        unfold globalRate
        rw [← hD]
        field_simp
        ring

/-- **Step 2, the positive recipe.** For a simple pattern on `k` vertices: injective homomorphisms
move by at most `coefficient · ε · N^k`, all homomorphisms by at most that plus the collision term
`C(k,2)·N^(k−1)`, for the same produced `Q`, `N`, with nullary compatibility explicit. -/
theorem exists_hom_transfer (M : FiniteRelModel L V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hs : 0 < s.card) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hlam0 : 0 ≤ lam)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (n : ℕ) (S : L.Relations (n + 1)), Decent M P S E θ γ)
    {k : ℕ} (Pat : FiniteRelModel L (Fin k)) (hPat : SimplePattern Pat) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel L V), Q.IsEquipartition ∧ Q.parts.card = t ∧
      N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      |(injectiveHomCountOn Pat M s : ℝ) - injectiveHomCountOn Pat N s|
        ≤ patternAtomCoefficient L k * globalRate L P.parts.card t s.card θ γ lam
            * (s.card : ℝ) ^ k ∧
      |(homCountOn Pat M s : ℝ) - homCountOn Pat N s|
        ≤ patternAtomCoefficient L k * globalRate L P.parts.card t s.card θ γ lam
            * (s.card : ℝ) ^ k + (k.choose 2 : ℝ) * s.card ^ (k - 1) := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, hedit⟩ :=
    exists_equitable_model_uniformEdit M P ht₀ ht hts hs hθ hγ E hE hlam hdec
  have hε := globalRate_nonneg L P.parts.card t s.card hθ hγ hlam0
  exact ⟨Q, N, hQ, hcard, hind, hnull,
    abs_injectiveHomCountOn_sub_le_of_simple Pat M N s hε hnull hPat hedit,
    abs_homCountOn_sub_le_of_simple Pat M N s hε hnull hPat hedit⟩

/-- **The induced corollary, only with its explicit premise.** For the produced `N`, *if*
`DiagonalAgreementOn M N s` holds (a premise the approximation does not supply), the induced
count of **any** pattern on `k` vertices (no simplicity is needed here) moves by at most
`coefficient · ε · N^k`. -/
theorem exists_induced_transfer_of_diagonalAgreement (M : FiniteRelModel L V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hs : 0 < s.card) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hlam0 : 0 ≤ lam)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (n : ℕ) (S : L.Relations (n + 1)), Decent M P S E θ γ)
    {k : ℕ} (Pat : FiniteRelModel L (Fin k)) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel L V), Q.IsEquipartition ∧ Q.parts.card = t ∧
      N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      (DiagonalAgreementOn M N s →
        |(inducedEmbeddingCountOn Pat M (fun _ ↦ s) : ℝ)
            - inducedEmbeddingCountOn Pat N (fun _ ↦ s)|
          ≤ patternAtomCoefficient L k * globalRate L P.parts.card t s.card θ γ lam
              * (s.card : ℝ) ^ k) := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, hedit⟩ :=
    exists_equitable_model_uniformEdit M P ht₀ ht hts hs hθ hγ E hE hlam hdec
  exact ⟨Q, N, hQ, hcard, hind, hnull, fun hdiag ↦
    abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement Pat M N s
      (globalRate_nonneg L P.parts.card t s.card hθ hγ hlam0) hnull hdiag hedit⟩

end Recipe

/-! ### The binary instance: the edge pattern of the regression language -/

section Binary

open DiagonalLoopRegression

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-- The regression language has one binary symbol: coefficient `2² = 4`, arity bound `2`. -/
theorem patternAtomCoefficient_language_two : patternAtomCoefficient language 2 = 4 := by decide
theorem arityBound_language : arityBound language = 2 := rfl

/-- **Binary recipe with the constants displayed**: for the edge pattern,
`|Δ injective| ≤ 4·ε·N²` and `|Δ hom| ≤ 4·ε·N² + 1·N` with
`ε = 2·(2θ + γ/2 + λ/2) + 2·((K−1)⌊N/t⌋)/N`. -/
theorem recipe_binary (M : FiniteRelModel language V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hs : 0 < s.card) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hlam0 : 0 ≤ lam)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (n : ℕ) (S : language.Relations (n + 1)), Decent M P S E θ γ) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel language V), Q.IsEquipartition ∧
      Q.parts.card = t ∧ N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      |(injectiveHomCountOn (complete 2 false) M s : ℝ) - injectiveHomCountOn (complete 2 false) N s|
        ≤ 4 * (2 * (2 * θ + γ / 2 + lam / 2)
            + 2 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) / s.card) * (s.card : ℝ) ^ 2 ∧
      |(homCountOn (complete 2 false) M s : ℝ) - homCountOn (complete 2 false) N s|
        ≤ 4 * (2 * (2 * θ + γ / 2 + lam / 2)
            + 2 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) / s.card) * (s.card : ℝ) ^ 2
          + 1 * s.card := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, h₁, h₂⟩ := exists_hom_transfer M P ht₀ ht hts hs hθ hγ
    hlam0 E hE hlam hdec (complete 2 false) edge_isSimplePattern
  rw [patternAtomCoefficient_language_two] at h₁ h₂
  unfold globalRate at h₁ h₂
  rw [arityBound_language] at h₁ h₂
  refine ⟨Q, N, hQ, hcard, hind, hnull, by exact_mod_cast h₁, ?_⟩
  have h₂' := h₂
  norm_num at h₂' ⊢
  exact h₂'

end Binary

/-! ### The ternary instance: one atom on three vertices in the one-symbol language of arity 3 -/

section Ternary

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-- The pattern with the single ternary atom on the vertices `0, 1, 2`. -/
def triple : FiniteRelModel (singleRelLang 3) (Fin 3) where
  rel := fun {r} _ x ↦ match r, x with
    | 3, x => decide (x = ![0, 1, 2])
    | _, _ => false

theorem triple_isSimplePattern : SimplePattern triple := by
  unfold SimplePattern
  decide

/-- One ternary symbol: coefficient `3³ = 27`, arity bound `3`. -/
theorem patternAtomCoefficient_singleRelLang_three :
    patternAtomCoefficient (singleRelLang 3) 3 = 27 := by decide
theorem arityBound_singleRelLang_three : arityBound (singleRelLang 3) = 3 := rfl

/-- **Ternary recipe with the constants displayed**: `|Δ injective| ≤ 27·ε·N³` and
`|Δ hom| ≤ 27·ε·N³ + 3·N²` with `ε = 3·(2θ + γ/2 + λ/2) + 3·((K−1)⌊N/t⌋)/N`. -/
theorem recipe_ternary (M : FiniteRelModel (singleRelLang 3) V) (P : Finpartition s)
    {t₀ : Finset V} (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card)
    (hs : 0 < s.card) {θ γ lam : ℝ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hlam0 : 0 ≤ lam)
    (E : Finset (Finset V)) (hE : E ⊆ P.parts) (hlam : (∑ l ∈ E, (l.card : ℝ)) ≤ lam * s.card)
    (hdec : ∀ (n : ℕ) (S : (singleRelLang 3).Relations (n + 1)), Decent M P S E θ γ) :
    ∃ (Q : Finpartition s) (N : FiniteRelModel (singleRelLang 3) V), Q.IsEquipartition ∧
      Q.parts.card = t ∧ N.IsIndivisibleFor Q ∧ NullaryCompatible M N ∧
      |(injectiveHomCountOn triple M s : ℝ) - injectiveHomCountOn triple N s|
        ≤ 27 * (3 * (2 * θ + γ / 2 + lam / 2)
            + 3 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) / s.card) * (s.card : ℝ) ^ 3 ∧
      |(homCountOn triple M s : ℝ) - homCountOn triple N s|
        ≤ 27 * (3 * (2 * θ + γ / 2 + lam / 2)
            + 3 * (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) / s.card) * (s.card : ℝ) ^ 3
          + 3 * (s.card : ℝ) ^ 2 := by
  obtain ⟨Q, N, hQ, hcard, hind, hnull, h₁, h₂⟩ := exists_hom_transfer M P ht₀ ht hts hs hθ hγ
    hlam0 E hE hlam hdec triple triple_isSimplePattern
  rw [patternAtomCoefficient_singleRelLang_three] at h₁ h₂
  unfold globalRate at h₁ h₂
  rw [arityBound_singleRelLang_three] at h₁ h₂
  refine ⟨Q, N, hQ, hcard, hind, hnull, by exact_mod_cast h₁, ?_⟩
  have h₂' := h₂
  norm_num at h₂' ⊢
  exact h₂'

end Ternary

/-! ### The boundary: reused regression and the precise negative statement -/

section Boundary

open DiagonalLoopRegression

-- The three-vertex regression, reused by name: induced `6` vs `0`, injective `6` vs `6`, all
-- homomorphisms `6` vs `9`, the edge pattern is simple, the hosts lack diagonal agreement.
example : inducedEmbeddingCount (complete 2 false) (complete 3 false) = 6 ∧
    inducedEmbeddingCount (complete 2 false) (complete 3 true) = 0 :=
  induced_count_changes_on_loops
example : injectiveHomCount (complete 2 false) (complete 3 false) = 6 ∧
    injectiveHomCount (complete 2 false) (complete 3 true) = 6 :=
  injective_hom_count_ignores_added_loops
example : homCount (complete 2 false) (complete 3 false) = 6 ∧
    homCount (complete 2 false) (complete 3 true) = 9 :=
  hom_count_collision_difference
example : SimplePattern (complete 2 false) := edge_isSimplePattern
example : ¬ DiagonalAgreementOn (complete 3 false) (complete 3 true) Finset.univ :=
  hosts_not_diagonalAgreement

/-- The regression language has no nullary symbol, so any two models are nullary-compatible. -/
theorem nullaryCompatible_language (M N : FiniteRelModel language V) : NullaryCompatible M N :=
  fun S ↦ (show Empty from S).elim

/-- On six vertices, adding loops edits exactly `6` of the `36` binary tuples, and every symbol
of positive arity satisfies `edit · 6 ≤ 6^arity` (there is only the binary one). -/
theorem edit_six_le : ∀ S : RelSymbol language, 0 < (S.1 : ℕ) →
    editDistance ((complete 6 false).Holds S.2) ((complete 6 true).Holds S.2)
        (fun _ ↦ (Finset.univ : Finset (Fin 6))) * 6
      ≤ 6 ^ (S.1 : ℕ) := by
  decide

/-- Six vertices: induced embeddings of the edge, `30` without loops and `0` with loops. -/
theorem induced_six :
    inducedEmbeddingCountOn (complete 2 false) (complete 6 false) (fun _ ↦ Finset.univ) = 30 ∧
      inducedEmbeddingCountOn (complete 2 false) (complete 6 true) (fun _ ↦ Finset.univ) = 0 := by
  decide

/-- The six-vertex hosts do not meet diagonal agreement (the loops disagree). -/
theorem six_not_diagonalAgreement :
    ¬ DiagonalAgreementOn (complete 6 false) (complete 6 true) Finset.univ := by
  intro h
  have hi : ¬ Function.Injective (fun _ : Fin 2 ↦ (0 : Fin 6)) := by
    intro hinj
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj (a₁ := 0) (a₂ := 1) rfl)
  have hh := h (RelSymbol.mk' (n := 2) (() : language.Relations 2)) (fun _ ↦ 0)
    (fun _ ↦ Finset.mem_univ _) hi
  change (false = true ↔ true = true) at hh
  exact Bool.false_ne_true (hh.mpr rfl)

/-- **The rounding pin.** Majority rounding of the loopless six-vertex host at the indiscrete
partition agrees, relation by relation, with the loop-added host: the single cell `V × V` has
`30` of `36` tuples true, so every tuple, loops included, rounds to true. -/
theorem majorityRound_top_six_agrees_loops :
    ∀ (S : RelSymbol language) (x : Fin (S.1 : ℕ) → Fin 6),
      ((complete 6 false).majorityRound (⊤ : Finpartition (Finset.univ : Finset (Fin 6)))).Holds
          S.2 x
        ↔ (complete 6 true).Holds S.2 x := by
  decide

/-- Hence the rounding operation itself fails diagonal agreement with its input. -/
theorem majorityRound_top_six_not_diagonalAgreement :
    ¬ DiagonalAgreementOn (complete 6 false)
      ((complete 6 false).majorityRound (⊤ : Finpartition (Finset.univ : Finset (Fin 6))))
      Finset.univ := by
  intro h
  apply six_not_diagonalAgreement
  intro S y hy hinj
  exact (h S y hy hinj).trans (majorityRound_top_six_agrees_loops S y)

/-- **The induced transfer fails without diagonal agreement: a counterexample.** Two hosts that
are nullary-compatible, a simple pattern, and an edit bound at rate `ε = 1/6` (the exact edited
fraction), yet the induced counts differ by `30 > 24 = 4 · (1/6) · 6²`. The only hypothesis of
`abs_inducedEmbeddingCountOn_sub_le_of_diagonalAgreement` not satisfied is diagonal agreement,
so that premise cannot be dropped and is not implied by the others. -/
theorem induced_transfer_fails_without_diagonalAgreement :
    ∃ (M N : FiniteRelModel language (Fin 6)) (ε : ℝ), 0 ≤ ε ∧ NullaryCompatible M N ∧
      SimplePattern (complete 2 false) ∧
      (∀ S : RelSymbol language, 0 < (S.1 : ℕ) →
        (editDistance (M.Holds S.2) (N.Holds S.2) (fun _ ↦ (Finset.univ : Finset (Fin 6))) : ℝ)
          ≤ ε * ((Finset.univ : Finset (Fin 6)).card : ℝ) ^ (S.1 : ℕ)) ∧
      ¬ DiagonalAgreementOn M N Finset.univ ∧
      (patternAtomCoefficient language 2 : ℝ) * ε * ((Finset.univ : Finset (Fin 6)).card : ℝ) ^ 2
        < |(inducedEmbeddingCountOn (complete 2 false) M (fun _ ↦ Finset.univ) : ℝ)
            - inducedEmbeddingCountOn (complete 2 false) N (fun _ ↦ Finset.univ)| := by
  refine ⟨complete 6 false, complete 6 true, 1 / 6, by norm_num, nullaryCompatible_language _ _,
    edge_isSimplePattern, ?_, six_not_diagonalAgreement, ?_⟩
  · intro S hS
    have h := edit_six_le S hS
    rw [Finset.card_univ, Fintype.card_fin]
    have h' : (editDistance ((complete 6 false).Holds S.2) ((complete 6 true).Holds S.2)
        (fun _ ↦ (Finset.univ : Finset (Fin 6))) : ℝ) * 6 ≤ (6 : ℝ) ^ (S.1 : ℕ) := by
      exact_mod_cast h
    linarith
  · rw [induced_six.1, induced_six.2, patternAtomCoefficient_language_two, Finset.card_univ,
      Fintype.card_fin]
    norm_num

end Boundary

end RegularityLemmataExamples
