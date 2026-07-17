/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryDiagStrong
import RegularityLemmata.Relational.TransversalCounting
import RegularityLemmata.Finite.WeightedChoice

/-!
# Phase 11 unit 7: role-indexed representative selection

The decisive feasibility unit of the removal route (Phase 11 design freeze in
`ARCHITECTURE.md`): from a strong diagonal-inclusive palette witness, select **three
role-indexed representative fine cells per large coarse cell** —
`rep : Finset V → Fin 3 → Finset V` — simultaneously uniform and density-close for
every ordered coarse-cell pair `(C, D)` **including `C = D`**, every ordered role pair
`(i, j)` with `i ≠ j`, and every palette color.

Proof order (frozen): candidate definition and the half-mass theorem; the abstract
weighted-selection lemma (`Finite/WeightedChoice.lean`) exposing all constants; the
simultaneous construction; the uniformity and density-closeness projections; the size
guarantee `2·q·|rep C i| ≥ |C|`; and only then the strong-witness instantiation.

**Circularity discipline (the unit's stop condition).** The fine-part bound `q` is
confined to the candidate threshold and the size guarantee. The union-bound
arithmetic depends on the coarse complexity, the palette count, and the schedule/gap
parameters only — the half-mass floor contributes the absolute constant `4`, never
`q`. If `q` ever appears in a required regularity/deviation tolerance or in the
union-bound inequality, the route is rejected for review.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### Large coarse cells and small-cell mass -/

open Classical in
/-- The coarse cells of relative size at least `α`. -/
noncomputable def largeParts (Pc : Finpartition s) (α : ℝ) : Finset (Finset V) :=
  Pc.parts.filter fun C => α * s.card ≤ C.card

theorem largeParts_subset {Pc : Finpartition s} {α : ℝ} :
    largeParts Pc α ⊆ Pc.parts :=
  Finset.filter_subset _ _

theorem card_le_of_mem_largeParts {Pc : Finpartition s} {α : ℝ} {C : Finset V}
    (hC : C ∈ largeParts Pc α) : α * s.card ≤ C.card := by
  classical
  exact (Finset.mem_filter.mp hC).2

open Classical in
/-- **Small-cell mass bound**: the coarse cells below the size threshold carry at most
`α·|s|·k` of the ground mass. -/
theorem sum_card_not_largeParts_le {Pc : Finpartition s} {α : ℝ} (hα : 0 ≤ α) :
    ∑ C ∈ Pc.parts.filter (fun C => ¬ α * s.card ≤ (C.card : ℝ)), (C.card : ℝ)
      ≤ α * s.card * Pc.parts.card := by
  classical
  calc ∑ C ∈ Pc.parts.filter (fun C => ¬ α * s.card ≤ (C.card : ℝ)), (C.card : ℝ)
      ≤ ∑ _C ∈ Pc.parts.filter (fun C => ¬ α * s.card ≤ (C.card : ℝ)), α * s.card := by
        refine Finset.sum_le_sum fun C hC => ?_
        exact le_of_lt (not_le.mp (Finset.mem_filter.mp hC).2)
    _ = (Pc.parts.filter (fun C => ¬ α * s.card ≤ (C.card : ℝ))).card * (α * s.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Pc.parts.card * (α * s.card) := by
        have hcard := Finset.card_filter_le Pc.parts
          (fun C => ¬ α * s.card ≤ (C.card : ℝ))
        have hnn : (0 : ℝ) ≤ α * s.card := by positivity
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
    _ = α * s.card * Pc.parts.card := by ring

/-! ### Representative candidates and the half-mass theorem -/

/-- The candidate fine cells inside `C`: fiber cells of relative size at least
`1/(2q)`, in the frozen multiplication form (never natural division). This is the ONLY
place the fine-part bound `q` enters the selection. -/
def repCandidates (Q : Finpartition s) (q : ℕ) (C : Finset V) : Finset (Finset V) :=
  (refinementFiber Q C).filter fun A => C.card ≤ 2 * q * A.card

theorem repCandidates_subset_fiber {Q : Finpartition s} {q : ℕ} {C : Finset V} :
    repCandidates Q q C ⊆ refinementFiber Q C :=
  Finset.filter_subset _ _

theorem mem_repCandidates {Q : Finpartition s} {q : ℕ} {C A : Finset V} :
    A ∈ repCandidates Q q C ↔ (A ∈ Q.parts ∧ A ⊆ C) ∧ C.card ≤ 2 * q * A.card := by
  rw [repCandidates, Finset.mem_filter, refinementFiber, Finset.mem_filter]

/-- **The half-mass theorem.** The large candidates inside a coarse cell carry at
least half of its mass: the discarded fiber cells each contribute less than
`|C|/(2q)` and there are at most `q` of them. -/
theorem half_le_sum_card_repCandidates {Q Pc : Finpartition s} (hQP : Q ≤ Pc)
    {C : Finset V} (hC : C ∈ Pc.parts) {q : ℕ} (hq : Q.parts.card ≤ q) :
    (C.card : ℝ) / 2 ≤ ∑ A ∈ repCandidates Q q C, (A.card : ℝ) := by
  classical
  have htotal : ∑ A ∈ refinementFiber Q C, (A.card : ℝ) = C.card := by
    rw [refinementFiber]
    exact sum_card_filter_subset_eq hQP hC
  have hsplit : ∑ A ∈ repCandidates Q q C, (A.card : ℝ)
      + ∑ A ∈ (refinementFiber Q C).filter (fun A => ¬ C.card ≤ 2 * q * A.card),
          (A.card : ℝ)
      = C.card := by
    rw [repCandidates, Finset.sum_filter_add_sum_filter_not, htotal]
  -- The discarded mass is at most `|C|/2`, via the pure-`ℕ` cancellation
  -- `q·(2·S) ≤ q·|C| → 2·S ≤ |C|` (no division).
  have hsmallN : 2 * (∑ A ∈ (refinementFiber Q C).filter
      (fun A => ¬ C.card ≤ 2 * q * A.card), A.card) ≤ C.card := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · -- `q = 0` forces `Q.parts = ∅`, hence an empty fiber and zero discarded mass.
      have hparts : Q.parts = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hq0 ▸ hq))
      rw [refinementFiber, hparts]
      simp
    · refine Nat.le_of_mul_le_mul_left ?_ hq0
      calc q * (2 * ∑ A ∈ (refinementFiber Q C).filter
            (fun A => ¬ C.card ≤ 2 * q * A.card), A.card)
          = ∑ A ∈ (refinementFiber Q C).filter
              (fun A => ¬ C.card ≤ 2 * q * A.card), 2 * q * A.card := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun A _ => by ring
        _ ≤ ∑ _A ∈ (refinementFiber Q C).filter
              (fun A => ¬ C.card ≤ 2 * q * A.card), C.card := by
            refine Finset.sum_le_sum fun A hA => ?_
            exact le_of_lt (not_le.mp (Finset.mem_filter.mp hA).2)
        _ = ((refinementFiber Q C).filter
              (fun A => ¬ C.card ≤ 2 * q * A.card)).card * C.card := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ q * C.card := by
            refine Nat.mul_le_mul_right _ ?_
            calc ((refinementFiber Q C).filter
                  (fun A => ¬ C.card ≤ 2 * q * A.card)).card
                ≤ (refinementFiber Q C).card := Finset.card_filter_le _ _
              _ ≤ Q.parts.card := Finset.card_filter_le _ _
              _ ≤ q := hq
  have hsmallR : ∑ A ∈ (refinementFiber Q C).filter
      (fun A => ¬ C.card ≤ 2 * q * A.card), (A.card : ℝ) ≤ (C.card : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm]
    have := (Nat.cast_le (α := ℝ)).mpr hsmallN
    push_cast at this
    linarith
  linarith

/-- A coarse cell of positive size has a candidate. -/
theorem repCandidates_nonempty {Q Pc : Finpartition s} (hQP : Q ≤ Pc) {C : Finset V}
    (hC : C ∈ Pc.parts) {q : ℕ} (hq : Q.parts.card ≤ q) (hCpos : 0 < C.card) :
    (repCandidates Q q C).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have := half_le_sum_card_repCandidates hQP hC hq
  rw [hne, Finset.sum_empty] at this
  have : (C.card : ℝ) ≤ 0 := by linarith
  exact absurd (by exact_mod_cast this : C.card ≤ 0) (Nat.not_le.mpr hCpos)

/-! ### The two mass bounds feeding the union bound -/

open Classical in
/-- The non-uniform fiber-pair mass inside any box pair is dominated by the
diagonal-inclusive bad mass of the whole partition. -/
theorem sum_fiber_nonuniform_le_badMassDiagNum (R : V → V → Prop) [DecidableRel R]
    {ε : ℝ} (Q : Finpartition s) (C D : Finset V) :
    ∑ p ∈ (refinementFiber Q C ×ˢ refinementFiber Q D).filter
        (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card)
      ≤ badMassDiagNum R ε Q := by
  rw [badMassDiagNum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
    (fun p _ _ => by positivity)
  rw [Finset.mem_filter, Finset.mem_product, refinementFiber, refinementFiber,
    Finset.mem_filter, Finset.mem_filter] at hp
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩

open FirstOrder in
/-- The `η`-deviant fiber-pair mass of a SINGLE coarse pair is dominated by the
witness's total deviant mass — including diagonal coarse pairs. -/
theorem BinaryPaletteStrongDiagWitness.deviant_pair_mass_le
    {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
    {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) (c : BinaryPairPalette L)
    {η : ℝ} (hη : 0 < η) {pd : Finset V × Finset V}
    (hpd : pd ∈ w.coarse.parts ×ˢ w.coarse.parts) :
    ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
        (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
          - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
      ((p.1.card : ℝ) * p.2.card)
      ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
  classical
  refine le_trans (Finset.single_le_sum (f := fun pd : Finset V × Finset V =>
      ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
            - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
        ((p.1.card : ℝ) * p.2.card))
    (fun pd' _ => Finset.sum_nonneg fun p _ => by positivity) hpd)
    (w.deviant_mass_le c hη)

end RegularityLemmata
