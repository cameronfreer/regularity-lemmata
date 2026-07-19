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

/-! ### The role-indexed representative selection -/

section Selection

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {M : FiniteRelModel L V}
  {E : ErrorSchedule} {δ : ℝ} {P₀ : Finpartition s}

/-- The event index of the selection: ordered pairs of LARGE coarse cells — equal
cells allowed — times ordered role pairs with distinct roles, times palette colors. -/
private abbrev SelEvent (w : BinaryPaletteStrongDiagWitness M E δ P₀) (α : ℝ) :
    Type _ :=
  ({C // C ∈ largeParts w.coarse α} × {C // C ∈ largeParts w.coarse α})
    × ({ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2} × BinaryPairPalette L)

open Classical in
/-- **The exact role/palette factor of the aggregate deviant mass** (11A checkpoint,
round 2): summing each event's deviant fiber-pair mass over the FULL event index —
six ordered role pairs times the `K = Fintype.card (BinaryPairPalette L)` palette
colors times all ordered large coarse pairs — costs exactly `6·K` times the per-color
witness deviance bound `(δ/η²)·n²`.

Factor accounting for the candidate re-scope, on record: charging each deviant event
the coarse-pair volume `|C|·|D|` and dividing by the two pinned candidate weights
(each at least `|C|/2` by the half-mass theorem) multiplies this bound by at most `4`,
giving the unconditional expected-cost input `μ ≤ 24·K·(δ/η²)·n²` of
`sum_piFinset_weight_mul_eventCost_le`; conditioning on all uniformity events under
the half-budget schedule (`σ ≤ 1/2`) doubles it, so the honest selected-cost constant
is `48·K·(δ/η²)·n²` (`exists_piFinset_forall_not_mem_bad_cost_le`). The
selection-with-cost wiring is deliberately NOT installed pending the round-2 route
decision on the re-scope. -/
theorem BinaryPaletteStrongDiagWitness.sum_selEvent_deviantMass_le
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) (α : ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ e : SelEvent w α,
        ∑ p ∈ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
            (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
          (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
            - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|),
          ((p.1.card : ℝ) * p.2.card)
      ≤ 6 * (Fintype.card (BinaryPairPalette L) : ℝ)
          * (δ / η ^ 2 * (s.card : ℝ) ^ 2) := by
  classical
  set f : Finset V × Finset V → BinaryPairPalette L → ℝ := fun pd c =>
    ∑ p ∈ ((w.fine.parts.filter (· ⊆ pd.1)) ×ˢ (w.fine.parts.filter (· ⊆ pd.2))).filter
        (fun p => η < |pairDensity (HasBinaryPairPalette M c) p.1 p.2
          - pairDensity (HasBinaryPairPalette M c) pd.1 pd.2|),
      ((p.1.card : ℝ) * p.2.card) with hf
  have hfnn : ∀ pd c, 0 ≤ f pd c := fun pd c =>
    Finset.sum_nonneg fun p _ => by positivity
  have hcardR : Fintype.card {ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2} = 6 := by decide
  -- Per color, the sum over ordered large coarse pairs is dominated by the witness's
  -- per-color deviance bound (the sum over ALL ordered coarse pairs).
  have hfbound : ∀ c : BinaryPairPalette L,
      ∑ CD : {C // C ∈ largeParts w.coarse α} × {C // C ∈ largeParts w.coarse α},
        f (CD.1.1, CD.2.1) c ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
    intro c
    have heq : ∑ CD : {C // C ∈ largeParts w.coarse α}
          × {C // C ∈ largeParts w.coarse α}, f (CD.1.1, CD.2.1) c
        = ∑ pd ∈ largeParts w.coarse α ×ˢ largeParts w.coarse α, f pd c := by
      rw [Fintype.sum_prod_type, Finset.sum_product, Finset.univ_eq_attach,
        ← Finset.sum_attach (largeParts w.coarse α)
          (fun C => ∑ D ∈ largeParts w.coarse α, f (C, D) c)]
      refine Finset.sum_congr rfl fun C _ => ?_
      show ∑ D ∈ (largeParts w.coarse α).attach, f (C.1, D.1) c
          = ∑ D ∈ largeParts w.coarse α, f (C.1, D) c
      exact Finset.sum_attach (largeParts w.coarse α) (fun D => f (C.1, D) c)
    rw [heq]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.product_subset_product largeParts_subset largeParts_subset)
        fun pd _ _ => hfnn pd c)
      (w.deviant_mass_le c hη)
  show ∑ e : SelEvent w α, f (e.1.1.1, e.1.2.1) e.2.2
      ≤ 6 * (Fintype.card (BinaryPairPalette L) : ℝ)
          * (δ / η ^ 2 * (s.card : ℝ) ^ 2)
  calc ∑ e : SelEvent w α, f (e.1.1.1, e.1.2.1) e.2.2
      = ∑ CD : {C // C ∈ largeParts w.coarse α} × {C // C ∈ largeParts w.coarse α},
          ∑ rc : {ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2} × BinaryPairPalette L,
            f (CD.1.1, CD.2.1) rc.2 :=
        Fintype.sum_prod_type _
    _ = ∑ CD : {C // C ∈ largeParts w.coarse α} × {C // C ∈ largeParts w.coarse α},
          (6 : ℝ) * ∑ c : BinaryPairPalette L, f (CD.1.1, CD.2.1) c := by
        refine Finset.sum_congr rfl fun CD _ => ?_
        rw [Fintype.sum_prod_type]
        show ∑ _r : {ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2}, ∑ c : BinaryPairPalette L,
            f (CD.1.1, CD.2.1) c
          = (6 : ℝ) * ∑ c : BinaryPairPalette L, f (CD.1.1, CD.2.1) c
        rw [Finset.sum_const, Finset.card_univ, hcardR, nsmul_eq_mul]
        norm_num
    _ = (6 : ℝ) * ∑ c : BinaryPairPalette L,
          ∑ CD : {C // C ∈ largeParts w.coarse α} × {C // C ∈ largeParts w.coarse α},
            f (CD.1.1, CD.2.1) c := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (6 : ℝ) * ∑ _c : BinaryPairPalette L, (δ / η ^ 2 * (s.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hfbound c)
          (by norm_num)
    _ = 6 * (Fintype.card (BinaryPairPalette L) : ℝ)
          * (δ / η ^ 2 * (s.card : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]

open Classical in
/-- **Role-indexed representative selection.** Under the host-free arithmetic
hypothesis — coarse complexity, palette count, schedule, and gap parameters ONLY; the
fine-part bound `q` appears in the size guarantee and NOWHERE in the tolerance — there
exist three role-indexed representative fine cells per large coarse cell,
simultaneously uniform and density-close for every ordered coarse pair (equal cells
included), every ordered role pair with distinct roles, and every palette color. -/
theorem BinaryPaletteStrongDiagWitness.exists_representatives
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) {q : ℕ}
    (hq : w.fine.parts.card ≤ q) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (harith : 24 * (w.coarse.parts.card : ℝ) ^ 2
        * (Fintype.card (BinaryPairPalette L) : ℝ)
        * (E w.coarse.parts.card + δ / η ^ 2) < α ^ 2) :
    ∃ rep : Finset V → Fin 3 → Finset V,
      (∀ C ∈ largeParts w.coarse α, ∀ i : Fin 3,
        rep C i ∈ w.fine.parts ∧ rep C i ⊆ C ∧ C.card ≤ 2 * q * (rep C i).card) ∧
      ∀ C ∈ largeParts w.coarse α, ∀ D ∈ largeParts w.coarse α,
        ∀ i j : Fin 3, i ≠ j → ∀ c : BinaryPairPalette L,
          IsUniformPair (HasBinaryPairPalette M c) (rep C i) (rep D j)
            (E w.coarse.parts.card) ∧
          |pairDensity (HasBinaryPairPalette M c) (rep C i) (rep D j)
            - pairDensity (HasBinaryPairPalette M c) C D| ≤ η := by
  classical
  -- Abbreviations for the instantiation of the abstract weighted-selection lemma.
  set t : {C // C ∈ largeParts w.coarse α} × Fin 3 → Finset (Finset V) :=
    fun Ci => repCandidates w.fine q Ci.1.1 with ht
  set i₁ : SelEvent w α → {C // C ∈ largeParts w.coarse α} × Fin 3 :=
    fun e => (e.1.1, e.2.1.1.1) with hi₁
  set i₂ : SelEvent w α → {C // C ∈ largeParts w.coarse α} × Fin 3 :=
    fun e => (e.1.2, e.2.1.1.2) with hi₂
  set Bad : SelEvent w α → Finset (Finset V × Finset V) := fun e =>
    ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
      (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
          (E w.coarse.parts.card)
        ∨ η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
            - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|) with hBad
  -- Facts about large cells and their candidate weights.
  have hcoarse : ∀ Ci : {C // C ∈ largeParts w.coarse α} × Fin 3,
      Ci.1.1 ∈ w.coarse.parts := fun Ci => largeParts_subset Ci.1.2
  have hWhalf : ∀ Ci : {C // C ∈ largeParts w.coarse α} × Fin 3,
      (Ci.1.1.card : ℝ) / 2 ≤ ∑ A ∈ t Ci, (A.card : ℝ) := fun Ci =>
    half_le_sum_card_repCandidates w.fine_le (hcoarse Ci) hq
  have hCpos : ∀ Ci : {C // C ∈ largeParts w.coarse α} × Fin 3,
      0 < Ci.1.1.card := fun Ci =>
    Finset.card_pos.mpr (w.coarse.nonempty_of_mem_parts (hcoarse Ci))
  have hWpos : ∀ Ci : {C // C ∈ largeParts w.coarse α} × Fin 3,
      0 < ∑ A ∈ t Ci, (A.card : ℝ) := fun Ci => by
    have h1 := hWhalf Ci
    have h2 : (0 : ℝ) < Ci.1.1.card := by exact_mod_cast hCpos Ci
    linarith
  have hWfloor : ∀ Ci : {C // C ∈ largeParts w.coarse α} × Fin 3,
      α * s.card / 2 ≤ ∑ A ∈ t Ci, (A.card : ℝ) := fun Ci => by
    have h1 := hWhalf Ci
    have h2 := card_le_of_mem_largeParts Ci.1.2
    linarith
  -- The analytic union-bound inequality.
  have hlt : ∑ e : SelEvent w α,
      (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card))
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ)
      < ∏ j, ∑ A ∈ t j, (A.card : ℝ) := by
    have hprodpos : (0 : ℝ) < ∏ j, ∑ A ∈ t j, (A.card : ℝ) :=
      Finset.prod_pos fun j _ => hWpos j
    rcases (largeParts w.coarse α).eq_empty_or_nonempty with hlarge | hlarge
    · -- No large cells: the event type is empty and the total weight is positive.
      have hEempty : IsEmpty (SelEvent w α) :=
        ⟨fun e => Finset.eq_empty_iff_forall_notMem.mp hlarge e.1.1.1 e.1.1.2⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact hprodpos
    · -- Some large cell exists: the host is nonempty and every bound is live.
      have hn : (0 : ℝ) < s.card := by
        obtain ⟨C, hC⟩ := hlarge
        have hCc : C ∈ w.coarse.parts := largeParts_subset hC
        have h1 : 0 < C.card :=
          Finset.card_pos.mpr (w.coarse.nonempty_of_mem_parts hCc)
        have h2 : C.card ≤ s.card :=
          Finset.card_le_card (w.coarse.le hCc)
        exact_mod_cast lt_of_lt_of_le h1 h2
      have hM0 : (0 : ℝ) ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 := by
        obtain ⟨C, hC⟩ := hlarge
        have hCc : C ∈ w.coarse.parts := largeParts_subset hC
        refine le_trans (Finset.sum_nonneg fun p _ => by positivity)
          (w.deviant_pair_mass_le (Classical.arbitrary (BinaryPairPalette L)) hη
            (pd := (C, C)) (Finset.mem_product.mpr ⟨hCc, hCc⟩))
      -- Per-event mass bound.
      have hmass : ∀ e : SelEvent w α,
          ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card)
            ≤ (E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2 := by
        intro e
        have hsub1 : Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)) ⊆ Bad e :=
          Finset.inter_subset_left
        have hstep1 : ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)),
            ((p.1.card : ℝ) * p.2.card) ≤ ∑ p ∈ Bad e, ((p.1.card : ℝ) * p.2.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun p _ _ => by positivity
        have hsplit : Bad e
            ⊆ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
                  (E w.coarse.parts.card))
              ∪ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
                  - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|) := by
          intro p hp
          rw [hBad, Finset.mem_filter] at hp
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          rcases hp.2 with h | h
          · exact Or.inl ⟨hp.1, h⟩
          · exact Or.inr ⟨hp.1, h⟩
        have hstep2 : ∑ p ∈ Bad e, ((p.1.card : ℝ) * p.2.card)
            ≤ ∑ p ∈ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                  (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                  (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
                    (E w.coarse.parts.card)), ((p.1.card : ℝ) * p.2.card)
              + ∑ p ∈ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                  (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                  (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
                    - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|),
                  ((p.1.card : ℝ) * p.2.card) := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsplit
            fun p _ _ => by positivity) ?_
          have hinter := Finset.sum_union_inter
            (s₁ := ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
                  (E w.coarse.parts.card)))
            (s₂ := ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
                  - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|))
            (f := fun p => ((p.1.card : ℝ) * p.2.card))
          have hinn : (0 : ℝ) ≤ ∑ p ∈ (((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
                  (E w.coarse.parts.card))
              ∩ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
                (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
                (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
                  - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|)),
              ((p.1.card : ℝ) * p.2.card) :=
            Finset.sum_nonneg fun p _ => by positivity
          linarith [hinter]
        have hnonunif : ∑ p ∈ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
              (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
              (fun p => ¬ IsUniformPair (HasBinaryPairPalette M e.2.2) p.1 p.2
                (E w.coarse.parts.card)), ((p.1.card : ℝ) * p.2.card)
            ≤ E w.coarse.parts.card * (s.card : ℝ) ^ 2 :=
          le_trans
            (sum_fiber_nonuniform_le_badMassDiagNum
              (HasBinaryPairPalette M e.2.2) w.fine e.1.1.1 e.1.2.1)
            (badMassDiagNum_le_of_isRegularPartitionDiag _ _
              (w.fine_diagRegular e.2.2))
        have hdev : ∑ p ∈ ((w.fine.parts.filter (· ⊆ e.1.1.1)) ×ˢ
              (w.fine.parts.filter (· ⊆ e.1.2.1))).filter
              (fun p => η < |pairDensity (HasBinaryPairPalette M e.2.2) p.1 p.2
                - pairDensity (HasBinaryPairPalette M e.2.2) e.1.1.1 e.1.2.1|),
              ((p.1.card : ℝ) * p.2.card)
            ≤ δ / η ^ 2 * (s.card : ℝ) ^ 2 :=
          w.deviant_pair_mass_le e.2.2 hη (pd := (e.1.1.1, e.1.2.1))
            (Finset.mem_product.mpr ⟨hcoarse (i₁ e), hcoarse (i₂ e)⟩)
        calc ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card)
            ≤ ∑ p ∈ Bad e, ((p.1.card : ℝ) * p.2.card) := hstep1
          _ ≤ _ + _ := hstep2
          _ ≤ E w.coarse.parts.card * (s.card : ℝ) ^ 2
              + δ / η ^ 2 * (s.card : ℝ) ^ 2 := add_le_add hnonunif hdev
          _ = (E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2 := by ring
      -- The remaining-coordinates weight versus the total weight.
      have hrest : ∀ e : SelEvent w α,
          ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ)
            ≤ (∏ j, ∑ A ∈ t j, (A.card : ℝ)) * (4 / (α ^ 2 * (s.card : ℝ) ^ 2)) := by
        intro e
        have hne12 : i₁ e ≠ i₂ e := fun h => e.2.1.2 (congrArg Prod.snd h)
        have hfact : ∏ j, ∑ A ∈ t j, (A.card : ℝ)
            = (∑ A ∈ t (i₁ e), (A.card : ℝ)) * ((∑ A ∈ t (i₂ e), (A.card : ℝ))
              * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
                  ∑ A ∈ t j, (A.card : ℝ)) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (i₁ e)),
            ← Finset.mul_prod_erase (Finset.univ.erase (i₁ e)) _
              (Finset.mem_erase.mpr ⟨hne12.symm, Finset.mem_univ _⟩)]
        have hWW : α * s.card / 2 * (α * s.card / 2)
            ≤ (∑ A ∈ t (i₁ e), (A.card : ℝ)) * ∑ A ∈ t (i₂ e), (A.card : ℝ) := by
          have h1 := hWfloor (i₁ e)
          have h2 := hWfloor (i₂ e)
          have hnn : (0 : ℝ) ≤ α * s.card / 2 := by positivity
          exact mul_le_mul h1 h2 hnn (le_of_lt (hWpos (i₁ e)))
        have hrestnn : (0 : ℝ) ≤ ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
            ∑ A ∈ t j, (A.card : ℝ) :=
          Finset.prod_nonneg fun j _ => le_of_lt (hWpos j)
        have hden : (0 : ℝ) < α * s.card / 2 * (α * s.card / 2) := by positivity
        have hup : (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
              ∑ A ∈ t j, (A.card : ℝ)) * (α * s.card / 2 * (α * s.card / 2))
            ≤ ∏ j, ∑ A ∈ t j, (A.card : ℝ) := by
          calc (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
                ∑ A ∈ t j, (A.card : ℝ)) * (α * s.card / 2 * (α * s.card / 2))
              ≤ (∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
                  ∑ A ∈ t j, (A.card : ℝ))
                * ((∑ A ∈ t (i₁ e), (A.card : ℝ))
                  * ∑ A ∈ t (i₂ e), (A.card : ℝ)) :=
                mul_le_mul_of_nonneg_left hWW hrestnn
            _ = (∑ A ∈ t (i₁ e), (A.card : ℝ)) * ((∑ A ∈ t (i₂ e), (A.card : ℝ))
                * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
                    ∑ A ∈ t j, (A.card : ℝ)) := by ring
            _ = ∏ j, ∑ A ∈ t j, (A.card : ℝ) := hfact.symm
        have hdiv : ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
              ∑ A ∈ t j, (A.card : ℝ)
            ≤ (∏ j, ∑ A ∈ t j, (A.card : ℝ))
              / (α * s.card / 2 * (α * s.card / 2)) :=
          (le_div_iff₀ hden).mpr hup
        have h4 : ∀ P : ℝ, P / (α * s.card / 2 * (α * s.card / 2))
            = P * (4 / (α ^ 2 * (s.card : ℝ) ^ 2)) := by
          intro P
          field_simp [hα.ne', hn.ne']
          ring
        rw [h4] at hdiv
        exact hdiv
      -- Count the events and assemble.
      have hEcard : (Fintype.card (SelEvent w α) : ℝ)
          ≤ (w.coarse.parts.card : ℝ) ^ 2 * 6
            * (Fintype.card (BinaryPairPalette L) : ℝ) := by
        have hsub6 : Fintype.card {ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2} = 6 := by decide
        have h1 : Fintype.card (SelEvent w α)
            = (largeParts w.coarse α).card * (largeParts w.coarse α).card
              * (6 * Fintype.card (BinaryPairPalette L)) := by
          rw [show Fintype.card (SelEvent w α)
              = Fintype.card ({C // C ∈ largeParts w.coarse α}
                  × {C // C ∈ largeParts w.coarse α})
                * Fintype.card ({ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2}
                  × BinaryPairPalette L) from Fintype.card_prod _ _,
            Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, hsub6]
        have h2R : ((largeParts w.coarse α).card : ℝ)
            ≤ (w.coarse.parts.card : ℝ) := by
          exact_mod_cast Finset.card_le_card
            (largeParts_subset (Pc := w.coarse) (α := α))
        have hnn : (0 : ℝ) ≤ ((largeParts w.coarse α).card : ℝ) := Nat.cast_nonneg _
        have hll : ((largeParts w.coarse α).card : ℝ)
              * ((largeParts w.coarse α).card : ℝ)
            ≤ (w.coarse.parts.card : ℝ) * (w.coarse.parts.card : ℝ) :=
          mul_le_mul h2R h2R hnn (Nat.cast_nonneg _)
        rw [h1]
        push_cast
        calc ((largeParts w.coarse α).card : ℝ)
              * ((largeParts w.coarse α).card : ℝ)
              * (6 * (Fintype.card (BinaryPairPalette L) : ℝ))
            ≤ (w.coarse.parts.card : ℝ) * (w.coarse.parts.card : ℝ)
              * (6 * (Fintype.card (BinaryPairPalette L) : ℝ)) := by
              refine mul_le_mul_of_nonneg_right hll (by positivity)
          _ = (w.coarse.parts.card : ℝ) ^ 2 * 6
              * (Fintype.card (BinaryPairPalette L) : ℝ) := by ring
      -- Assemble the union bound.
      have hδη : (0 : ℝ) ≤ δ / η ^ 2 := by
        have hn2 : (0 : ℝ) < (s.card : ℝ) ^ 2 := by positivity
        nlinarith [hM0]
      have hMpos : (0 : ℝ) < E w.coarse.parts.card + δ / η ^ 2 := by
        have h1 := E.pos w.coarse.parts.card
        linarith
      have hconstnn : (0 : ℝ) ≤ (E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2
          * ((∏ j, ∑ A ∈ t j, (A.card : ℝ)) * (4 / (α ^ 2 * (s.card : ℝ) ^ 2))) :=
        mul_nonneg (mul_nonneg (le_of_lt hMpos) (sq_nonneg _))
          (mul_nonneg (le_of_lt hprodpos) (by positivity))
      have hperevent : ∀ e : SelEvent w α,
          (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card))
            * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ)
          ≤ (E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2
            * ((∏ j, ∑ A ∈ t j, (A.card : ℝ))
              * (4 / (α ^ 2 * (s.card : ℝ) ^ 2))) := by
        intro e
        refine mul_le_mul (hmass e) (hrest e)
          (Finset.prod_nonneg fun j _ => le_of_lt (hWpos j))
          (mul_nonneg (le_of_lt hMpos) (sq_nonneg _))
      calc ∑ e : SelEvent w α,
            (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card))
              * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e),
                  ∑ A ∈ t j, (A.card : ℝ)
          ≤ ∑ _e : SelEvent w α,
              (E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2
                * ((∏ j, ∑ A ∈ t j, (A.card : ℝ))
                  * (4 / (α ^ 2 * (s.card : ℝ) ^ 2))) :=
            Finset.sum_le_sum fun e _ => hperevent e
        _ = (Fintype.card (SelEvent w α) : ℝ)
            * ((E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2
              * ((∏ j, ∑ A ∈ t j, (A.card : ℝ))
                * (4 / (α ^ 2 * (s.card : ℝ) ^ 2)))) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ ≤ (w.coarse.parts.card : ℝ) ^ 2 * 6
              * (Fintype.card (BinaryPairPalette L) : ℝ)
            * ((E w.coarse.parts.card + δ / η ^ 2) * (s.card : ℝ) ^ 2
              * ((∏ j, ∑ A ∈ t j, (A.card : ℝ))
                * (4 / (α ^ 2 * (s.card : ℝ) ^ 2)))) :=
            mul_le_mul_of_nonneg_right hEcard hconstnn
        _ = (∏ j, ∑ A ∈ t j, (A.card : ℝ))
            * (24 * (w.coarse.parts.card : ℝ) ^ 2
              * (Fintype.card (BinaryPairPalette L) : ℝ)
              * (E w.coarse.parts.card + δ / η ^ 2) / α ^ 2) := by
            have hgen : ∀ P k2 K M : ℝ,
                k2 * 6 * K * (M * (s.card : ℝ) ^ 2
                    * (P * (4 / (α ^ 2 * (s.card : ℝ) ^ 2))))
                  = P * (24 * k2 * K * M / α ^ 2) := by
              intro P k2 K M
              field_simp [hα.ne', hn.ne']
              ring
            exact hgen _ _ _ _
        _ < ∏ j, ∑ A ∈ t j, (A.card : ℝ) := by
            refine mul_lt_of_lt_one_right hprodpos ?_
            rw [div_lt_one (by positivity)]
            exact harith
  -- Apply the abstract weighted-selection lemma and extract the representatives.
  have hlt' : ∑ e : SelEvent w α, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)),
      (p.1.card : ℝ) * p.2.card
        * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ)
      < ∏ j, ∑ A ∈ t j, (A.card : ℝ) := by
    calc ∑ e : SelEvent w α, ∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)),
        (p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ)
        = ∑ e : SelEvent w α,
          (∑ p ∈ Bad e ∩ (t (i₁ e) ×ˢ t (i₂ e)), ((p.1.card : ℝ) * p.2.card))
            * ∏ j ∈ (Finset.univ.erase (i₁ e)).erase (i₂ e), ∑ A ∈ t j, (A.card : ℝ) :=
          Finset.sum_congr rfl fun e _ => (Finset.sum_mul _ _ _).symm
      _ < ∏ j, ∑ A ∈ t j, (A.card : ℝ) := hlt
  obtain ⟨g, hg, hgood⟩ := exists_piFinset_forall_not_mem_bad t
    (fun A : Finset V => (A.card : ℝ)) (fun A => Nat.cast_nonneg _)
    i₁ i₂ (fun e h => e.2.1.2 (congrArg Prod.snd h)) Bad hlt'
  refine ⟨fun C i => if h : C ∈ largeParts w.coarse α then g (⟨C, h⟩, i) else ∅,
    ?_, ?_⟩
  · -- Membership, containment, and the size guarantee (the only consumers of `q`).
    intro C hC i
    beta_reduce
    rw [dif_pos hC]
    have hmem : g (⟨C, hC⟩, i) ∈ t (⟨C, hC⟩, i) := Fintype.mem_piFinset.mp hg _
    simp only [ht] at hmem
    have h3 := mem_repCandidates.mp hmem
    exact ⟨h3.1.1, h3.1.2, h3.2⟩
  · -- Uniformity and density-closeness, from the avoided bad events.
    intro C hC D hD i j hij c
    beta_reduce
    rw [dif_pos hC, dif_pos hD]
    have hgoodE := hgood ((⟨C, hC⟩, ⟨D, hD⟩), (⟨(i, j), hij⟩, c))
    simp only [hi₁, hi₂, hBad] at hgoodE
    have hmemC : g (⟨C, hC⟩, i) ∈ t (⟨C, hC⟩, i) := Fintype.mem_piFinset.mp hg _
    have hmemD : g (⟨D, hD⟩, j) ∈ t (⟨D, hD⟩, j) := Fintype.mem_piFinset.mp hg _
    simp only [ht] at hmemC hmemD
    have hC3 := mem_repCandidates.mp hmemC
    have hD3 := mem_repCandidates.mp hmemD
    have hpair : (g (⟨C, hC⟩, i), g (⟨D, hD⟩, j))
        ∈ (w.fine.parts.filter (· ⊆ C)) ×ˢ (w.fine.parts.filter (· ⊆ D)) :=
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hC3.1.1, hC3.1.2⟩,
        Finset.mem_filter.mpr ⟨hD3.1.1, hD3.1.2⟩⟩
    have hnot : ¬ (¬ IsUniformPair (HasBinaryPairPalette M c) (g (⟨C, hC⟩, i))
          (g (⟨D, hD⟩, j)) (E w.coarse.parts.card)
        ∨ η < |pairDensity (HasBinaryPairPalette M c) (g (⟨C, hC⟩, i)) (g (⟨D, hD⟩, j))
            - pairDensity (HasBinaryPairPalette M c) C D|) :=
      fun hbad => hgoodE (Finset.mem_filter.mpr ⟨hpair, hbad⟩)
    obtain ⟨h1, h2⟩ := not_or.mp hnot
    exact ⟨not_not.mp h1, le_of_not_gt h2⟩

end Selection

/-! ### Tests and adversarial examples -/

section Tests

open FirstOrder

-- Statement-level: the selection exists at concrete types.
example (M : FiniteRelModel (singleRelLang 2) (Fin 5)) (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition (Finset.univ : Finset (Fin 5)))
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) {q : ℕ}
    (hq : w.fine.parts.card ≤ q) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (harith : 24 * (w.coarse.parts.card : ℝ) ^ 2
        * (Fintype.card (BinaryPairPalette (singleRelLang 2)) : ℝ)
        * (E w.coarse.parts.card + δ / η ^ 2) < α ^ 2) :
    ∃ rep : Finset (Fin 5) → Fin 3 → Finset (Fin 5),
      (∀ C ∈ largeParts w.coarse α, ∀ i : Fin 3,
        rep C i ∈ w.fine.parts ∧ rep C i ⊆ C ∧ C.card ≤ 2 * q * (rep C i).card) ∧
      ∀ C ∈ largeParts w.coarse α, ∀ D ∈ largeParts w.coarse α,
        ∀ i j : Fin 3, i ≠ j → ∀ c,
          IsUniformPair (HasBinaryPairPalette M c) (rep C i) (rep D j)
            (E w.coarse.parts.card) ∧
          |pairDensity (HasBinaryPairPalette M c) (rep C i) (rep D j)
            - pairDensity (HasBinaryPairPalette M c) C D| ≤ η :=
  w.exists_representatives hq hα hη harith

-- **The circularity stop condition, checked**: the arithmetic hypothesis does not
-- mention `q`, so the SAME hypothesis serves EVERY fine-part bound — here the same
-- `harith` is consumed at `q` and at `q + 1`. Dependence of the selection tolerance
-- on the fine-part bound would make this example impossible.
example (M : FiniteRelModel (singleRelLang 2) (Fin 5)) (E : ErrorSchedule) {δ : ℝ}
    (P₀ : Finpartition (Finset.univ : Finset (Fin 5)))
    (w : BinaryPaletteStrongDiagWitness M E δ P₀) {q : ℕ}
    (hq : w.fine.parts.card ≤ q) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (harith : 24 * (w.coarse.parts.card : ℝ) ^ 2
        * (Fintype.card (BinaryPairPalette (singleRelLang 2)) : ℝ)
        * (E w.coarse.parts.card + δ / η ^ 2) < α ^ 2) :
    (∃ rep : Finset (Fin 5) → Fin 3 → Finset (Fin 5), ∀ C ∈ largeParts w.coarse α,
        ∀ i : Fin 3, C.card ≤ 2 * q * (rep C i).card) ∧
    ∃ rep : Finset (Fin 5) → Fin 3 → Finset (Fin 5), ∀ C ∈ largeParts w.coarse α,
        ∀ i : Fin 3, C.card ≤ 2 * (q + 1) * (rep C i).card :=
  ⟨(w.exists_representatives hq hα hη harith).elim fun rep h =>
      ⟨rep, fun C hC i => (h.1 C hC i).2.2⟩,
    (w.exists_representatives (hq.trans (Nat.le_succ q)) hα hη harith).elim
      fun rep h => ⟨rep, fun C hC i => (h.1 C hC i).2.2⟩⟩

-- The half-mass theorem, concretely: on the discrete refinement of a two-cell
-- ground set every fiber cell is a candidate at `q = 2`, and the candidate mass is
-- the whole cell.
example : ∑ A ∈ repCandidates (⊥ : Finpartition ({0, 1} : Finset (Fin 2))) 2 {0, 1},
    A.card = 2 := by decide

-- Adversarial: at `q = 0` there are no candidates at all (the threshold is
-- unsatisfiable for a nonempty cell) — the half-mass theorem's `q ≥ #fine parts`
-- hypothesis is genuinely needed.
example : repCandidates (⊥ : Finpartition ({0, 1} : Finset (Fin 2))) 0 {0, 1} = ∅ := by
  decide

end Tests
