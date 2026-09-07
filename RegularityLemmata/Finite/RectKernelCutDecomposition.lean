/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RelationKernel
import RegularityLemmata.Finite.RectKernelCutNorm
import Mathlib.Data.Fin.VecNotation

/-!
# The cut-matrix decomposition

Frieze–Kannan's second statement, in the library's raw-weight units: an absolutely unit-bounded
kernel on `A ×ˢ B` is a sum of at most `⌈1/ε²⌉₊` weighted rectangle indicators, with coefficients
of absolute value at most `1/ε`, plus a residual of cut norm at most `ε` times the total mass.
One statement, `kernel_frieze_kannan_cutDecomposition`, carries all four guarantees.

**Why it is a separate summit.** The step-partition theorem
(`Partition/RectKernelFriezeKannan.lean`) predicts by a stepped kernel, whose stepped prediction
is a rectangle combination with the *product* term count `#P · #Q`. The decomposition is produced
by a **greedy residual iteration** that records one rectangle per round and forms no partition,
so its term count is `O(ε⁻²)`; its residual is measured by the partition-free cut norm
(`Finite/RectKernelCutNorm.lean`), and the two summits meet on the residual through
`rectCutDiscrepancy_eq_rectCutNorm_rectResidual`. Design freeze:
`docs/design/cut-matrix-decomposition.md`.

**The iteration.** The potential is the pointwise mass-weighted square `rectSqMass` of the
residual. The invariant after `t` rounds (`CutIterInv`) records `t` rectangles inside the
carriers with coefficients bounded by `1/ε` whose residual `Rₜ` satisfies
`Φ(Rₜ) + t·ε²·M ≤ Φ(f)`, **strictly** once `t ≥ 1`. A failing round — a witness rectangle with
`ε·M < |rectSum Rₜ S T|` — subtracts the rectangle at the residual's own average: the decrement
identity (`rectSqMass_sub_rectAverage_smul_rectIndicator`) drops the potential by the block
energy, which exceeds `ε²·M` *strictly* by the strict witness inequality, and the new coefficient
is bounded by `abs_rectAverage_le_inv_of_lt_abs_rectSum`, using only `Φ(Rₜ) ≤ M` (never any
boundedness of the residual, which is not unit-bounded after the first round). With `M > 0`,
`N = ⌈1/ε²⌉₊` consecutive failures would give `Φ(R_N) < 0`, so some round `t ≤ N` stops; with
`M = 0` the empty decomposition already works. This is what supplies the budget with no `+ 1`.

Nonnegative carrier weights and `0 < ε` are the only hypotheses beyond `|f| ≤ 1` on `A ×ˢ B`:
no nonemptiness, no positive mass, no `ε ≤ 1` (at `ε ≥ 1` the empty decomposition suffices, by
the trivial bound `rectCutNorm_le_mul_mass`).
-/

namespace RegularityLemmata

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] {A : Finset X} {B : Finset Y}

/-! ### Appending a rectangle to a combination -/

/-- Appending one weighted rectangle to a combination adds its term pointwise. -/
theorem rectCombination_snoc {n : ℕ} (c : Fin n → ℝ) (S : Fin n → Finset X)
    (T : Fin n → Finset Y) (a : ℝ) (S₀ : Finset X) (T₀ : Finset Y) :
    rectCombination (Fin.snoc c a) (Fin.snoc S S₀) (Fin.snoc T T₀)
      = fun x y => rectCombination c S T x y + a * rectIndicator S₀ T₀ x y := by
  funext x y
  simp only [rectCombination_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-! ### The invariant and the greedy step -/

/-- **The iteration invariant** after `t` rounds: `t` recorded rectangles inside the carriers,
coefficients bounded by `1/ε`, and the potential bound `Φ(Rₜ) + t·ε²·M ≤ Φ(f)` on the residual,
strict once at least one round has been performed. -/
def CutIterInv (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y)
    (ε : ℝ) (t : ℕ) : Prop :=
  ∃ (c : Fin t → ℝ) (S : Fin t → Finset X) (T : Fin t → Finset Y),
    (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧ (∀ k, |c k| ≤ 1 / ε) ∧
    rectSqMass (fun x y => f x y - rectCombination c S T x y) wX wY A B
        + t * ε ^ 2 * (finsetMass wX A * finsetMass wY B)
      ≤ rectSqMass f wX wY A B ∧
    (1 ≤ t → rectSqMass (fun x y => f x y - rectCombination c S T x y) wX wY A B
        + t * ε ^ 2 * (finsetMass wX A * finsetMass wY B)
      < rectSqMass f wX wY A B)

/-- **`Inv 0`**: the empty family, with the residual `f` itself. -/
theorem cutIterInv_zero (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X)
    (B : Finset Y) (ε : ℝ) : CutIterInv f wX wY A B ε 0 := by
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, ?_, fun h => absurd h (by omega)⟩
  simp

/-- **The greedy step.** From `Inv t`, either the residual already has cut norm at most `ε·M`
(the recorded family is the decomposition) or a witness rectangle exists and `Inv (t + 1)` holds
with that rectangle appended at the residual's own average. Needs nonnegative weights, `0 < ε`,
and `Φ(f) ≤ M` (for the coefficient bound); **no boundedness of the residual**. -/
theorem cutIterInv_step (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {ε : ℝ} (hε : 0 < ε)
    (hΦ : rectSqMass f wX wY A B ≤ finsetMass wX A * finsetMass wY B) {t : ℕ}
    (h : CutIterInv f wX wY A B ε t) :
    (∃ (c : Fin t → ℝ) (S : Fin t → Finset X) (T : Fin t → Finset Y),
      (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧ (∀ k, |c k| ≤ 1 / ε) ∧
      rectCutNorm (fun x y => f x y - rectCombination c S T x y) wX wY A B
        ≤ ε * (finsetMass wX A * finsetMass wY B))
    ∨ CutIterInv f wX wY A B ε (t + 1) := by
  obtain ⟨c, S, T, hST, hc, hpot, hstrict⟩ := h
  set M := finsetMass wX A * finsetMass wY B with hM
  set R : RectKernel X Y := fun x y => f x y - rectCombination c S T x y with hR
  by_cases hdone : rectCutNorm R wX wY A B ≤ ε * M
  · exact Or.inl ⟨c, S, T, hST, hc, hdone⟩
  · right
    -- A witness rectangle.
    rw [rectCutNorm_le_iff] at hdone
    push Not at hdone
    obtain ⟨S₀, hS₀, T₀, hT₀, hwit⟩ := hdone
    have hM0 : 0 ≤ M := mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
    have hΦR : rectSqMass R wX wY A B ≤ M := by
      have := mul_nonneg (mul_nonneg (Nat.cast_nonneg t) (sq_nonneg ε)) hM0
      linarith
    have hMpos : 0 < M := finsetMass_mul_pos_of_lt_abs_rectSum hwX hwY hS₀ hT₀ hwit
    -- The new coefficient and its bound.
    set a := rectAverage R wX wY S₀ T₀ with ha
    have hcoef : |a| ≤ 1 / ε :=
      abs_rectAverage_le_inv_of_lt_abs_rectSum hwX hwY hS₀ hT₀ hε hwit hΦR
    -- The strict gain: the block energy of the witness exceeds `ε² M`.
    have hwS : ∀ x ∈ S₀, 0 ≤ wX x := fun x hx => hwX x (hS₀ hx)
    have hwT : ∀ y ∈ T₀, 0 ≤ wY y := fun y hy => hwY y (hT₀ hy)
    set d := finsetMass wX S₀ * finsetMass wY T₀ with hd
    have hdpos : 0 < d := by
      rcases eq_or_lt_of_le (mul_nonneg (finsetMass_nonneg hwS) (finsetMass_nonneg hwT)) with
        h0 | h0
      · exfalso
        rw [rectSum_eq_zero_of_finsetMass_mul_eq_zero hwS hwT (Finset.Subset.refl S₀)
          (Finset.Subset.refl T₀) h0.symm, abs_zero] at hwit
        nlinarith [mul_nonneg hε.le hM0]
      · exact h0
    have hdM : d ≤ M := mul_le_mul (finsetMass_mono hwX hS₀) (finsetMass_mono hwY hT₀)
      (finsetMass_nonneg hwT) (finsetMass_nonneg hwX)
    have hgain : ε ^ 2 * M < rectBlockEnergy R wX wY S₀ T₀ := by
      have hsq : (ε * M) ^ 2 < rectSum R wX wY S₀ T₀ ^ 2 := by
        have h1 : 0 ≤ ε * M := mul_nonneg hε.le hM0
        nlinarith [hwit, abs_nonneg (rectSum R wX wY S₀ T₀), sq_abs (rectSum R wX wY S₀ T₀)]
      -- `rectBlockEnergy = rectSum² / d`, and `d ≤ M`.
      have hbe : rectBlockEnergy R wX wY S₀ T₀ = rectSum R wX wY S₀ T₀ ^ 2 / d := by
        have hd0 : d ≠ 0 := hdpos.ne'
        rw [rectBlockEnergy, rectAverage, ← hd, div_pow]
        field_simp
      rw [hbe, lt_div_iff₀ hdpos]
      calc ε ^ 2 * M * d ≤ ε ^ 2 * M * M :=
            mul_le_mul_of_nonneg_left hdM (mul_nonneg (sq_nonneg ε) hM0)
        _ = (ε * M) ^ 2 := by ring
        _ < rectSum R wX wY S₀ T₀ ^ 2 := hsq
    -- The appended family.
    refine ⟨Fin.snoc c a, Fin.snoc S S₀, Fin.snoc T T₀, ?_, ?_, ?_, ?_⟩
    · intro k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [Fin.snoc_last, hS₀, hT₀]
      · simp [Fin.snoc_castSucc, hST i]
    · intro k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simpa [Fin.snoc_last] using hcoef
      · simpa [Fin.snoc_castSucc] using hc i
    all_goals
      have hres : (fun x y => f x y - rectCombination (Fin.snoc c a) (Fin.snoc S S₀)
          (Fin.snoc T T₀) x y) = fun x y => R x y - a * rectIndicator S₀ T₀ x y := by
        funext x y
        rw [rectCombination_snoc, hR]
        ring
      have hdec := rectSqMass_sub_rectAverage_smul_rectIndicator (wX := wX) (wY := wY) R hS₀ hT₀
      rw [hres, ← ha] at *
      rw [hdec]
      push_cast
    · -- `≤` form.
      nlinarith [hgain, hpot]
    · -- strict form, for every `t + 1 ≥ 1`.
      intro _
      nlinarith [hgain, hpot]

/-! ### The summit -/

/-- **The cut-matrix decomposition.** An absolutely unit-bounded kernel on `A ×ˢ B`, with
nonnegative carrier weights and `0 < ε`, is a combination of at most `⌈1/ε²⌉₊` weighted
rectangles inside the carriers, with coefficients of absolute value at most `1/ε`, plus a
residual of cut norm at most `ε` times the total mass. Denominator-free; no nonemptiness,
positive-mass, or `ε ≤ 1` hypothesis. -/
theorem kernel_frieze_kannan_cutDecomposition (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y),
      n ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ k, |c k| ≤ 1 / ε) ∧
      (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧
      rectCutNorm (fun x y => f x y - rectCombination c S T x y) wX wY A B
        ≤ ε * (finsetMass wX A * finsetMass wY B) := by
  set M := finsetMass wX A * finsetMass wY B with hM
  have hM0 : 0 ≤ M := mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  have hΦ : rectSqMass f wX wY A B ≤ M := by
    have := rectSqMass_le hwX hwY hf
    rwa [one_pow, one_mul] at this
  rcases eq_or_lt_of_le hM0 with hM0' | hMpos
  · -- Zero total mass: the empty decomposition.
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Nat.zero_le _,
      fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [← hM0', mul_zero]
    exact le_of_eq (rectCutNorm_eq_zero_of_finsetMass_mul_eq_zero hwX hwY hM0'.symm)
  · -- Positive mass: run the greedy iteration up to the budget.
    set N := ⌈1 / ε ^ 2⌉₊ with hN
    have hNε : 1 ≤ (N : ℝ) * ε ^ 2 := by
      have h1 : 1 / ε ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
      have hε2 : 0 < ε ^ 2 := by positivity
      rw [div_le_iff₀ hε2] at h1
      linarith
    -- Either some round `n ≤ t` has stopped, or the invariant holds at `t`.
    have hrun : ∀ t, t ≤ N →
        (∃ n ≤ t, ∃ (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y),
          (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧ (∀ k, |c k| ≤ 1 / ε) ∧
          rectCutNorm (fun x y => f x y - rectCombination c S T x y) wX wY A B ≤ ε * M)
        ∨ CutIterInv f wX wY A B ε t := by
      intro t
      induction t with
      | zero => intro _; exact Or.inr (cutIterInv_zero f wX wY A B ε)
      | succ t ih =>
        intro ht
        rcases ih (Nat.le_of_succ_le ht) with ⟨n, hn, hdec⟩ | hinv
        · exact Or.inl ⟨n, Nat.le_succ_of_le hn, hdec⟩
        · rcases cutIterInv_step f wX wY hwX hwY hε hΦ hinv with ⟨c, S, T, hST, hc, hdone⟩ | hnext
          · exact Or.inl ⟨t, Nat.le_succ t, c, S, T, hST, hc, hdone⟩
          · exact Or.inr hnext
    rcases hrun N le_rfl with ⟨n, hn, c, S, T, hST, hc, hdone⟩ | hinv
    · exact ⟨n, c, S, T, hn, hc, hST, hdone⟩
    · -- `N` consecutive failures contradict nonnegativity of the potential.
      exfalso
      obtain ⟨c, S, T, -, -, -, hstrict⟩ := hinv
      have hN1 : 1 ≤ N := by
        rw [hN, Nat.one_le_ceil_iff]
        positivity
      have hlt := hstrict hN1
      have hnn := rectSqMass_nonneg (f := fun x y => f x y - rectCombination c S T x y) hwX hwY
      have hNM : M ≤ (N : ℝ) * ε ^ 2 * M := by
        calc M = 1 * M := (one_mul M).symm
          _ ≤ (N : ℝ) * ε ^ 2 * M := mul_le_mul_of_nonneg_right hNε hM0
      linarith

/-! ### Corollaries -/

/-- **Normalized form**: the residual's cut norm divided by the total mass is at most `ε`,
guard-free under `x / 0 = 0`. -/
theorem kernel_frieze_kannan_cutDecomposition_normalized (f : RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset X) (T : Fin n → Finset Y),
      n ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ k, |c k| ≤ 1 / ε) ∧
      (∀ k, S k ⊆ A ∧ T k ⊆ B) ∧
      rectCutNorm (fun x y => f x y - rectCombination c S T x y) wX wY A B
        / (finsetMass wX A * finsetMass wY B) ≤ ε := by
  obtain ⟨n, c, S, T, hn, hc, hST, hcut⟩ :=
    kernel_frieze_kannan_cutDecomposition f wX wY hwX hwY hf hε
  refine ⟨n, c, S, T, hn, hc, hST, ?_⟩
  rcases eq_or_lt_of_le (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)) with
    h0 | hpos
  · rw [← h0, div_zero]
    exact hε.le
  · rw [div_le_iff₀ hpos]
    exact hcut

/-- The combination transposes with its rectangles swapped. -/
theorem rectCombination_op {n : ℕ} (c : Fin n → ℝ) (S : Fin n → Finset X)
    (T : Fin n → Finset Y) : (rectCombination c S T).op = rectCombination c T S := by
  funext y x
  simp only [RectKernel.op, rectCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← rectIndicator_op]
  rfl

/-- **`op` transport**: a decomposition of `f.op` on `B ×ˢ A` with the rectangles swapped. -/
theorem kernel_frieze_kannan_cutDecomposition_op (f : RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (T : Fin n → Finset Y) (S : Fin n → Finset X),
      n ≤ ⌈1 / ε ^ 2⌉₊ ∧
      (∀ k, |c k| ≤ 1 / ε) ∧
      (∀ k, T k ⊆ B ∧ S k ⊆ A) ∧
      rectCutNorm (fun y x => f.op y x - rectCombination c T S y x) wY wX B A
        ≤ ε * (finsetMass wX A * finsetMass wY B) := by
  obtain ⟨n, c, S, T, hn, hc, hST, hcut⟩ :=
    kernel_frieze_kannan_cutDecomposition f wX wY hwX hwY hf hε
  refine ⟨n, c, T, S, hn, hc, fun k => ⟨(hST k).2, (hST k).1⟩, ?_⟩
  have hres : (fun y x => f.op y x - rectCombination c T S y x)
      = RectKernel.op (fun x y => f x y - rectCombination c S T x y) := by
    funext y x
    rw [← rectCombination_op]
    rfl
  rw [hres, rectCutNorm_op]
  exact hcut

/-! ### Tests and adversarial examples -/

section Tests

/-- The `±1` chequerboard on `Fin 2 × Fin 2`. -/
private def cheqD : RectKernel (Fin 2) (Fin 2) := fun x y => if x = y then 1 else -1

private theorem cheqD_bounded : IsAbsUnitBoundedOnRectangle cheqD Finset.univ Finset.univ :=
  fun x _ y _ => by unfold cheqD; split_ifs <;> norm_num

-- **Budget arithmetic**, separately from the forcing: `⌈1/ε²⌉₊` is `4` at `ε = 1/2` and `25` at
-- `ε = 1/5`.
example : ⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ = 4 := by norm_num
example : ⌈1 / (1 / 5 : ℝ) ^ 2⌉₊ = 25 := by norm_num

-- **A forced update.** At unit weights the chequerboard has `M = 4` and cut norm `1`
-- (`Finite/RectKernelCutNorm.lean`), so at `ε = 1/5` the **empty** decomposition fails the
-- target `ε·M = 4/5 < 1`: the summit must record at least one rectangle. (At `ε = 1/2` the
-- target is `2`, and the empty decomposition already succeeds.)
example : ¬ (rectCutNorm cheqD (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    ≤ (1 / 5 : ℝ) * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
      * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ)) := by
  intro h
  have hcell := abs_rectSum_le_rectCutNorm (f := cheqD) (wX := fun _ => 1) (wY := fun _ => 1)
    (Finset.subset_univ ({0} : Finset (Fin 2))) (Finset.subset_univ ({0} : Finset (Fin 2)))
  simp [cheqD, rectSum, finsetMass] at hcell h
  linarith

-- The summit, instantiated on the chequerboard at `ε = 1/5`: at most `25` rectangles,
-- coefficients at most `5`, residual cut norm at most `4/5`.
example : ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset (Fin 2)) (T : Fin n → Finset (Fin 2)),
    n ≤ ⌈1 / (1 / 5 : ℝ) ^ 2⌉₊ ∧ (∀ k, |c k| ≤ 1 / (1 / 5 : ℝ)) ∧
    (∀ k, S k ⊆ Finset.univ ∧ T k ⊆ Finset.univ) ∧
    rectCutNorm (fun x y => cheqD x y - rectCombination c S T x y) (fun _ => 1) (fun _ => 1)
      Finset.univ Finset.univ
      ≤ (1 / 5 : ℝ) * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
        * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition cheqD _ _ (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) cheqD_bounded (by norm_num)

-- **`ε ≥ 1`: the empty decomposition suffices** by the trivial bound, so the summit's
-- existential is met with `n = 0`; pinned directly.
example : rectCutNorm (fun x y => cheqD x y
      - rectCombination (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i => i.elim0) (fun i => i.elim0)
        x y) (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    ≤ (1 : ℝ) * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
      * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ) := by
  rw [rectCombination_zero]
  simpa using rectCutNorm_le_mul_mass (f := cheqD) (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) zero_le_one cheqD_bounded

-- **Empty carrier and zero mass**: the summit holds with the target `0` (statement-level; the
-- proof takes the `M = 0` branch).
example (f : RectKernel (Fin 2) (Fin 3)) (hf : IsAbsUnitBoundedOnRectangle f ∅ Finset.univ) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset (Fin 2)) (T : Fin n → Finset (Fin 3)),
      n ≤ ⌈1 / (1 / 3 : ℝ) ^ 2⌉₊ ∧ (∀ k, |c k| ≤ 1 / (1 / 3 : ℝ)) ∧
      (∀ k, S k ⊆ ∅ ∧ T k ⊆ Finset.univ) ∧
      rectCutNorm (fun x y => f x y - rectCombination c S T x y) (fun _ => 1) (fun _ => 1)
        ∅ Finset.univ
        ≤ (1 / 3 : ℝ) * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) ∅
          * finsetMass (fun _ : Fin 3 => (1 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition f _ _ (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    hf (by norm_num)
example (hf : IsAbsUnitBoundedOnRectangle cheqD Finset.univ Finset.univ) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (S : Fin n → Finset (Fin 2)) (T : Fin n → Finset (Fin 2)),
      n ≤ ⌈1 / (1 / 3 : ℝ) ^ 2⌉₊ ∧ (∀ k, |c k| ≤ 1 / (1 / 3 : ℝ)) ∧
      (∀ k, S k ⊆ Finset.univ ∧ T k ⊆ Finset.univ) ∧
      rectCutNorm (fun x y => cheqD x y - rectCombination c S T x y) (fun _ => 0) (fun _ => 0)
        Finset.univ Finset.univ
        ≤ (1 / 3 : ℝ) * (finsetMass (fun _ : Fin 2 => (0 : ℝ)) Finset.univ
          * finsetMass (fun _ : Fin 2 => (0 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition cheqD _ _ (fun _ _ => le_rfl) (fun _ _ => le_rfl) hf
    (by norm_num)

-- **Coefficient sanity check**: the single rectangle kernel `𝟙_{{0}×{0}}` decomposes exactly in
-- one round with coefficient `1`: the residual is `0`, so its cut norm is `0` at every `ε`.
example (ε : ℝ) : rectCutNorm (fun x y => rectIndicator ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2))
      x y - rectCombination ![(1 : ℝ)] ![({0} : Finset (Fin 2))] ![({0} : Finset (Fin 2))] x y)
      (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    ≤ ε * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
      * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ) ↔ 0 ≤ ε * 4 := by
  have hz : (fun x y => rectIndicator ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) x y
      - rectCombination ![(1 : ℝ)] ![({0} : Finset (Fin 2))] ![({0} : Finset (Fin 2))] x y)
      = fun _ _ => (0 : ℝ) := by
    funext x y
    simp [rectCombination_apply]
  rw [hz, rectCutNorm_le_iff]
  simp [rectSum, finsetMass]

-- **`op`**: the decomposition of `f.op` is that of `f` with the rectangles swapped, instantiated.
example : ∃ (n : ℕ) (c : Fin n → ℝ) (T : Fin n → Finset (Fin 2)) (S : Fin n → Finset (Fin 2)),
    n ≤ ⌈1 / (1 / 5 : ℝ) ^ 2⌉₊ ∧ (∀ k, |c k| ≤ 1 / (1 / 5 : ℝ)) ∧
    (∀ k, T k ⊆ Finset.univ ∧ S k ⊆ Finset.univ) ∧
    rectCutNorm (fun y x => cheqD.op y x - rectCombination c T S y x) (fun _ => 1) (fun _ => 1)
      Finset.univ Finset.univ
      ≤ (1 / 5 : ℝ) * (finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ
        * finsetMass (fun _ : Fin 2 => (1 : ℝ)) Finset.univ) :=
  kernel_frieze_kannan_cutDecomposition_op cheqD _ _ (fun _ _ => zero_le_one)
    (fun _ _ => zero_le_one) cheqD_bounded (by norm_num)

-- **`Inv 0`** holds for every kernel, and the greedy step is stated at any `t`.
example (f : RectKernel (Fin 2) (Fin 2)) (ε : ℝ) :
    CutIterInv f (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ ε 0 :=
  cutIterInv_zero f _ _ _ _ ε

end Tests

end RegularityLemmata
