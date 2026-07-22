/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import RegularityLemmata.Graph.BadMass

/-!
# Equitable-supplier ladder, step 2: finite-family regularity surfaces

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence
step 2: the generic surfaces for regularity of finitely many DIRECTED relations
simultaneously — in `Graph/`, independent of relational palettes.

* `IsFamilyRegular Rk ε P` — `ε`-regularity (off-diagonal, mass-weighted) for EVERY
  relation of the family. No symmetry is assumed anywhere: each `Rk k` is an
  arbitrary directed relation, and the singleton bridge (`isFamilyRegular_single`)
  applies verbatim to an asymmetric relation (permanent test below).
* `familyEnergy Rk P` — the SUM of the per-relation partition energies. The ceiling
  is `K`, not `1` (`familyEnergy_le_card`): the family iteration's fuel scales
  accordingly, and the one-step energy gain (sequence step 4) lifts a
  single-relation increment into the sum by monotonicity of every other summand
  under refinement (`familyEnergy_mono`).
* `familyStepBound` / `familyRegularityBound K ε l` — the closed-form part-count
  bound for the iterate (sequence step 5): one step atomises by the witness cuts of
  all `K` relations over both ordered directions (at most `2·K·n` cuts per cell,
  hence a `2^(2·K·n)` factor) and then equitabilises (a further mathlib-style
  `4^…` factor); the fuel is `⌈K/ε⁵⌉ + 1`, the energy ceiling `K` divided by the
  per-step gain. The bound is DELIBERATELY generous — only finiteness and
  monotonicity matter, quantitative optimality is out of scope, and no tower-type
  claim is made (see the Conlon–Fox scope in `PROVENANCE.md`).

Ordinary off-diagonal regularity only: this ladder does NOT touch equitable strong
regularity (deferred in `ARCHITECTURE.md`) nor the diagonal-inclusive layer.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-! ### Family regularity and family energy -/

/-- `ε`-regularity for every relation of a finite directed family. -/
def IsFamilyRegular {K : ℕ} (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (ε : ℝ) (P : Finpartition s) : Prop :=
  ∀ k, IsRegularPartition (Rk k) ε P

/-- The family energy: the sum of the per-relation partition energies. -/
noncomputable def familyEnergy {K : ℕ} (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (P : Finpartition s) : ℝ :=
  ∑ k, energy (Rk k) P

section Family

variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]
  {ε : ℝ} {P Q : Finpartition s}

/-- The singleton bridge: family regularity of one relation is that relation's
regularity. Nothing here assumes symmetry. -/
theorem isFamilyRegular_single {R : α → α → Prop} [DecidableRel R] :
    IsFamilyRegular (fun _ : Fin 1 => R) ε P ↔ IsRegularPartition R ε P := by
  constructor
  · intro h
    exact h 0
  · intro h k
    exact h

/-- The empty family is regular at every tolerance — the `K = 0` endpoint. -/
theorem isFamilyRegular_zero (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] : IsFamilyRegular Rk ε P :=
  fun k => k.elim0

theorem familyEnergy_nonneg : 0 ≤ familyEnergy Rk P :=
  Finset.sum_nonneg fun k _ => energy_nonneg (Rk k)

/-- The family-energy ceiling is `K`, not `1`. -/
theorem familyEnergy_le_card : familyEnergy Rk P ≤ (K : ℝ) := by
  calc familyEnergy Rk P
      ≤ ∑ _k : Fin K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => energy_le_one (Rk k)
    _ = (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one]

/-- Family energy is monotone under refinement — every summand is. -/
theorem familyEnergy_mono (hQ : Q ≤ P) : familyEnergy Rk P ≤ familyEnergy Rk Q :=
  Finset.sum_le_sum fun k _ => energy_mono (Rk k) hQ

/-- A single relation's energy is dominated by the family energy — the vehicle by
which a one-relation increment lifts into the family sum. -/
theorem energy_le_familyEnergy (k : Fin K) : energy (Rk k) P ≤ familyEnergy Rk P :=
  Finset.single_le_sum (f := fun k => energy (Rk k) P)
    (fun j _ => energy_nonneg (Rk j)) (Finset.mem_univ k)

/-- The empty family has zero energy. -/
theorem familyEnergy_zero (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] : familyEnergy Rk P = 0 := by
  simp [familyEnergy]

end Family

/-! ### The part-count bound -/

/-- One equitabilised family-refinement step, in closed form: witness atomisation
for `K` relations over both ordered directions splits each of `n` cells into at
most `2^(2·K·n)` atoms, and mathlib-style equitabilisation costs a further
exponential factor. Deliberately generous. -/
def familyStepBound (K n : ℕ) : ℕ :=
  n * 2 ^ (2 * K * n) * 4 ^ (n * 2 ^ (2 * K * n))

/-- The fuel-indexed iterate of the step bound. -/
def familyRegularityBoundAux (K : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | t + 1, m => familyRegularityBoundAux K t (familyStepBound K m)

/-- **The family part-count bound**: the step bound iterated `⌈K/ε⁵⌉ + 1` times
from `max l 2` — the energy ceiling `K` divided by the per-step gain, starting no
lower than the requested minimum part count. -/
noncomputable def familyRegularityBound (K : ℕ) (ε : ℝ) (l : ℕ) : ℕ :=
  familyRegularityBoundAux K (⌈(K : ℝ) / ε ^ 5⌉₊ + 1) (max l 2)

theorem le_familyStepBound (K n : ℕ) : n ≤ familyStepBound K n := by
  have h1 : 1 ≤ 2 ^ (2 * K * n) := Nat.one_le_two_pow
  have h2 : 1 ≤ 4 ^ (n * 2 ^ (2 * K * n)) := Nat.one_le_pow _ _ (by norm_num)
  calc n = n * 1 * 1 := by ring
    _ ≤ n * 2 ^ (2 * K * n) * 4 ^ (n * 2 ^ (2 * K * n)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left n h1) h2

theorem le_familyRegularityBoundAux (K t m : ℕ) :
    m ≤ familyRegularityBoundAux K t m := by
  induction t generalizing m with
  | zero => simp [familyRegularityBoundAux]
  | succ t IH =>
    rw [familyRegularityBoundAux]
    exact le_trans (le_familyStepBound K m) (IH _)

/-- The requested minimum part count survives to the bound. -/
theorem le_familyRegularityBound (K : ℕ) (ε : ℝ) (l : ℕ) :
    l ≤ familyRegularityBound K ε l := by
  rw [familyRegularityBound]
  exact le_trans (le_max_left l 2) (le_familyRegularityBoundAux K _ _)

/-- The bound is at least `2` — iterates never collapse below the seed. -/
theorem two_le_familyRegularityBound (K : ℕ) (ε : ℝ) (l : ℕ) :
    2 ≤ familyRegularityBound K ε l := by
  rw [familyRegularityBound]
  exact le_trans (le_max_right l 2) (le_familyRegularityBoundAux K _ _)

/-! ### Tests -/

section Tests

-- The `K = 0` endpoint, concretely: any partition of any host is family-regular
-- for the empty family at any tolerance, with zero family energy.
example (P : Finpartition (Finset.univ : Finset (Fin 3))) (ε : ℝ) :
    IsFamilyRegular (fun _ : Fin 0 => fun _ _ : Fin 3 => True) ε P :=
  isFamilyRegular_zero _

-- An ASYMMETRIC relation passes through the singleton bridge unchanged: family
-- regularity never assumes symmetry (the family version of gate G-U3).
example (P : Finpartition (Finset.univ : Finset (Fin 3))) (ε : ℝ)
    (h : IsRegularPartition (fun a b : Fin 3 => a = 0 ∧ b = 1) ε P) :
    IsFamilyRegular (fun _ : Fin 1 => fun a b : Fin 3 => a = 0 ∧ b = 1) ε P :=
  isFamilyRegular_single.mpr h

-- The step bound at the smallest seeds, by kernel computation: growth is monotone
-- and explosive, exactly as documented — only finiteness matters.
example : familyStepBound 0 2 = 32 := by decide

example : familyStepBound 1 1 = 4 * 4 ^ 4 := by decide

end Tests

end RegularityLemmata
