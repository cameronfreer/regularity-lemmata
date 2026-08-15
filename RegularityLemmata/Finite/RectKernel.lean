/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Weight
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Rectangular weighted kernels

A kernel between two possibly different finite carriers, together with **raw carrier weights
on both sides**. The design freeze is `docs/design/rectangular-kernels.md`.

`RectKernel` is an unbundled function alias, not a structure: bundling a boundedness proof
into the kernel would make addition, subtraction, indicators, and restriction awkward, so
bounds are predicates and hypotheses instead.

The weighted `rectSum` is the **primitive**; `rectAverage` divides by the product of the two
carrier masses, and the unweighted counting forms are wrappers at `wX = wY = 1`. Building the
unweighted version as primitive would force a second weighted API later, and would make cell
masses in partition formulas come out as cardinalities.

## Traps this file pins

* A **nonempty** rectangle can have **zero mass**, since every weight may vanish. So
  `rectAverage_const` requires `0 < finsetMass`, not nonemptiness — and a test witnesses the
  gap.
* General interval preservation on a zero-mass rectangle needs `0 ∈ [a,b]`, because the
  guard-free average is then `0`. Only `[0,1]` and `[-C,C]` get unconditional forms.
* Absolute estimates need **nonnegative** carrier weights; with signed weights the triangle
  inequality goes the wrong way.
* `pullback` evaluation and composition are unconditional, but transporting a *sum* along an
  arbitrary map needs injectivity or explicit fibre multiplicities. No such transport is
  claimed here.
* `restrict` restricts the kernel **and the weights** by subtype inclusion, with **no
  renormalization**.

Partitions, stepification, energy, variance, and cut discrepancy are deliberately absent;
they belong to the next tranche.
-/

namespace RegularityLemmata

/-- A rectangular kernel between two carriers. Unbundled on purpose — boundedness is a
hypothesis, not a field. -/
abbrev RectKernel (X Y : Type*) := X → Y → ℝ

variable {X Y X' Y' : Type*}

/-! ### Weighted rectangle sums and averages -/

/-- The **primitive**: the weighted sum of a kernel over a rectangle. -/
def rectSum (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, wX x * wY y * f x y

/-- The weighted average, guard-free: zero when either carrier mass vanishes. -/
noncomputable def rectAverage (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  rectSum f wX wY A B / (finsetMass wX A * finsetMass wY B)

/-- The uniform-counting specialization of `rectSum`. -/
noncomputable abbrev rectSumCount (f : RectKernel X Y) (A : Finset X) (B : Finset Y) : ℝ :=
  rectSum f (fun _ => 1) (fun _ => 1) A B

/-- The uniform-counting specialization of `rectAverage`. -/
noncomputable abbrev rectAverageCount (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) : ℝ :=
  rectAverage f (fun _ => 1) (fun _ => 1) A B

variable {f g : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ} {A : Finset X} {B : Finset Y}

@[simp] theorem rectSum_empty_left (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (B : Finset Y) : rectSum f wX wY ∅ B = 0 := by
  rw [rectSum, Finset.sum_empty]

@[simp] theorem rectSum_empty_right (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) : rectSum f wX wY A ∅ = 0 := by
  rw [rectSum]
  exact Finset.sum_eq_zero fun x _ => Finset.sum_empty

/-! ### Algebra -/

@[simp] theorem rectSum_zero (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectSum (fun _ _ => (0 : ℝ)) wX wY A B = 0 := by
  rw [rectSum]
  exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => mul_zero _

/-- A constant kernel's weighted sum is the constant times the rectangle mass. -/
theorem rectSum_const (c : ℝ) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectSum (fun _ _ => c) wX wY A B = c * (finsetMass wX A * finsetMass wY B) := by
  rw [rectSum, finsetMass, finsetMass, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem rectSum_add (f g : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => f x y + g x y) wX wY A B
      = rectSum f wX wY A B + rectSum g wX wY A B := by
  rw [rectSum, rectSum, rectSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem rectSum_neg (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => -f x y) wX wY A B = -rectSum f wX wY A B := by
  rw [rectSum, rectSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem rectSum_sub (f g : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => f x y - g x y) wX wY A B
      = rectSum f wX wY A B - rectSum g wX wY A B := by
  rw [rectSum, rectSum, rectSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem rectSum_smul (c : ℝ) (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => c * f x y) wX wY A B = c * rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Rescaling one carrier weight rescales the sum.** Rescaling the other side is the same
statement through `op`. -/
theorem rectSum_smul_weight_left (c : ℝ) (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum f (fun x => c * wX x) wY A B = c * rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Rescaling **one** carrier weight leaves the average unchanged, for `c ≠ 0`: the sum and
the mass scale together. -/
theorem rectAverage_smul_weight_left {c : ℝ} (hc : c ≠ 0) (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectAverage f (fun x => c * wX x) wY A B = rectAverage f wX wY A B := by
  rw [rectAverage, rectAverage, rectSum_smul_weight_left, finsetMass_smul,
    show c * finsetMass wX A * finsetMass wY B
      = c * (finsetMass wX A * finsetMass wY B) from by ring]
  rcases eq_or_ne (finsetMass wX A * finsetMass wY B) 0 with h | h
  · rw [h, mul_zero, div_zero, div_zero]
  · rw [mul_div_mul_left _ _ hc]

/-! ### Transpose, pullback, restriction -/

/-- The transposed kernel. -/
def RectKernel.op (f : RectKernel X Y) : RectKernel Y X := fun y x => f x y

@[simp] theorem RectKernel.op_apply (f : RectKernel X Y) (y : Y) (x : X) :
    f.op y x = f x y := rfl

@[simp] theorem RectKernel.op_op (f : RectKernel X Y) : f.op.op = f := rfl

/-- `op` exchanges the two sides of a weighted sum. -/
theorem rectSum_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum f.op wY wX B A = rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [RectKernel.op_apply]; ring

theorem rectAverage_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectAverage f.op wY wX B A = rectAverage f wX wY A B := by
  rw [rectAverage, rectAverage, rectSum_op, mul_comm (finsetMass wY B)]

/-- Pullback along maps of both carriers. Evaluation and composition are unconditional;
transporting a **sum** along `u`, `v` is not, and is deliberately not stated — it would need
injectivity or explicit fibre multiplicities. -/
def RectKernel.pullback (f : RectKernel X Y) (u : X' → X) (v : Y' → Y) : RectKernel X' Y' :=
  fun x y => f (u x) (v y)

@[simp] theorem RectKernel.pullback_apply (f : RectKernel X Y) (u : X' → X) (v : Y' → Y)
    (x : X') (y : Y') : f.pullback u v x y = f (u x) (v y) := rfl

theorem RectKernel.pullback_pullback {X'' Y'' : Type*} (f : RectKernel X Y)
    (u : X' → X) (v : Y' → Y) (u' : X'' → X') (v' : Y'' → Y') :
    (f.pullback u v).pullback u' v' = f.pullback (u ∘ u') (v ∘ v') := rfl

@[simp] theorem RectKernel.pullback_id (f : RectKernel X Y) : f.pullback id id = f := rfl

/-- Restriction to subcarriers, by subtype inclusion. The **weights are carried across
unchanged** — no renormalization, per the design freeze. -/
def RectKernel.restrict (f : RectKernel X Y) (A : Finset X) (B : Finset Y) :
    RectKernel {x // x ∈ A} {y // y ∈ B} :=
  f.pullback Subtype.val Subtype.val

@[simp] theorem RectKernel.restrict_apply (f : RectKernel X Y) (A : Finset X) (B : Finset Y)
    (x : {x // x ∈ A}) (y : {y // y ∈ B}) : f.restrict A B x y = f x.val y.val := rfl

/-- The restricted weight on a subcarrier: the same raw weight, not renormalized. -/
def restrictWeight (w : X → ℝ) (A : Finset X) : {x // x ∈ A} → ℝ := fun x => w x.val

@[simp] theorem restrictWeight_apply (w : X → ℝ) (A : Finset X) (x : {x // x ∈ A}) :
    restrictWeight w A x = w x.val := rfl

/-! ### Boundedness

Signed and interval bounds are **different predicates**, because the Frieze–Kannan theory
handles signed residuals while relation indicators live in `[0,1]`. -/

/-- The kernel takes values in `[a, b]` on the rectangle. -/
def IsIccBoundedOnRectangle (f : RectKernel X Y) (a b : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, f x y ∈ Set.Icc a b

/-- The kernel is bounded in absolute value by `C` on the rectangle. -/
def IsAbsBoundedOnRectangle (f : RectKernel X Y) (C : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, |f x y| ≤ C

/-- Values in `[0,1]` — the relation-indicator case. -/
abbrev IsUnitIntervalOnRectangle (f : RectKernel X Y) (A : Finset X) (B : Finset Y) : Prop :=
  IsIccBoundedOnRectangle f 0 1 A B

/-- Absolute value at most `1` — the signed-residual case. -/
abbrev IsAbsUnitBoundedOnRectangle (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) : Prop :=
  IsAbsBoundedOnRectangle f 1 A B

theorem IsIccBoundedOnRectangle.absBounded {a b C : ℝ}
    (h : IsIccBoundedOnRectangle f a b A B) (ha : -C ≤ a) (hb : b ≤ C) :
    IsAbsBoundedOnRectangle f C A B := fun x hx y hy => by
  have := h x hx y hy
  rw [Set.mem_Icc] at this
  rw [abs_le]
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-! ### Estimates

All of these need **nonnegative carrier weights**: with signed weights the triangle
inequality points the wrong way. -/

theorem rectSum_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ f x y) : 0 ≤ rectSum f wX wY A B :=
  Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy =>
    mul_nonneg (mul_nonneg (hwX x hx) (hwY y hy)) (hf x hx y hy)

theorem rectAverage_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ f x y) : 0 ≤ rectAverage f wX wY A B :=
  div_nonneg (rectSum_nonneg hwX hwY hf)
    (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))

/-- The absolute rectangle-sum estimate, in **multiplication form**: no denominator, so no
positivity hypothesis on the masses. -/
theorem abs_rectSum_le {C : ℝ} (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsBoundedOnRectangle f C A B) :
    |rectSum f wX wY A B| ≤ C * (finsetMass wX A * finsetMass wY B) := by
  rw [← rectSum_const C wX wY A B]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [rectSum]
  refine Finset.sum_le_sum fun x hx => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun y hy => ?_
  rw [abs_mul, abs_of_nonneg (mul_nonneg (hwX x hx) (hwY y hy))]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) (mul_nonneg (hwX x hx) (hwY y hy))

/-- The absolute average estimate. **Guard-free**: on a zero-mass rectangle the average is
`0`, which is why `0 ≤ C` is the only extra hypothesis needed. -/
theorem abs_rectAverage_le {C : ℝ} (hC : 0 ≤ C) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) (hf : IsAbsBoundedOnRectangle f C A B) :
    |rectAverage f wX wY A B| ≤ C := by
  have hm : 0 ≤ finsetMass wX A * finsetMass wY B :=
    mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  rcases eq_or_lt_of_le hm with h | h
  · rw [rectAverage, ← h, div_zero, abs_zero]
    exact hC
  · rw [rectAverage, abs_div, abs_of_pos h, div_le_iff₀ h]
    exact abs_rectSum_le hwX hwY hf

/-- **Guard-free `[0,1]` bounds** for a unit-interval kernel: on a zero-mass rectangle the
average is `0`, which lies in `[0,1]`. This is the case where the interval contains `0`; see
`rectAverage_mem_Icc` for the general interval, which needs positive mass. -/
theorem rectAverage_mem_unitInterval (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsUnitIntervalOnRectangle f A B) :
    rectAverage f wX wY A B ∈ Set.Icc (0 : ℝ) 1 := by
  have habs : IsAbsBoundedOnRectangle f 1 A B :=
    hf.absBounded (by norm_num) le_rfl
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact rectAverage_nonneg hwX hwY fun x hx y hy => (Set.mem_Icc.mp (hf x hx y hy)).1
  · have := abs_rectAverage_le (by norm_num : (0:ℝ) ≤ 1) hwX hwY habs
    exact (abs_le.mp this).2

/-! ### Positive mass, not nonemptiness

A nonempty rectangle can have zero mass, so these statements assume positive mass. -/

/-- The average of a constant is the constant — **only under positive mass on both sides**.
Nonemptiness is not enough: every weight may vanish, and then the guard-free average is `0`
rather than `c`. -/
theorem rectAverage_const (c : ℝ) (hA : 0 < finsetMass wX A) (hB : 0 < finsetMass wY B) :
    rectAverage (fun _ _ => c) wX wY A B = c := by
  rw [rectAverage, rectSum_const, mul_div_assoc, div_self (by positivity), mul_one]

/-- General interval preservation. Positive mass is required, and unlike the `[0,1]` case it
cannot be dropped: on a zero-mass rectangle the average is `0`, which need not lie in
`[a,b]`. -/
theorem rectAverage_mem_Icc {a b : ℝ} (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hA : 0 < finsetMass wX A) (hB : 0 < finsetMass wY B)
    (hf : IsIccBoundedOnRectangle f a b A B) :
    rectAverage f wX wY A B ∈ Set.Icc a b := by
  have hm : 0 < finsetMass wX A * finsetMass wY B := mul_pos hA hB
  have hlow : a * (finsetMass wX A * finsetMass wY B) ≤ rectSum f wX wY A B := by
    rw [← rectSum_const a wX wY A B, rectSum, rectSum]
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (Set.mem_Icc.mp (hf x hx y hy)).1
      (mul_nonneg (hwX x hx) (hwY y hy))
  have hhigh : rectSum f wX wY A B ≤ b * (finsetMass wX A * finsetMass wY B) := by
    rw [← rectSum_const b wX wY A B, rectSum, rectSum]
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (Set.mem_Icc.mp (hf x hx y hy)).2
      (mul_nonneg (hwX x hx) (hwY y hy))
  rw [rectAverage, Set.mem_Icc, le_div_iff₀ hm, div_le_iff₀ hm]
  exact ⟨by linarith, by linarith⟩

/-! ### Tests and adversarial examples -/

section Tests

/-- A nonuniform weight on the left carrier. -/
private def wL : Fin 2 → ℝ := ![2, 3]

/-- A nonuniform weight on the right carrier. -/
private def wR : Fin 3 → ℝ := ![1, 2, 3]

/-- A genuinely **signed** kernel between different carriers, not an indicator. -/
private def sk : RectKernel (Fin 2) (Fin 3) := fun x y => if x.val ≤ y.val then 1 else -1

-- Nonuniform weights on `Fin 2 × Fin 3`: the rectangle mass is `5 · 6 = 30`.
example : finsetMass wL Finset.univ * finsetMass wR Finset.univ = 30 := by
  rw [finsetMass, finsetMass, Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [wL, wR, Matrix.cons_val_two, Matrix.tail_cons]

-- **A nonempty rectangle with all weights zero.** The average is `0`, not the constant, so
-- `rectAverage_const` genuinely needs positive mass rather than nonemptiness.
example : rectAverage (fun _ _ => (7 : ℝ)) (fun _ : Fin 2 => 0) (fun _ : Fin 3 => 0)
    Finset.univ Finset.univ = 0 := by
  rw [rectAverage, finsetMass_eq_zero_of_forall_eq_zero (fun _ _ => rfl), zero_mul, div_zero]

-- The signed kernel really is signed: its absolute bound is `1`, and it is **not**
-- `[0,1]`-valued.
example : IsAbsUnitBoundedOnRectangle sk Finset.univ Finset.univ := by
  intro x _ y _
  rw [sk]
  split <;> norm_num

example : ¬ IsUnitIntervalOnRectangle sk Finset.univ Finset.univ := by
  intro h
  have := (Set.mem_Icc.mp (h 1 (Finset.mem_univ _) 0 (Finset.mem_univ _))).1
  rw [sk] at this
  norm_num at this

-- **Rescaling only the left carrier** leaves the average fixed.
example (f : RectKernel (Fin 2) (Fin 3)) (A : Finset (Fin 2)) (B : Finset (Fin 3)) :
    rectAverage f (fun x => 5 * wL x) wR A B = rectAverage f wL wR A B :=
  rectAverage_smul_weight_left (by norm_num) f wL wR A B

-- **`op` between genuinely different carriers**: the transposed kernel lives on
-- `Fin 3 → Fin 2` and its weighted sum agrees.
example (A : Finset (Fin 2)) (B : Finset (Fin 3)) :
    rectSum sk.op wR wL B A = rectSum sk wL wR A B :=
  rectSum_op sk wL wR A B

-- A constant kernel's average, under positive mass on both sides.
example : rectAverage (fun _ _ => (7 : ℝ)) wL wR Finset.univ Finset.univ = 7 := by
  refine rectAverage_const 7 ?_ ?_
  · rw [finsetMass, Fin.sum_univ_two]; norm_num [wL]
  · rw [finsetMass, Fin.sum_univ_three]; norm_num [wR, Matrix.cons_val_two, Matrix.tail_cons]

end Tests

end RegularityLemmata
