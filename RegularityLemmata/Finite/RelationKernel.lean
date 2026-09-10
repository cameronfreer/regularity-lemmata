/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RectKernel
import RegularityLemmata.Finite.PairDensity

/-!
# Relation indicators as rectangular kernels

The bridge between the two independent cores. `RegularityLemmata/Finite/RectKernel.lean` knows
nothing about relations and `RegularityLemmata/Finite/PairDensity.lean` knows nothing about kernels;
this file imports both and identifies the indicator kernel's uniform-counting sum and average with
`pairCount` and `pairDensity`.

```
PairDensity ────┐
                ├─→ RelationKernel
RectKernel ─────┘
```

Keeping the two cores mutually independent is deliberate: the box layer wants masses without
kernels, and the kernel layer wants to develop its algebra and estimates without a relation
in sight.

Indicators are the `[0,1]`-valued case, so they satisfy `IsUnitIntervalOnRectangle`
unconditionally — this is the predicate that exists separately from `IsAbsBoundedOnRectangle`
precisely so that indicators and signed residuals are not conflated.
-/

namespace RegularityLemmata

variable {α β : Type*}

/-- The `0/1` indicator kernel of a relation. -/
def relationKernel (R : α → β → Prop) [DecidableRel R] : RectKernel α β :=
  fun a b => if R a b then 1 else 0

variable {R : α → β → Prop} [DecidableRel R] {A : Finset α} {B : Finset β}

@[simp] theorem relationKernel_apply (a : α) (b : β) :
    relationKernel R a b = if R a b then 1 else 0 := rfl

/-- Indicators take values in `[0,1]`, on every rectangle. -/
theorem isUnitIntervalOnRectangle_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) : IsUnitIntervalOnRectangle (relationKernel R) A B := by
  intro a _ b _
  rw [Set.mem_Icc, relationKernel]
  split <;> norm_num

/-- The indicator's absolute bound is `1` — the weaker signed statement, recorded so a
consumer working with residuals can use it without reproving. -/
theorem isAbsUnitBoundedOnRectangle_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) : IsAbsUnitBoundedOnRectangle (relationKernel R) A B :=
  (isUnitIntervalOnRectangle_relationKernel R A B).absBounded (by norm_num) le_rfl

/-! ### The pair bridges -/

/-- **The counting bridge**: at uniform weights, the indicator kernel's rectangle sum is the
pair count. -/
theorem rectSum_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectSum (relationKernel R) (fun _ => 1) (fun _ => 1) A B = (pairCount R A B : ℝ) := by
  classical
  rw [rectSum, pairCount, Finset.card_filter, Finset.sum_product]
  push_cast
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [relationKernel]
    split <;> norm_num

/-- The same statement through the counting wrapper. -/
theorem rectSumCount_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectSumCount (relationKernel R) A B = (pairCount R A B : ℝ) :=
  rectSum_relationKernel R A B

/-- **The density bridge**: at uniform weights, the indicator kernel's rectangle average is
the pair density. Guard-free on both sides — an empty side gives `0` either way. -/
theorem rectAverage_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectAverage (relationKernel R) (fun _ => 1) (fun _ => 1) A B = pairDensity R A B := by
  rw [rectAverage, rectSum_relationKernel, finsetMass_one, finsetMass_one,
    pairDensity_eq_count_div]

theorem rectAverageCount_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectAverageCount (relationKernel R) A B = pairDensity R A B :=
  rectAverage_relationKernel R A B

/-! ### Transpose and complement -/

/-- Transposing the kernel is transposing the relation. -/
@[simp] theorem relationKernel_op (R : α → β → Prop) [DecidableRel R] :
    (relationKernel R).op = relationKernel (swapRel R) := rfl

/-- The complement's indicator is `1` minus the indicator, pointwise. -/
theorem relationKernel_not (R : α → β → Prop) [DecidableRel R] (a : α) (b : β) :
    relationKernel (fun a b => ¬ R a b) a b = 1 - relationKernel R a b := by
  by_cases h : R a b <;> simp [relationKernel, h]

/-! ### Rectangle indicators and their finite combinations

The building blocks of the cut-matrix decomposition (design freeze
`docs/design/cut-matrix-decomposition.md`): the `0/1` indicator of a rectangle `S ×ˢ T`, as the
relation indicator of `x ∈ S ∧ y ∈ T`, and finite weighted combinations
`∑ k, c k • 𝟙_{S k} ⊗ 𝟙_{T k}`, indexed by `Fin n` so that the term count is a first-class
natural number. Rectangles may overlap freely; no partition is involved. -/

/-- The indicator kernel of the rectangle `S ×ˢ T`. -/
def rectIndicator [DecidableEq α] [DecidableEq β] (S : Finset α) (T : Finset β) :
    RectKernel α β :=
  relationKernel fun a b => a ∈ S ∧ b ∈ T

section RectIndicator

variable [DecidableEq α] [DecidableEq β] {S : Finset α} {T : Finset β}

@[simp] theorem rectIndicator_apply (S : Finset α) (T : Finset β) (a : α) (b : β) :
    rectIndicator S T a b = if a ∈ S ∧ b ∈ T then 1 else 0 := rfl

theorem isUnitIntervalOnRectangle_rectIndicator (S : Finset α) (T : Finset β) (A : Finset α)
    (B : Finset β) : IsUnitIntervalOnRectangle (rectIndicator S T) A B :=
  isUnitIntervalOnRectangle_relationKernel _ A B

/-- **The rectangle sum of an indicator is the mass of the overlap**: on `S' ×ˢ T'` it is
`mass (S' ∩ S) · mass (T' ∩ T)`, for arbitrary (signed) weights. -/
theorem rectSum_rectIndicator (S : Finset α) (T : Finset β) (wX : α → ℝ) (wY : β → ℝ)
    (S' : Finset α) (T' : Finset β) :
    rectSum (rectIndicator S T) wX wY S' T' = finsetMass wX (S' ∩ S) * finsetMass wY (T' ∩ T) := by
  rw [rectSum, finsetMass, finsetMass, Finset.sum_mul_sum, ← Finset.filter_mem_eq_inter,
    ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all

/-- Transposing a rectangle indicator swaps its sides. -/
theorem rectIndicator_op (S : Finset α) (T : Finset β) :
    (rectIndicator S T).op = rectIndicator T S := by
  funext b a
  simp [RectKernel.op, rectIndicator, relationKernel, and_comm]

end RectIndicator

/-- The kernel `∑ k, c k • 𝟙_{S k} ⊗ 𝟙_{T k}`: a finite weighted combination of rectangle
indicators, indexed by `Fin n`. -/
def rectCombination [DecidableEq α] [DecidableEq β] {n : ℕ} (c : Fin n → ℝ)
    (S : Fin n → Finset α) (T : Fin n → Finset β) : RectKernel α β :=
  fun a b => ∑ k, c k * rectIndicator (S k) (T k) a b

section RectCombination

variable [DecidableEq α] [DecidableEq β] {n : ℕ}

@[simp] theorem rectCombination_apply (c : Fin n → ℝ) (S : Fin n → Finset α)
    (T : Fin n → Finset β) (a : α) (b : β) :
    rectCombination c S T a b = ∑ k, c k * rectIndicator (S k) (T k) a b := rfl

/-- The empty combination is the zero kernel. -/
@[simp] theorem rectCombination_zero (c : Fin 0 → ℝ) (S : Fin 0 → Finset α)
    (T : Fin 0 → Finset β) : rectCombination c S T = fun _ _ => 0 := by
  funext a b; simp [rectCombination]

/-- **Linearity**: the rectangle sum of a combination is the combination of the overlap
masses, for arbitrary (signed) weights. -/
theorem rectSum_rectCombination (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β)
    (wX : α → ℝ) (wY : β → ℝ) (S' : Finset α) (T' : Finset β) :
    rectSum (rectCombination c S T) wX wY S' T'
      = ∑ k, c k * (finsetMass wX (S' ∩ S k) * finsetMass wY (T' ∩ T k)) := by
  unfold rectCombination
  rw [rectSum_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [rectSum_smul, rectSum_rectIndicator]

/-- Appending one weighted rectangle to a combination adds its term pointwise. -/
theorem rectCombination_snoc (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β)
    (a : ℝ) (S₀ : Finset α) (T₀ : Finset β) :
    rectCombination (Fin.snoc c a) (Fin.snoc S S₀) (Fin.snoc T T₀)
      = fun x y => rectCombination c S T x y + a * rectIndicator S₀ T₀ x y := by
  funext x y
  simp only [rectCombination_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The combination transposes with its rectangles swapped. -/
theorem rectCombination_op (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β) :
    (rectCombination c S T).op = rectCombination c T S := by
  funext y x
  simp only [RectKernel.op, rectCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← rectIndicator_op]
  rfl

end RectCombination

/-! ### The decrement identities

The algebra of one round of the cut-matrix decomposition: subtracting a multiple of a
rectangle indicator from a kernel changes the pointwise square by a quadratic in the
coefficient, and at the rectangle's own average the change is exactly minus the block energy.
Both identities are **hypothesis-free apart from rectangle containment** and hold for arbitrary
signed weights; positivity enters only the estimates (`RegularityLemmata/Finite/RectKernel.lean`).
-/

section Decrement

variable [DecidableEq α] [DecidableEq β] {wX : α → ℝ} {wY : β → ℝ} {A : Finset α}
  {B : Finset β} {S : Finset α} {T : Finset β}

/-- Multiplying by a rectangle indicator restricts the rectangle sum to the rectangle, when the
rectangle lies inside the carriers. -/
theorem rectSum_mul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A) (hT : T ⊆ B) :
    rectSum (fun x y => f x y * rectIndicator S T x y) wX wY A B = rectSum f wX wY S T := by
  rw [rectSum, rectSum, ← Finset.inter_eq_right.mpr hS, ← Finset.inter_eq_right.mpr hT,
    ← Finset.filter_mem_eq_inter, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all

/-- **The quadratic expansion**, arbitrary coefficient `a`:
`Φ(f − a·𝟙_{S×T}) = Φ(f) − 2a · rectSum f S T + a² · mass S · mass T`. -/
theorem rectSqMass_sub_smul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A) (hT : T ⊆ B)
    (a : ℝ) :
    rectSqMass (fun x y => f x y - a * rectIndicator S T x y) wX wY A B
      = rectSqMass f wX wY A B - 2 * a * rectSum f wX wY S T
        + a ^ 2 * (finsetMass wX S * finsetMass wY T) := by
  have hpt : ∀ x y, (f x y - a * rectIndicator S T x y) ^ 2
      = f x y ^ 2 - 2 * a * (f x y * rectIndicator S T x y) + a ^ 2 * rectIndicator S T x y := by
    intro x y
    rw [rectIndicator_apply]
    split_ifs <;> ring
  rw [rectSqMass, rectSqMass]
  simp_rw [hpt]
  rw [rectSum_add, rectSum_sub, rectSum_smul, rectSum_smul, rectSum_mul_rectIndicator f hS hT,
    rectSum_rectIndicator, Finset.inter_eq_right.mpr hS, Finset.inter_eq_right.mpr hT]

/-- **The decrement at the average**: subtracting the rectangle's own average drops the
pointwise square by exactly the block energy, `Φ(f − c·𝟙_{S×T}) = Φ(f) − c²·d` with
`c = rectAverage f S T`. Signed weights are admitted: when the rectangle mass `d` vanishes the
totalized average is `0` and nothing changes; when `d ≠ 0`, `c · d = rectSum f S T` by
cancellation. -/
theorem rectSqMass_sub_rectAverage_smul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A)
    (hT : T ⊆ B) :
    rectSqMass (fun x y => f x y - rectAverage f wX wY S T * rectIndicator S T x y) wX wY A B
      = rectSqMass f wX wY A B - rectBlockEnergy f wX wY S T := by
  rw [rectSqMass_sub_smul_rectIndicator f hS hT, rectBlockEnergy]
  rcases eq_or_ne (finsetMass wX S * finsetMass wY T) 0 with h0 | h0
  · rw [rectAverage, h0, div_zero]
    ring
  · have hc : rectAverage f wX wY S T * (finsetMass wX S * finsetMass wY T)
        = rectSum f wX wY S T := by
      rw [rectAverage]
      exact div_mul_cancel₀ _ h0
    rw [← hc]
    ring

end Decrement

/-! ### Tests and adversarial examples -/

section Tests

-- The rectangular running example: `a ≤ b` on `Fin 2 → Fin 3` has `5` related pairs and
-- density `5/6`, recovered through the kernel layer.
example : rectSumCount (relationKernel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val))
    Finset.univ Finset.univ = 5 := by
  rw [rectSumCount_relationKernel,
    show pairCount (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
      Finset.univ Finset.univ = 5 from by decide]
  norm_num

example : rectAverageCount (relationKernel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val))
    Finset.univ Finset.univ = 5 / 6 := by
  rw [rectAverageCount_relationKernel, pairDensity_eq_count_div,
    show pairCount (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)
      Finset.univ Finset.univ = 5 from by decide]
  simp
  norm_num

-- **Complement indicators on an empty rectangle**: both sums are `0`, matching the
-- guard-free count behaviour rather than summing to the rectangle mass.
example (B : Finset (Fin 3)) :
    rectSumCount (relationKernel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)) ∅ B = 0 ∧
      rectSumCount (relationKernel (fun (a : Fin 2) (b : Fin 3) => ¬ (a.val ≤ b.val)))
        ∅ B = 0 :=
  ⟨rectSum_empty_left _ _ _ _, rectSum_empty_left _ _ _ _⟩

-- The transpose bridge, between genuinely different carriers.
example (A : Finset (Fin 2)) (B : Finset (Fin 3)) :
    rectSumCount (relationKernel (swapRel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)))
        B A
      = rectSumCount (relationKernel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)) A B := by
  rw [← relationKernel_op]
  exact rectSum_op _ _ _ A B

-- Indicators are `[0,1]`-valued, which is the predicate that keeps them distinct from
-- signed residuals.
example (A : Finset (Fin 2)) (B : Finset (Fin 3)) :
    IsUnitIntervalOnRectangle
      (relationKernel (fun (a : Fin 2) (b : Fin 3) => a.val ≤ b.val)) A B :=
  isUnitIntervalOnRectangle_relationKernel _ A B

-- **Rectangle indicators.** On `{0} ×ˢ {1, 2} ⊆ Fin 2 × Fin 3` at unit weights the full
-- rectangle sum is the overlap mass `1 · 2 = 2`; restricted to `{1} ×ˢ univ` it is `0`.
example : rectSum (rectIndicator ({0} : Finset (Fin 2)) ({1, 2} : Finset (Fin 3)))
    (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ = 2 := by
  rw [rectSum_rectIndicator]; simp [finsetMass]
example : rectSum (rectIndicator ({0} : Finset (Fin 2)) ({1, 2} : Finset (Fin 3)))
    (fun _ => 1) (fun _ => 1) {1} Finset.univ = 0 := by
  rw [rectSum_rectIndicator]; simp [finsetMass]

-- **Signed weights are admitted** by the overlap identity: weights `1, −1` on `Fin 2` give the
-- indicator of `univ ×ˢ univ` total rectangle sum `0 · 0 = 0`.
example : rectSum (rectIndicator (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 2)))
    (fun i => if i = 0 then 1 else -1) (fun i => if i = 0 then 1 else -1)
    Finset.univ Finset.univ = 0 := by
  rw [rectSum_rectIndicator]; simp [finsetMass, Fin.sum_univ_two]

-- **The empty combination is the zero kernel**, and a one-term combination is its rectangle
-- scaled by its coefficient.
example : rectCombination (fun i : Fin 0 => (i.elim0 : ℝ)) (fun i => i.elim0) (fun i => i.elim0)
    = (fun (_ : Fin 2) (_ : Fin 3) => (0 : ℝ)) :=
  rectCombination_zero _ _ _
example : rectSum (rectCombination ![(3 : ℝ)] ![({0} : Finset (Fin 2))]
      ![({1, 2} : Finset (Fin 3))]) (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ = 6 := by
  rw [rectSum_rectCombination]; simp [finsetMass]; norm_num

-- **The `±1` chequerboard on `Fin 2` is a three-term combination**,
-- `2·𝟙_{{0}×{0}} + 2·𝟙_{{1}×{1}} − 𝟙_{univ×univ}`, pointwise.
example (x y : Fin 2) :
    rectCombination ![(2 : ℝ), 2, -1] ![({0} : Finset (Fin 2)), {1}, Finset.univ]
        ![({0} : Finset (Fin 2)), {1}, Finset.univ] x y
      = if x = y then 1 else -1 := by
  fin_cases x <;> fin_cases y <;> simp [rectCombination, Fin.sum_univ_three] <;> norm_num

-- **Transposing an indicator swaps its sides.**
example : (rectIndicator ({0} : Finset (Fin 2)) ({1, 2} : Finset (Fin 3))).op
    = rectIndicator ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 2)) :=
  rectIndicator_op _ _

/-! #### The decrement identities -/

/-- The `±1` chequerboard on `Fin 2 × Fin 2`. -/
private def cheqR : RectKernel (Fin 2) (Fin 2) := fun x y => if x = y then 1 else -1

-- **One round on the chequerboard**: subtracting the cell `{0} × {0}` at its average `1` drops
-- the pointwise square from `4` by the block energy `1`, statement-level from the identity.
example : rectSqMass (fun x y => cheqR x y
      - rectAverage cheqR (fun _ => 1) (fun _ => 1) {0} {0} * rectIndicator {0} {0} x y)
      (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
    = rectSqMass cheqR (fun _ => 1) (fun _ => 1) Finset.univ Finset.univ
      - rectBlockEnergy cheqR (fun _ => 1) (fun _ => 1) {0} {0} :=
  rectSqMass_sub_rectAverage_smul_rectIndicator cheqR (Finset.subset_univ _)
    (Finset.subset_univ _)

-- **Signed weights that cancel to zero total mass** are admitted by the expansion: with weights
-- `1, −1` on both sides the full rectangle has mass `0 · 0`, and the identity still holds as
-- stated — it fails if anyone strengthens the hypotheses to nonnegativity.
example (f : RectKernel (Fin 2) (Fin 2)) (a : ℝ) :
    rectSqMass (fun x y => f x y - a * rectIndicator Finset.univ Finset.univ x y)
      (fun i => if i = 0 then (1 : ℝ) else -1) (fun i => if i = 0 then (1 : ℝ) else -1)
      Finset.univ Finset.univ
    = rectSqMass f (fun i => if i = 0 then (1 : ℝ) else -1) (fun i => if i = 0 then (1 : ℝ) else -1)
        Finset.univ Finset.univ
      - 2 * a * rectSum f (fun i => if i = 0 then (1 : ℝ) else -1)
          (fun i => if i = 0 then (1 : ℝ) else -1) Finset.univ Finset.univ
      + a ^ 2 * (finsetMass (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) Finset.univ
          * finsetMass (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) Finset.univ) :=
  rectSqMass_sub_smul_rectIndicator f (Finset.Subset.refl _) (Finset.Subset.refl _) a

-- …and at the average with zero rectangle mass, the totalized average is `0`, so the update is
-- the identity: the decrement is the block energy `0`.
example (f : RectKernel (Fin 2) (Fin 2)) :
    rectSqMass (fun x y => f x y - rectAverage f (fun i => if i = 0 then (1 : ℝ) else -1)
        (fun i => if i = 0 then (1 : ℝ) else -1) Finset.univ Finset.univ
        * rectIndicator Finset.univ Finset.univ x y)
      (fun i => if i = 0 then (1 : ℝ) else -1) (fun i => if i = 0 then (1 : ℝ) else -1)
      Finset.univ Finset.univ
    = rectSqMass f (fun i => if i = 0 then (1 : ℝ) else -1) (fun i => if i = 0 then (1 : ℝ) else -1)
        Finset.univ Finset.univ
      - rectBlockEnergy f (fun i => if i = 0 then (1 : ℝ) else -1)
          (fun i => if i = 0 then (1 : ℝ) else -1) Finset.univ Finset.univ :=
  rectSqMass_sub_rectAverage_smul_rectIndicator f (Finset.Subset.refl _) (Finset.Subset.refl _)

end Tests

end RegularityLemmata
