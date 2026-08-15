/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RectKernel
import RegularityLemmata.Finite.PairDensity

/-!
# Relation indicators as rectangular kernels

The bridge between the two independent cores. `Finite/RectKernel.lean` knows nothing about
relations and `Finite/PairDensity.lean` knows nothing about kernels; this file imports both
and identifies the indicator kernel's uniform-counting sum and average with `pairCount` and
`pairDensity`.

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

end Tests

end RegularityLemmata
