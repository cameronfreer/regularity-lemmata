/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import RegularityLemmata.Finite.MulticolorRamsey
import RegularityLemmata.Finite.PairDensity

/-!
# Route (b) step 1: density buckets and the extraction instantiation

`ARCHITECTURE.md` route (b) ladder, step 1, second commit (design freeze 2026-07-20;
reviewer-specified split 2026-07-21): half-open density buckets and the multicolor
Ramsey instantiation extracting a subfamily of pieces whose pairwise densities are
aligned within `α`, for every relation of a finite family and in BOTH orientations.

* `densityBucket α x = ⌊x/α⌋₊` — the HALF-OPEN bucket `[k·α, (k+1)·α)`. Two values in
  one bucket differ by strictly less than `α`
  (`abs_sub_lt_of_densityBucket_eq`). Densities live in `[0, 1]`, which occupies the
  `⌊1/α⌋₊ + 1` buckets `0, …, ⌊1/α⌋₊` (`densityBucket_lt_of_le_one`). The endpoint
  behavior is pinned by permanent tests: density `0` lies in bucket `0`; density `1`
  lies in the top bucket, ALONE when `1/α` is an integer; and a boundary value `k·α`
  belongs to bucket `k`, not `k − 1` (half-open on the right).
* `exists_bucketAligned_subfamily` — the extraction: with at least
  `multicolorRamseyBound` pieces (for the color space of paired bucket vectors),
  there are `t` pieces such that for every relation index and every two
  chain-ordered piece pairs, the forward densities agree within `α` and the reverse
  densities agree within `α`. The Ramsey color of an ordered piece pair records the
  bucket vectors of BOTH orientations: gate G-U3 in `Graph/UniformUnion.lean` shows
  the reverse density is not determined by the forward one for a single relation —
  for palette families the swap law determines it, but retaining both explicitly is
  harmless and clearer (reviewer decision 2026-07-21).

The union theorem (`Graph/UniformUnion.lean`) consumes exactly this alignment: all
pairwise densities of the extracted pieces lie in a common `α`-window, so any member
serves as the class center `d` at width `2α`.
-/

namespace RegularityLemmata

/-! ### Half-open density buckets -/

/-- The half-open bucket index of `x` at width `α`: bucket `k` is `[k·α, (k+1)·α)`. -/
noncomputable def densityBucket (α x : ℝ) : ℕ := ⌊x / α⌋₊

/-- **Bucket equality forces `α`-closeness**, strictly. -/
theorem abs_sub_lt_of_densityBucket_eq {α x y : ℝ} (hα : 0 < α) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : densityBucket α x = densityBucket α y) : |x - y| < α := by
  have hx1 : (densityBucket α x : ℝ) ≤ x / α := Nat.floor_le (div_nonneg hx hα.le)
  have hx2 : x / α < (densityBucket α x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hy1 : (densityBucket α x : ℝ) ≤ y / α := by
    rw [h]
    exact Nat.floor_le (div_nonneg hy hα.le)
  have hy2 : y / α < (densityBucket α x : ℝ) + 1 := by
    rw [h]
    exact Nat.lt_floor_add_one _
  have hxy : x / α - y / α < 1 := by linarith
  have hyx : y / α - x / α < 1 := by linarith
  have hx' : x / α * α = x := div_mul_cancel₀ x (ne_of_gt hα)
  have hy' : y / α * α = y := div_mul_cancel₀ y (ne_of_gt hα)
  rw [abs_lt]
  constructor
  · have h1 := mul_lt_mul_of_pos_right hyx hα
    rw [sub_mul, hx', hy', one_mul] at h1
    linarith
  · have h1 := mul_lt_mul_of_pos_right hxy hα
    rw [sub_mul, hx', hy', one_mul] at h1
    linarith

/-- Values in `[0, 1]` occupy the buckets `0, …, ⌊1/α⌋₊`. -/
theorem densityBucket_lt_of_le_one {α x : ℝ} (hα : 0 < α) (hx1 : x ≤ 1) :
    densityBucket α x < ⌊1 / α⌋₊ + 1 := by
  rw [densityBucket, Nat.lt_add_one_iff]
  exact Nat.floor_le_floor (by gcongr)

/-! ### The extraction -/

section Extraction

variable {V : Type*} [DecidableEq V]

open Finset

omit [DecidableEq V] in
/-- **The bucket-aligned subfamily.** With at least `multicolorRamseyBound` pieces
(for the color space of paired bucket vectors over the `K` relations), there are `t`
pieces such that for every relation and every two chain-ordered piece pairs the
forward densities agree within `α` and the reverse densities agree within `α`. -/
theorem exists_bucketAligned_subfamily {K n t : ℕ}
    (Rk : Fin K → V → V → Prop) [inst : ∀ k, DecidableRel (Rk k)]
    (A : Fin n → Finset V) {α : ℝ} (hα : 0 < α)
    (hn : multicolorRamseyBound
        (Fintype.card ((Fin K → Fin (⌊1 / α⌋₊ + 1))
          × (Fin K → Fin (⌊1 / α⌋₊ + 1)))) t ≤ n) :
    ∃ g : Fin t → Fin n, Function.Injective g ∧
      ∀ k : Fin K, ∀ i j i' j' : Fin t, i < j → i' < j' →
        |pairDensity (Rk k) (A (g i)) (A (g j))
            - pairDensity (Rk k) (A (g i')) (A (g j'))| < α ∧
        |pairDensity (Rk k) (A (g j)) (A (g i))
            - pairDensity (Rk k) (A (g j')) (A (g i'))| < α := by
  classical
  set bucket : ℝ → Fin (⌊1 / α⌋₊ + 1) := fun x =>
    ⟨min (densityBucket α x) ⌊1 / α⌋₊, by omega⟩ with hbucket
  have hbeq : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      bucket x = bucket y → |x - y| < α := by
    intro x y hx0 hx1 hy0 hy1 hxy
    have h1 : densityBucket α x ≤ ⌊1 / α⌋₊ :=
      Nat.lt_add_one_iff.mp (densityBucket_lt_of_le_one hα hx1)
    have h2 : densityBucket α y ≤ ⌊1 / α⌋₊ :=
      Nat.lt_add_one_iff.mp (densityBucket_lt_of_le_one hα hy1)
    have h3 : min (densityBucket α x) ⌊1 / α⌋₊
        = min (densityBucket α y) ⌊1 / α⌋₊ := congrArg Fin.val hxy
    rw [min_eq_left h1, min_eq_left h2] at h3
    exact abs_sub_lt_of_densityBucket_eq hα hx0 hy0 h3
  set χ : Fin n → Fin n
      → (Fin K → Fin (⌊1 / α⌋₊ + 1)) × (Fin K → Fin (⌊1 / α⌋₊ + 1)) := fun a b =>
    (fun k => bucket (pairDensity (Rk k) (A a) (A b)),
     fun k => bucket (pairDensity (Rk k) (A b) (A a))) with hχ
  set e := Fintype.equivFin ((Fin K → Fin (⌊1 / α⌋₊ + 1))
    × (Fin K → Fin (⌊1 / α⌋₊ + 1))) with he
  obtain ⟨v, c, hmem, hinj, hchain⟩ :=
    exists_monochromatic_subchain (fun a b => e (χ a b)) (univ : Finset (Fin n))
      (by rwa [Finset.card_univ, Fintype.card_fin])
  refine ⟨v, hinj, ?_⟩
  intro k i j i' j' hij hij'
  have h1 : χ (v i) (v j) = χ (v i') (v j') :=
    e.injective ((hchain i j hij).trans (hchain i' j' hij').symm)
  have hfwd : bucket (pairDensity (Rk k) (A (v i)) (A (v j)))
      = bucket (pairDensity (Rk k) (A (v i')) (A (v j'))) :=
    congrFun (congrArg Prod.fst h1) k
  have hrev : bucket (pairDensity (Rk k) (A (v j)) (A (v i)))
      = bucket (pairDensity (Rk k) (A (v j')) (A (v i'))) :=
    congrFun (congrArg Prod.snd h1) k
  exact ⟨hbeq _ _ pairDensity_nonneg pairDensity_le_one
      pairDensity_nonneg pairDensity_le_one hfwd,
    hbeq _ _ pairDensity_nonneg pairDensity_le_one
      pairDensity_nonneg pairDensity_le_one hrev⟩

end Extraction

/-! ### Tests: endpoint behavior of the half-open buckets -/

section Tests

-- Density `0` lies in bucket `0`.
example : densityBucket (1/4 : ℝ) 0 = 0 := by
  rw [densityBucket]
  norm_num

-- Density `1` lies in the top bucket `⌊1/α⌋₊ = 4`.
example : densityBucket (1/4 : ℝ) 1 = 4 := by
  rw [densityBucket, Nat.floor_eq_iff (by norm_num)]
  norm_num

-- …and, when `1/α` is an integer, ALONE: every density strictly below `1` lands in
-- a lower bucket, so the top class carries no width at the right endpoint.
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : densityBucket (1/4 : ℝ) x < 4 := by
  rw [densityBucket, Nat.floor_lt (by positivity)]
  have : x / (1/4 : ℝ) = 4 * x := by ring
  rw [this]
  push_cast
  linarith

-- The boundary value `k·α` belongs to bucket `k`, NOT `k − 1`: half-open on the
-- right, matching the inclusive largeness cutoffs elsewhere in the route.
example : densityBucket (1/4 : ℝ) (1/4) = 1 := by
  rw [densityBucket, Nat.floor_eq_iff (by norm_num)]
  norm_num

-- A generic interior value: `1/5 ∈ [0, 1/4)` is in bucket `0`.
example : densityBucket (1/4 : ℝ) (1/5) = 0 := by
  rw [densityBucket]
  norm_num

-- Bucket equality at width `1/4` forces closeness within `1/4`, strictly —
-- instantiating the generic lemma at the endpoint test values.
example (x : ℝ) (h0 : 0 ≤ x)
    (h : densityBucket (1/4 : ℝ) x = densityBucket (1/4 : ℝ) 1) :
    |x - 1| < 1/4 :=
  abs_sub_lt_of_densityBucket_eq (by norm_num) h0 (by norm_num) h

end Tests

end RegularityLemmata
