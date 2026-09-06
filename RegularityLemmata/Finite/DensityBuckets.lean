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
* `le_add_of_ceil_div_pred_eq` — the **predecessor-ceiling** bucket `⌈x / c⌉₊ - 1`, which
  cuts `[0, 1]` into exactly `⌈1/c⌉₊` buckets (one fewer than the half-open buckets whenever
  `1/c` is an integer): equal buckets and `0 ≤ y` give the **one-sided** closeness `x ≤ y + c`.
  It is one-sided because the truncated subtraction merges ceilings `0` and `1`, and it is
  not strict, both pinned by tests.
* `exists_bucketAligned_subfamily` — the extraction: with at least
  `multicolorRamseyBound` pieces (for the color space of paired bucket vectors),
  there are `t` pieces such that for every relation index and every two
  chain-ordered piece pairs, the forward densities agree within `α` and the reverse
  densities agree within `α`. The Ramsey color of an ordered piece pair records the
  bucket vectors of BOTH orientations: gate G-U3 in `Graph/UniformUnion.lean` shows
  the reverse density is not determined by the forward one for a single relation —
  for palette families the swap law determines it, but retaining both explicitly is
  harmless and clearer (reviewer decision 2026-07-21).

**What this feeds, and when.** Any two extracted densities of the SAME orientation
differ by strictly less than `α`, hence by at most `α`, so any member of a class
serves as that class's center at width `α`. But the union theorem
(`Graph/UniformUnion.lean`) consumes a SINGLE center `d` for EVERY ordered pair of
distinct pieces — both orientations at once. This extraction supplies two classes,
one forward and one reverse, and they feed `hclose` only when they share a common
center; symmetry of the relation is the clean sufficient condition, since then the
two classes coincide. For arbitrary DIRECTED relations they need not agree: gate
**G-U5** in `Graph/UniformUnion.lean` exhibits the strict order, forward class `1`
and reverse class `0`, where no center is within `α < 1/2` of both — and where the
self-union conclusion is not merely uninstantiable but FALSE. The results in this
file are unaffected; what fails is the proposed composition (`ARCHITECTURE.md`,
2026-07-26). Provenance: the bucket-and-extract step of
the Lemma 3.6 construction in D. Conlon and J. Fox, *Graph removal lemmas*
(arXiv:1211.3487, §3.2); see `PROVENANCE.md` for the precise scope.
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

/-! ### Predecessor-ceiling buckets -/

/-- **Closeness from equal predecessor-ceiling buckets.** If the `c`-buckets `⌈x / c⌉₊ - 1` and
`⌈y / c⌉₊ - 1` agree and `0 ≤ y`, then `x ≤ y + c`.

The conclusion is **one-sided**: with only `0 ≤ y` the symmetric claim `y ≤ x + c` is false
(`x = -100`, `y = 0`, `c = 1` satisfies the hypothesis, since the truncated subtraction merges the
ceilings `0` and `1` into one bucket). It also cannot be strengthened to `x < y + c`: `x = c`,
`y = 0` gives equality. This is the closeness fact for the consumer's bucketing of `[0, 1]` into
exactly `⌈1 / c⌉₊` buckets, as opposed to the `⌊1 / c⌋₊ + 1` half-open buckets of
`densityBucket`. Mathlib's pin has `Nat.ceil_eq_iff` and the floor-equality lemma
`Int.abs_sub_lt_one_of_floor_eq_floor` but no predecessor-ceiling variant. -/
theorem le_add_of_ceil_div_pred_eq {x y c : ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (h : ⌈x / c⌉₊ - 1 = ⌈y / c⌉₊ - 1) : x ≤ y + c := by
  rcases Nat.lt_or_ge ⌈y / c⌉₊ 2 with hy2 | hy2
  · -- Both ceilings are at most `1`, the merged bucket: `x ≤ c ≤ y + c`.
    have hx1 : ⌈x / c⌉₊ ≤ 1 := by omega
    have hxc : x / c ≤ (1 : ℕ) := Nat.ceil_le.mp hx1
    rw [Nat.cast_one, div_le_iff₀ hc, one_mul] at hxc
    linarith
  · -- Both ceilings equal some `q ≥ 2`: `x ≤ q·c` and `(q − 1)·c < y`.
    have hq : ⌈x / c⌉₊ = ⌈y / c⌉₊ := by omega
    have hq0 : ⌈y / c⌉₊ ≠ 0 := by omega
    obtain ⟨hy1, -⟩ := (Nat.ceil_eq_iff hq0).mp rfl
    obtain ⟨-, hx2⟩ := (Nat.ceil_eq_iff hq0).mp hq
    rw [div_le_iff₀ hc] at hx2
    rw [lt_div_iff₀ hc, Nat.cast_sub (by omega), Nat.cast_one, sub_mul, one_mul] at hy1
    linarith

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

-- **Predecessor-ceiling closeness is one-sided.** `x = -100`, `y = 0`, `c = 1` satisfies the
-- hypothesis (both ceilings are `0`, and so are both truncated predecessors), the conclusion
-- `x ≤ y + c` holds, and the symmetric `y ≤ x + c` fails.
private theorem ceil_neg_hundred : ⌈(-100 : ℝ) / 1⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by norm_num)
private theorem ceil_zero : ⌈(0 : ℝ) / 1⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by norm_num)
private theorem ceil_half : ⌈(1 / 2 : ℝ) / 1⌉₊ = 1 :=
  (Nat.ceil_eq_iff one_ne_zero).mpr ⟨by norm_num, by norm_num⟩
private theorem ceil_one : ⌈(1 : ℝ) / 1⌉₊ = 1 :=
  (Nat.ceil_eq_iff one_ne_zero).mpr ⟨by norm_num, by norm_num⟩

example : ⌈(-100 : ℝ) / 1⌉₊ - 1 = ⌈(0 : ℝ) / 1⌉₊ - 1 := by rw [ceil_neg_hundred, ceil_zero]
example : (-100 : ℝ) ≤ 0 + 1 :=
  le_add_of_ceil_div_pred_eq one_pos le_rfl (by rw [ceil_neg_hundred, ceil_zero])
example : ¬ ((0 : ℝ) ≤ -100 + 1) := by norm_num

-- **The merged `0`-bucket**: `x = 0` has ceiling `0` and `y = c / 2` has ceiling `1`; the
-- truncated predecessors agree, and the conclusion `0 ≤ c / 2 + c` holds (at `c = 1`).
example : ⌈(0 : ℝ) / 1⌉₊ - 1 = ⌈(1 / 2 : ℝ) / 1⌉₊ - 1 := by rw [ceil_zero, ceil_half]
example : (0 : ℝ) ≤ 1 / 2 + 1 :=
  le_add_of_ceil_div_pred_eq one_pos (by norm_num) (by rw [ceil_zero, ceil_half])

-- **Equality can occur**: `x = c`, `y = 0` (ceilings `1` and `0`, predecessors both `0`) gives
-- `x = y + c` exactly, so the conclusion cannot be strengthened to `x < y + c`.
example : ⌈(1 : ℝ) / 1⌉₊ - 1 = ⌈(0 : ℝ) / 1⌉₊ - 1 := by rw [ceil_one, ceil_zero]
example : (1 : ℝ) ≤ 0 + 1 :=
  le_add_of_ceil_div_pred_eq one_pos le_rfl (by rw [ceil_one, ceil_zero])
example : ¬ ((1 : ℝ) < 0 + 1) := by norm_num

end Tests

end RegularityLemmata
