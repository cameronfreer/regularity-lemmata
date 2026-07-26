/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.UnionCenter

/-!
# Route (b) step 1: the equal-cardinality union theorem

`ARCHITECTURE.md` route (b) ladder, step 1 (design freeze 2026-07-20;
reviewer-specified statement 2026-07-21): a union of `s` pairwise-disjoint pieces of
COMMON positive cardinality, with every ordered pair of distinct pieces `α`-uniform
and all those densities within `α` of a common `d ∈ [0, 1]`, satisfies the exact
four-term estimate

    |density(X, Y) − density(U, U)| ≤ 3α + 2α/ε + 1/(s·ε) + 1/s

on `ε`-large test sets, with stable term meanings: `3α` — pair regularity,
density-class width, and comparison of `density(U, U)` with the class center;
`2α/ε` — pieces on which `X` or `Y` is too small to invoke pair regularity;
`1/(s·ε)` — the uncontrolled within-piece contribution inside `X × Y`; `1/s` — the
within-piece contribution to `density(U, U)`. The diagonal bound is the equal-size
estimate (costing `1/(s·ε)`, NOT `1/(s·ε²)`), which is what makes `α = (ε/3)²`,
`s ≥ 2/α` viable (`isUniformPair_self_union`, displayed error at most `2ε/3`).

Equal cardinality is a genuine hypothesis: comparable-but-unequal pieces incur a
comparability factor `Λ` in both within-piece terms (gate G-U2), and the frozen
design trims comparable pieces to equal size FIRST via `Graph/UniformSlicing.lean`.
The `α·m ≤ |X∩Aᵢ|` cutoff is inclusive (gate G-U4), matching `IsUniformPair`.

**A single common center is a genuine hypothesis too, and it is what breaks the
DIRECTED self-union composition** (gate G-U5, 2026-07-26): `hclose` demands one `d`
for EVERY ordered pair, while the density-bucket extraction
(`Finite/DensityBuckets.lean`) aligns a forward class and a reverse class which by
gate G-U3 need not agree. For the strict order relation they are `1` and `0`, no
center is within `α < 1/2` of both, and indeed no positive-linear-size self-uniform
subset exists at tolerance `1/4`. The theorems in this file are unaffected and
remain valid — what fails is the proposed route (b) step 1 composition for arbitrary
directed relations; see `ARCHITECTURE.md`.

Provenance: this adapts the Lemma 3.6 self-regular-subset construction of
D. Conlon and J. Fox, *Graph removal lemmas* (arXiv:1211.3487, §3.2) to directed
finite binary palettes; the piece supplier follows the weaker
regularity-plus-independent-set route the survey mentions, so no tower-type bound
is claimed, and the full cylinder lemma and their quantitative bounds are NOT
formalized (see `PROVENANCE.md`). The substrate lives in `Graph/UnionCenter.lean`.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {R : V → V → Prop} [DecidableRel R]

section Union

variable {s m : ℕ} {A : Fin s → Finset V} {α d ε : ℝ} {U X Y : Finset V}

/-- **The generic union estimate**, with the exact four-term error. -/
theorem pairDensity_union_sub_self_le (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hα : 0 < α) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) α)
    (hclose : ∀ i j : Fin s, i ≠ j → |pairDensity R (A i) (A j) - d| ≤ α)
    (hU : U = Finset.univ.biUnion A) (hX : X ⊆ U) (hY : Y ⊆ U)
    (hε : 0 < ε) (hXl : ε * (U.card : ℝ) ≤ (X.card : ℝ))
    (hYl : ε * (U.card : ℝ) ≤ (Y.card : ℝ)) :
    |pairDensity R X Y - pairDensity R U U|
      ≤ 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by
  have h1 := pairDensity_union_close_center hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX hY hε hXl hYl
  have h2 := pairDensity_union_self_close_center hm hs hdisj hcard hα hd0 hd1
    hclose hU
  calc |pairDensity R X Y - pairDensity R U U|
      ≤ |pairDensity R X Y - d| + |d - pairDensity R U U| := abs_sub_le _ _ _
    _ ≤ (2 * α + 2 * α / ε + 1 / ((s : ℝ) * ε)) + (α + 1 / (s : ℝ)) := by
        refine add_le_add h1 ?_
        rw [abs_sub_comm]
        exact h2
    _ = 3 * α + 2 * α / ε + 1 / ((s : ℝ) * ε) + 1 / (s : ℝ) := by ring

/-- **The self-uniformity corollary at the frozen constants**: with `α = (ε/3)²` and
`2 ≤ α·s`, the union is `ε`-uniform with itself — the displayed error is at most
`2ε/3`, leaving slack for later slicing and palette bookkeeping. -/
theorem isUniformPair_self_union (hm : 0 < m) (hs : 0 < s)
    (hdisj : ∀ i j : Fin s, i ≠ j → Disjoint (A i) (A j))
    (hcard : ∀ i, (A i).card = m)
    (hunif : ∀ i j : Fin s, i ≠ j → IsUniformPair R (A i) (A j) ((ε / 3) ^ 2))
    (hclose : ∀ i j : Fin s, i ≠ j →
      |pairDensity R (A i) (A j) - d| ≤ (ε / 3) ^ 2)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hU : U = Finset.univ.biUnion A)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsα : 2 ≤ (ε / 3) ^ 2 * (s : ℝ)) :
    IsUniformPair R U U ε := by
  intro X' hX' Y' hY' hXc hYc
  have hα : (0 : ℝ) < (ε / 3) ^ 2 := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htri := pairDensity_union_sub_self_le hm hs hdisj hcard hα hd0 hd1 hunif
    hclose hU hX' hY' hε hXc hYc
  refine le_trans htri ?_
  have e1 : 2 * (ε / 3) ^ 2 / ε = 2 * ε / 9 := by
    field_simp
    ring
  have e2 : 1 / ((s : ℝ) * ε) ≤ ε / 18 := by
    rw [div_le_iff₀ (mul_pos hsR hε)]
    nlinarith [hsα]
  have e3 : 1 / (s : ℝ) ≤ ε ^ 2 / 18 := by
    rw [div_le_iff₀ hsR]
    nlinarith [hsα]
  have e4 : ε ^ 2 ≤ ε := by nlinarith
  linarith [e1, e2, e3, e4]

end Union

/-! ### Tests and adversarial examples -/

section Tests

-- G-U1a: the two ordered singleton pieces of the equality relation are perfectly
-- uniform at ANY nonnegative tolerance — every subrectangle has density zero.
example (α : ℝ) (hα : 0 ≤ α) :
    IsUniformPair (fun a b : Fin 2 => a = b) {0} {1} α := by
  have hzero : ∀ X' Y' : Finset (Fin 2), X' ⊆ {0} → Y' ⊆ {1} →
      pairDensity (fun a b : Fin 2 => a = b) X' Y' = 0 := by
    intro X' Y' hX' hY'
    have hcount : pairCount (fun a b : Fin 2 => a = b) X' Y' = 0 := by
      rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq
      rw [Finset.mem_product] at hq
      have hx := Finset.mem_singleton.mp (hX' hq.1)
      have hy := Finset.mem_singleton.mp (hY' hq.2)
      rw [hx, hy]
      decide
    rw [pairDensity_eq_count_div, hcount]
    norm_num
  intro X' hX' Y' hY' _ _
  rw [hzero X' Y' hX' hY', hzero {0} {1} subset_rfl subset_rfl]
  simpa using hα

-- G-U1b: yet their union is NOT `1/4`-uniform with itself (witness `X' = Y' = {0}`:
-- density `1` against `1/2`) — with `s` below the `2/α` threshold, the `1/(s·ε)`
-- diagonal term is REAL and the union lemma's size demand cannot be waived.
example : ¬ IsUniformPair (fun a b : Fin 2 => a = b)
    (Finset.univ : Finset (Fin 2)) Finset.univ (1 / 4 : ℝ) := by
  intro h
  have h3 := h (X' := {0}) (by simp) (Y' := {0}) (by simp)
    (by norm_num [Finset.card_univ]) (by norm_num [Finset.card_univ])
  rw [pairDensity_eq_count_div, pairDensity_eq_count_div] at h3
  norm_num [show pairCount (fun a b : Fin 2 => a = b) {0} {0} = 1 from by decide,
    show pairCount (fun a b : Fin 2 => a = b)
      (Finset.univ : Finset (Fin 2)) Finset.univ = 2 from by decide,
    Finset.card_univ] at h3

-- G-U2: WITHOUT equal cardinality the `1/s` self-term is FALSE. Pieces `{0}` and
-- `{1,2,3}` with `R x y := x ≠ 0 ∧ y ≠ 0`: all ordered piece pairs have density `0`
-- (with perfect uniformity), yet `density(U,U) = 9/16` exceeds `α + 1/2` for
-- `α = 1/32` — a comparability factor is unavoidable if pieces are not trimmed.
example : ¬ (|pairDensity (fun a b : Fin 4 => a ≠ 0 ∧ b ≠ 0)
      Finset.univ Finset.univ - 0| ≤ 1 / 32 + 1 / 2) := by
  rw [pairDensity_eq_count_div]
  norm_num [show pairCount (fun a b : Fin 4 => a ≠ 0 ∧ b ≠ 0)
      Finset.univ Finset.univ = 9 from by decide, Finset.card_univ]

-- G-U3: directed densities are NOT reversal-invariant — the extraction color of the
-- density-bucket unit must record BOTH orientations of each piece pair.
example : pairCount (fun a b : Fin 2 => a = 0 ∧ b = 1) {0} {1} = 1 := by decide

example : pairCount (fun a b : Fin 2 => a = 0 ∧ b = 1) {1} {0} = 0 := by decide

-- **G-U5: the directed self-union composition is FALSE.** The union theorem's `hclose`
-- demands ONE center `d` for EVERY ordered pair; the density-bucket extraction supplies a
-- forward class and a reverse class, and by G-U3 these need not agree. Strict order on
-- `Fin 4` with the four singleton pieces is decisive: the pieces are equal-sized,
-- pairwise disjoint, and PERFECTLY uniform in both directions (below), the forward class
-- is `{1}` and the reverse class is `{0}` — so Ramsey alignment succeeds — yet the union
-- is not `1/4`-uniform with itself, and `isUniformPair_self_union` cannot be instantiated
-- because no `d` is within `α` of both `1` and `0`.
--
-- The obstruction is not a small-host artifact: for `<` on any linearly ordered `W` with
-- `|W| ≥ 2`, `d(W, W) = (|W|-1)/(2|W|) ≤ 1/2` while the lower and upper halves have
-- density `1`, so NO positive-linear-size self-uniform subset exists at tolerance `1/4`.
-- The `Fin 8` instance below records that the gap does not close as the host grows.

/-- Singletons are perfectly uniform: at a positive tolerance the only admissible test
sets are the singletons themselves. -/
private theorem isUniformPair_singleton {W : Type*} [DecidableEq W] {R : W → W → Prop}
    [DecidableRel R] (x y : W) {α : ℝ} (hα : 0 < α) : IsUniformPair R {x} {y} α := by
  intro X' hX' Y' hY' hXc hYc
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hXc hYc
  have hX : X' = {x} := by
    rcases Finset.subset_singleton_iff.mp hX' with rfl | h
    · rw [Finset.card_empty] at hXc
      exact absurd hXc (by push_cast; linarith)
    · exact h
  have hY : Y' = {y} := by
    rcases Finset.subset_singleton_iff.mp hY' with rfl | h
    · rw [Finset.card_empty] at hYc
      exact absurd hYc (by push_cast; linarith)
    · exact h
  rw [hX, hY, sub_self, abs_zero]
  exact hα.le

-- The four singleton pieces are equal-sized, disjoint, and pairwise uniform in BOTH
-- directions at every positive tolerance.
example (α : ℝ) (hα : 0 < α) (i j : Fin 4) :
    IsUniformPair (fun a b : Fin 4 => a < b) {i} {j} α := isUniformPair_singleton i j hα

example (i j : Fin 4) (hij : i ≠ j) : Disjoint ({i} : Finset (Fin 4)) {j} := by
  simpa using hij

example (i : Fin 4) : ({i} : Finset (Fin 4)).card = 1 := Finset.card_singleton i

-- Forward class `1`, reverse class `0`: alignment succeeds, with NO common center.
example : pairDensity (fun a b : Fin 4 => a < b) {0} {1} = 1 := by
  rw [pairDensity_eq_count_div,
    show pairCount (fun a b : Fin 4 => a < b) {0} {1} = 1 from by decide]
  norm_num

example : pairDensity (fun a b : Fin 4 => a < b) {1} {0} = 0 := by
  rw [pairDensity_eq_count_div,
    show pairCount (fun a b : Fin 4 => a < b) {1} {0} = 0 from by decide]
  norm_num

-- No center is within `α < 1/2` of both orientation classes.
example {d α : ℝ} (hα : α < 1 / 2) (h1 : |(1 : ℝ) - d| ≤ α) (h0 : |(0 : ℝ) - d| ≤ α) :
    False := by
  rw [abs_le] at h1 h0
  linarith [h1.1, h1.2, h0.1, h0.2]

-- The pieces do union to the whole host…
example : (Finset.univ.biUnion fun i : Fin 4 => ({i} : Finset (Fin 4))) = Finset.univ := by
  decide

-- …and that union is NOT `1/4`-uniform with itself: the lower and upper halves are
-- `1/4`-large and have density `1` against the host density `6/16 = 3/8`.
example : ¬ IsUniformPair (fun a b : Fin 4 => a < b)
    (Finset.univ : Finset (Fin 4)) Finset.univ (1 / 4 : ℝ) := by
  intro h
  have h3 := h (X' := {0, 1}) (Finset.subset_univ _) (Y' := {2, 3}) (Finset.subset_univ _)
    (by norm_num [Finset.card_univ]) (by norm_num [Finset.card_univ])
  rw [pairDensity_eq_count_div, pairDensity_eq_count_div] at h3
  norm_num [show pairCount (fun a b : Fin 4 => a < b) {0, 1} {2, 3} = 4 from by decide,
    show pairCount (fun a b : Fin 4 => a < b)
      (Finset.univ : Finset (Fin 4)) Finset.univ = 6 from by decide,
    show ({0, 1} : Finset (Fin 4)).card = 2 from by decide,
    show ({2, 3} : Finset (Fin 4)).card = 2 from by decide,
    Finset.card_univ] at h3

-- The same failure on a larger host: `d(univ, univ) = 28/64 = 7/16`, halves at density
-- `1`. Growing the host does not close the gap.
example : ¬ IsUniformPair (fun a b : Fin 8 => a < b)
    (Finset.univ : Finset (Fin 8)) Finset.univ (1 / 4 : ℝ) := by
  intro h
  have h3 := h (X' := {0, 1, 2, 3}) (Finset.subset_univ _) (Y' := {4, 5, 6, 7})
    (Finset.subset_univ _)
    (by norm_num [Finset.card_univ, show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 from by decide])
    (by norm_num [Finset.card_univ, show ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 from by decide])
  rw [pairDensity_eq_count_div, pairDensity_eq_count_div] at h3
  norm_num [show pairCount (fun a b : Fin 8 => a < b) {0, 1, 2, 3} {4, 5, 6, 7} = 16 from
      by decide,
    show pairCount (fun a b : Fin 8 => a < b)
      (Finset.univ : Finset (Fin 8)) Finset.univ = 28 from by decide,
    show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 from by decide,
    show ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 from by decide,
    Finset.card_univ] at h3

-- G-U4: the largeness cutoff is INCLUSIVE — a test set of size exactly `ε·|A|`
-- enters the regularity-controlled case (matching `IsUniformPair`'s inclusive
-- largeness); only strictly smaller test sets are exceptional.
example {V : Type*} [DecidableEq V] {R : V → V → Prop} [DecidableRel R]
    {A B X' Y' : Finset V} {ε : ℝ} (h : IsUniformPair R A B ε)
    (hX' : X' ⊆ A) (hY' : Y' ⊆ B)
    (hx : (X'.card : ℝ) = ε * A.card) (hy : (Y'.card : ℝ) = ε * B.card) :
    |pairDensity R X' Y' - pairDensity R A B| ≤ ε :=
  h hX' hY' (le_of_eq hx.symm) (le_of_eq hy.symm)

end Tests


end RegularityLemmata
