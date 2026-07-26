/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.PieceExtraction
import RegularityLemmata.Graph.EquitableFamilyRegularity

/-!
# Route (b) step 6b: the parameter schedule and the piece-supplier summit

`ARCHITECTURE.md` route (b), supplier checkpoint (2026-07-22): the obligation frozen there
as `PieceSupplierStatement` prose, now proved. Step 6a extracted a piece family from an
equitable family-regular partition with the numerical relations as hypotheses; this file
chooses the parameters, in the only order that is acyclic:

1. `supplierTolerance K t τ = min (τ/2) (1/(64(K+1)t))` — the internal tolerance `ρ`,
   from `(K, t, τ)` **only**. It does not mention the part-count bound, and cannot: the
   bound is defined from it. This is the acyclicity gate G-S1 exists to protect.
2. `supplierParts t = 4t` — the requested part count `l`, a fixed multiple of `t`, which
   is what the independent-set estimate of step 6a needs.
3. `supplierBound K t τ = familyRegularityBound K (supplierTolerance K t τ)
   (supplierParts t)` — the host-independent part-count bound `B`, and only now may it be
   named.
4. `supplierThreshold K t τ = supplierBound K t τ` — the host threshold `N₀`; it is what
   makes the common size `m` positive.
5. `supplierRetention K t τ = t / (2·B)` — the retention floor `κ`; `|A| ≤ 2·n·m ≤ 2·B·m`
   turns it into the mass floor `κ|A| ≤ t·m`.

`exists_pieceFamily` is the summit; `pieceSupplier` restates it in the frozen existential
shape, with `κ` and `N₀` produced before the family and the host are quantified.

**`0 < t` is required and gate G-S2 stays permanent**: with `t = 0` a piece family exists
vacuously while every positive mass floor fails, so the zero-target instance is FALSE
(`Graph/PieceSupplier.lean`).

Provenance: step 1 of the Lemma 3.6 construction of D. Conlon and J. Fox, *Graph removal
lemmas* (arXiv:1211.3487, §3.2), by the **weaker Szemerédi-plus-independent-set route**
the survey mentions — over this repository's own equitable finite-family regularity
engine, not their strong cylinder regularity lemma, so no tower-type bound is claimed.
See `PROVENANCE.md` for the precise scope map.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V]

/-! ### The schedule -/

/-- **The internal tolerance** `ρ`, from `(K, t, τ)` only: half the target tolerance, and
small enough for the independent-set estimate of step 6a. It does NOT mention the
part-count bound — the bound is defined from it, and the reverse dependency is the
circularity route (b) exists to avoid. -/
noncomputable def supplierTolerance (K t : ℕ) (τ : ℝ) : ℝ :=
  min (τ / 2) (1 / (64 * ((K : ℝ) + 1) * (t : ℝ)))

/-- **The requested part count** `l`: a fixed multiple of `t`, the one step 6a's
independent-set estimate consumes. -/
def supplierParts (t : ℕ) : ℕ := 4 * t

/-- **The part-count bound** `B` of the family regularity summit at the internal
tolerance. Host-independent; mentions only `K`, `t`, `τ`. -/
noncomputable def supplierBound (K t : ℕ) (τ : ℝ) : ℕ :=
  familyRegularityBound K (supplierTolerance K t τ) (supplierParts t)

/-- **The host threshold** `N₀`: enough vertices to carry the partition, which is exactly
what makes the common cell size positive. -/
noncomputable def supplierThreshold (K t : ℕ) (τ : ℝ) : ℕ := supplierBound K t τ

/-- **The retention floor** `κ = t/(2B)`: since `|A| ≤ 2·n·m ≤ 2·B·m`, the `t` pieces of
size `m` carry at least a `κ` fraction of the host. -/
noncomputable def supplierRetention (K t : ℕ) (τ : ℝ) : ℝ :=
  (t : ℝ) / (2 * (supplierBound K t τ : ℝ))

/-! ### Properties of the schedule -/

section Schedule

variable {K t : ℕ} {τ : ℝ}

theorem supplierTolerance_le_half_target : supplierTolerance K t τ ≤ τ / 2 :=
  min_le_left _ _

theorem supplierTolerance_le_bound :
    supplierTolerance K t τ ≤ 1 / (64 * ((K : ℝ) + 1) * (t : ℝ)) :=
  min_le_right _ _

theorem supplierTolerance_pos (ht : 0 < t) (hτ : 0 < τ) : 0 < supplierTolerance K t τ := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  refine lt_min (by linarith) ?_
  positivity

/-- The internal tolerance is at most `1/2` — in fact at most `1/64` — so it is a
legitimate input to the family regularity summit, and the slicing hypothesis `ρ ≤ 1/2`
holds with room. -/
theorem supplierTolerance_le_half (ht : 0 < t) : supplierTolerance K t τ ≤ 1 / 2 := by
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  refine le_trans supplierTolerance_le_bound ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem two_mul_supplierTolerance_le : 2 * supplierTolerance K t τ ≤ τ := by
  have := supplierTolerance_le_half_target (K := K) (t := t) (τ := τ)
  linarith

theorem supplierParts_pos (ht : 0 < t) : 0 < supplierParts t := by
  rw [supplierParts]; omega

theorem supplierBound_pos : 0 < supplierBound K t τ := by
  have h2 : 2 ≤ familyInitialBound familyChunkThreshold (supplierTolerance K t τ)
      (supplierParts t) := two_le_familyInitialBound _ _ _
  have := le_familyRegularityBound K (supplierTolerance K t τ) (supplierParts t)
  rw [supplierBound]
  omega

theorem supplierRetention_pos (ht : 0 < t) : 0 < supplierRetention K t τ := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hB : (0 : ℝ) < (supplierBound K t τ : ℝ) := by
    exact_mod_cast supplierBound_pos (K := K) (t := t) (τ := τ)
  rw [supplierRetention]
  positivity

end Schedule

/-! ### The supplier summit -/

/-- **The piece supplier.** For every palette count `K`, target count `t > 0`, and
tolerance `τ > 0`, every host with `supplierThreshold K t τ ≤ |A|` admits a common size
`m > 0` and `t` pairwise-disjoint pieces of size exactly `m`, every ordered pair of
distinct pieces `τ`-uniform for every relation of the family, carrying at least a
`supplierRetention K t τ` fraction of the host.

The retention floor and the threshold depend on `(K, t, τ)` only — they are fixed before
any partition is produced, and `supplierTolerance` does not mention the part-count bound.
This is the obligation frozen at the 2026-07-22 supplier checkpoint. -/
theorem exists_pieceFamily {K t : ℕ} (ht : 0 < t) {τ : ℝ} (hτ : 0 < τ)
    (Rk : Fin K → V → V → Prop) [∀ k, DecidableRel (Rk k)] (A : Finset V)
    (hA : supplierThreshold K t τ ≤ A.card) :
    ∃ m : ℕ, 0 < m ∧ ∃ Pc : Fin t → Finset V,
      IsPieceFamily Rk A τ m Pc
        ∧ supplierRetention K t τ * (A.card : ℝ) ≤ (t : ℝ) * (m : ℝ) := by
  classical
  set ρ := supplierTolerance K t τ with hρdef
  have hρ0 : 0 < ρ := supplierTolerance_pos ht hτ
  have hρhalf : ρ ≤ 1 / 2 := supplierTolerance_le_half ht
  -- The family regularity summit at the internal tolerance.
  obtain ⟨P, hPeq, hPreg, hPl, hPB⟩ :=
    exists_familyRegular_equipartition (s := A) Rk hρ0 (by linarith) (supplierParts t)
      (by rw [← supplierBound]; exact le_trans (le_of_eq rfl) hA)
  have hnpos : 0 < P.parts.card := by
    have := supplierParts_pos (t := t) ht
    omega
  -- The host threshold is exactly what makes the common size positive.
  have hBn : P.parts.card ≤ supplierBound K t τ := by rw [supplierBound]; exact hPB
  have hm : 0 < A.card / P.parts.card := by
    refine Nat.one_le_div_iff hnpos |>.mpr ?_
    exact le_trans hBn (le_trans (le_of_eq rfl) hA)
  refine ⟨A.card / P.parts.card, hm, ?_⟩
  obtain ⟨Pc, hPc⟩ := exists_pieceFamily_of_familyRegular hPeq hm hPreg ht hρ0 hρhalf
    two_mul_supplierTolerance_le supplierTolerance_le_bound
    (by rw [← supplierParts]; exact hPl)
  refine ⟨Pc, hPc, ?_⟩
  -- The mass floor: `|A| ≤ 2·n·m ≤ 2·B·m`.
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hBR : (0 : ℝ) < (supplierBound K t τ : ℝ) := by exact_mod_cast supplierBound_pos
  have hA2 := card_le_two_mul_card_parts_mul hPeq hm
  have hnB : ((P.parts.card : ℕ) : ℝ) ≤ ((supplierBound K t τ : ℕ) : ℝ) := by
    exact_mod_cast hBn
  have hmR : (0 : ℝ) ≤ ((A.card / P.parts.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hAB : (A.card : ℝ)
      ≤ 2 * (supplierBound K t τ : ℝ) * ((A.card / P.parts.card : ℕ) : ℝ) := by
    refine le_trans hA2 ?_
    have := mul_le_mul_of_nonneg_right hnB hmR
    nlinarith
  rw [supplierRetention, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The frozen existential shape** of the supplier obligation: the retention floor and
the host threshold are produced from `(K, t, τ)` BEFORE the family and the host are
quantified. -/
theorem pieceSupplier (K t : ℕ) (ht : 0 < t) (τ : ℝ) (hτ : 0 < τ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ,
      ∀ (Rk : Fin K → V → V → Prop) [∀ k, DecidableRel (Rk k)] (A : Finset V),
        N₀ ≤ A.card →
          ∃ m : ℕ, 0 < m ∧ ∃ Pc : Fin t → Finset V,
            IsPieceFamily Rk A τ m Pc ∧ κ * (A.card : ℝ) ≤ (t : ℝ) * (m : ℝ) :=
  ⟨supplierRetention K t τ, supplierRetention_pos ht, supplierThreshold K t τ,
    fun Rk _ A hA => exists_pieceFamily ht hτ Rk A hA⟩

/-! ### Tests and adversarial examples -/

section Tests

-- **Acyclicity, definitionally.** The internal tolerance mentions only `K`, `t`, `τ` —
-- never the part-count bound, which is defined FROM it. This is a permanent guard on the
-- direction of the dependency.
example (K t : ℕ) (τ : ℝ) :
    supplierTolerance K t τ = min (τ / 2) (1 / (64 * ((K : ℝ) + 1) * (t : ℝ))) := rfl

example (K t : ℕ) (τ : ℝ) :
    supplierBound K t τ
      = familyRegularityBound K (supplierTolerance K t τ) (supplierParts t) := rfl

-- The tolerance is genuinely below the target and below `1/2`, with room.
example (t : ℕ) (ht : 0 < t) (τ : ℝ) (hτ : 0 < τ) {K : ℕ} :
    0 < supplierTolerance K t τ ∧ 2 * supplierTolerance K t τ ≤ τ
      ∧ supplierTolerance K t τ ≤ 1 / 2 :=
  ⟨supplierTolerance_pos ht hτ, two_mul_supplierTolerance_le,
    supplierTolerance_le_half ht⟩

-- **Positivity of `m` comes from `N₀`**: the threshold is the part-count bound, so a host
-- meeting it has at least one vertex per cell. Below the threshold nothing is claimed.
example (K t : ℕ) (τ : ℝ) : supplierThreshold K t τ = supplierBound K t τ := rfl

example (K t : ℕ) (τ : ℝ) : 0 < supplierThreshold K t τ := supplierBound_pos

-- **The `K = 0` endpoint.** With no relations the uniformity clause is vacuous, but the
-- supplier still delivers `t` disjoint equal-size pieces with the mass floor — the
-- schedule degenerates rather than breaking.
example (t : ℕ) (ht : 0 < t) (τ : ℝ) (hτ : 0 < τ) (A : Finset (Fin 3))
    (hA : supplierThreshold 0 t τ ≤ A.card) :
    ∃ m : ℕ, 0 < m ∧ ∃ Pc : Fin t → Finset (Fin 3),
      IsPieceFamily (fun _ : Fin 0 => fun _ _ : Fin 3 => True) A τ m Pc
        ∧ supplierRetention 0 t τ * (A.card : ℝ) ≤ (t : ℝ) * (m : ℝ) :=
  exists_pieceFamily ht hτ _ A hA

-- **Gate G-S2 stays live**: `0 < t` is not decoration. With `t = 0` the mass floor
-- `κ·|A| ≤ t·m = 0` is unsatisfiable on a nonempty host for any positive `κ`, which is
-- why the summit demands `0 < t` (the vacuous piece family at `t = 0` is exhibited in
-- `Graph/PieceSupplier.lean`).
example (κ : ℝ) (hκ : 0 < κ) (m : ℕ) :
    ¬ (κ * (((Finset.univ : Finset (Fin 3)).card : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) * (m : ℝ)) := by
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, Nat.cast_zero, zero_mul,
    not_le]
  positivity

-- The pieces of a supplied family have EXACTLY the common size, in both orientations of
-- every relation — the two clauses the extraction was built to deliver.
example {K t m : ℕ} (Rk : Fin K → Fin 3 → Fin 3 → Prop) [∀ k, DecidableRel (Rk k)]
    (A : Finset (Fin 3)) (τ : ℝ) (Pc : Fin t → Finset (Fin 3))
    (h : IsPieceFamily Rk A τ m Pc) (i j : Fin t) (hij : i ≠ j) (k : Fin K) :
    (Pc i).card = m ∧ (Pc j).card = m
      ∧ IsUniformPair (Rk k) (Pc i) (Pc j) τ ∧ IsUniformPair (Rk k) (Pc j) (Pc i) τ :=
  ⟨h.2.2.1 i, h.2.2.1 j, h.2.2.2 k i j hij, h.2.2.2 k j i hij.symm⟩

end Tests

end RegularityLemmata
