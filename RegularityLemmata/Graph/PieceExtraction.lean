/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.PieceSupplier
import RegularityLemmata.Graph.UniformSlicing
import RegularityLemmata.Graph.FamilyRegularity
import RegularityLemmata.Partition.Equitable

/-!
# Route (b) step 6a: extraction of a piece family from an equitable regular partition

`ARCHITECTURE.md` route (b), supplier checkpoint (2026-07-22) and supplier route decision:
the extraction half of the piece supplier. Given an EQUITABLE partition that is
`ρ`-regular for every relation of a finite directed family, this file produces
`IsPieceFamily`. No schedule constant is chosen here: `ρ`, `t`, and the required part
count enter as hypotheses, and the numerical relations among them are exactly the ones the
proof consumes.

The order is the one gate **G-S1** forces:

1. **Weighted mass to unweighted count** (`card_le_of_forall_isBadPair`): on an
   equipartition, every cell has `m ≤ |C| ≤ m + 1 ≤ 2m`, so a set of bad ordered pairs
   has `|F|·m² ≤ badMassNum ≤ ρ·|A|² ≤ 4ρ·n²·m²`, giving `|F| ≤ 4ρn²` — the conversion
   G-S1 shows is FALSE without equal sizes.
2. **Summed symmetrized bad degree** (`sum_card_badNbhd_le`): both orientations and all
   `K` relations, so `∑_C |badNbhd C| ≤ 8Kρn²` — the `2K` factor
   `Finite/IndependentSet.lean` documents.
3. **Independent-set corollary** (`exists_clean_cells`): with `ρ ≤ 1/(64(K+1)t)` and
   `4t ≤ n`, the degree budget `D + 1 = n/(2t)` satisfies the Markov hypothesis and
   `2(D+1)t ≤ n`, so the extraction returns at least `t` pairwise-clean cells. The
   constant `64(K+1)t` is DERIVED here, not posited: it is what makes `16Kρn ≤ n/(4t)`.
4. **Trimming and slicing** (`exists_pieceFamily_of_familyRegular`): each selected cell is
   trimmed to exactly `m`, a retention of at least `1/2` since `|C| ≤ 2m`, and
   `IsUniformPair.slice` transports `ρ`-uniformity to `τ`-uniformity whenever `2ρ ≤ τ`
   and `ρ ≤ 1/2`.

Nothing here mentions a part-count bound, so no tolerance can depend on the produced
number of parts.

Provenance: this is step 1 of the Lemma 3.6 construction of D. Conlon and J. Fox,
*Graph removal lemmas* (arXiv:1211.3487, §3.2), taken by the **weaker
Szemerédi-plus-independent-set route** the survey mentions rather than by their strong
cylinder regularity lemma — so no tower-type bound is claimed. See `PROVENANCE.md` for the
precise scope map.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {K : ℕ} {Rk : Fin K → V → V → Prop}
  [∀ k, DecidableRel (Rk k)] {ρ τ : ℝ} {A : Finset V} {P : Finpartition A}

/-! ### The family bad-pair predicate -/

/-- A pair of cells is family-bad when some relation of the family is nonuniform on it.
Cleanliness for this predicate is exactly what the piece family needs, in both
orientations (the symmetrization happens once, in `badNbhd`). -/
def IsFamilyBadPair (Rk : Fin K → V → V → Prop) [∀ k, DecidableRel (Rk k)] (ρ : ℝ)
    (C D : Finset V) : Prop :=
  ∃ k, IsBadPair (Rk k) ρ C D

omit [DecidableEq V] in
theorem isUniformPair_of_not_isFamilyBadPair {C D : Finset V} (hCD : C ≠ D)
    (h : ¬ IsFamilyBadPair Rk ρ C D) (k : Fin K) : IsUniformPair (Rk k) C D ρ := by
  by_contra hcon
  exact h ⟨k, hCD, hcon⟩

/-! ### Step 1: weighted mass to unweighted count -/

/-- Cells of an equipartition are sandwiched: `m ≤ |C| ≤ m + 1`. -/
theorem card_part_bounds (hP : P.IsEquipartition) {C : Finset V} (hC : C ∈ P.parts) :
    A.card / P.parts.card ≤ C.card ∧ C.card ≤ A.card / P.parts.card + 1 :=
  ⟨hP.average_le_card_part hC, hP.card_part_le_average_add_one hC⟩

/-- The host is at most `2·n·m`: `n` cells of size at most `m + 1 ≤ 2m`. -/
theorem card_le_two_mul_card_parts_mul (hP : P.IsEquipartition)
    (hm : 0 < A.card / P.parts.card) :
    (A.card : ℝ) ≤ 2 * (P.parts.card : ℝ) * ((A.card / P.parts.card : ℕ) : ℝ) := by
  have hsum : ∑ C ∈ P.parts, C.card = A.card := P.sum_card_parts
  have hle : ∑ C ∈ P.parts, C.card
      ≤ ∑ _C ∈ P.parts, (A.card / P.parts.card + 1) :=
    Finset.sum_le_sum fun C hC => (card_part_bounds hP hC).2
  rw [hsum, Finset.sum_const, smul_eq_mul] at hle
  have hcast : (A.card : ℝ)
      ≤ (P.parts.card : ℝ) * (((A.card / P.parts.card : ℕ) : ℝ) + 1) := by
    exact_mod_cast hle
  have h1 : (1 : ℝ) ≤ ((A.card / P.parts.card : ℕ) : ℝ) := by exact_mod_cast hm
  nlinarith [Nat.cast_nonneg (α := ℝ) P.parts.card]

/-- **The weighted-to-unweighted bad-pair bound** (the conversion gate G-S1 rules out
without equal sizes). Any set of ordered bad pairs of cells has at most `4ρn²` elements:
each contributes at least `m²` to the bad mass, which is at most `ρ|A|² ≤ 4ρn²m²`. -/
theorem card_le_of_forall_isBadPair (hP : P.IsEquipartition)
    (hm : 0 < A.card / P.parts.card) (k : Fin K) (hreg : IsRegularPartition (Rk k) ρ P)
    (F : Finset (Finset V × Finset V)) (hFsub : F ⊆ P.parts ×ˢ P.parts)
    (hFbad : ∀ p ∈ F, IsBadPair (Rk k) ρ p.1 p.2) :
    (F.card : ℝ) ≤ 4 * ρ * (P.parts.card : ℝ) ^ 2 := by
  classical
  set m := A.card / P.parts.card with hmdef
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    have : 0 < A.card := Nat.lt_of_lt_of_le hm (Nat.div_le_self _ _)
    exact_mod_cast this
  -- The regularity hypothesis, cleared of its denominator.
  have hbm : badMassNum (Rk k) ρ P ≤ ρ * (A.card : ℝ) ^ 2 := by
    have hsq : (0 : ℝ) < (A.card : ℝ) ^ 2 := by positivity
    have h := hreg
    rw [IsRegularPartition, badMass, div_le_iff₀ hsq] at h
    linarith
  -- Every bad pair carries at least `m²` of bad mass.
  have hFsubfilter : F ⊆ (P.parts ×ˢ P.parts).filter
      (fun uv => IsBadPair (Rk k) ρ uv.1 uv.2) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hFsub hp, hFbad p hp⟩
  have hlow : (F.card : ℝ) * (m : ℝ) ^ 2 ≤ badMassNum (Rk k) ρ P := by
    rw [badMassNum]
    calc (F.card : ℝ) * (m : ℝ) ^ 2 = ∑ _p ∈ F, (m : ℝ) * (m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ p ∈ F, (p.1.card : ℝ) * (p.2.card : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp (hFsub hp)
          exact mul_le_mul (by exact_mod_cast (card_part_bounds hP h1).1)
            (by exact_mod_cast (card_part_bounds hP h2).1) hmpos.le
            (Nat.cast_nonneg _)
      _ ≤ ∑ p ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair (Rk k) ρ uv.1 uv.2),
            (p.1.card : ℝ) * (p.2.card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hFsubfilter
            (fun p _ _ => by positivity)
  -- The host bound turns `ρ|A|²` into `4ρn²m²`.
  have hA2 := card_le_two_mul_card_parts_mul hP hm
  have hρ0 : 0 ≤ ρ := by
    by_contra hcon
    push Not at hcon
    have h0 : (0 : ℝ) ≤ badMassNum (Rk k) ρ P := badMassNum_nonneg _ _
    have hneg : ρ * (A.card : ℝ) ^ 2 < 0 := mul_neg_of_neg_of_pos hcon (by positivity)
    linarith
  have hkey : (F.card : ℝ) * (m : ℝ) ^ 2
      ≤ 4 * ρ * (P.parts.card : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
    have hsq : (A.card : ℝ) ^ 2 ≤ (2 * (P.parts.card : ℝ) * (m : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (A.card : ℝ) := hApos.le
      nlinarith
    nlinarith
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_right (by linarith) hm2

/-! ### Step 2: the summed symmetrized bad degree -/

open scoped Classical in
/-- **The summed symmetrized bad degree**: both orientations and all `K` relations, so the
per-relation count `4ρn²` becomes `8Kρn²`. -/
theorem sum_card_badNbhd_le (hP : P.IsEquipartition) (hm : 0 < A.card / P.parts.card)
    (hreg : IsFamilyRegular Rk ρ P) :
    ((∑ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card : ℕ) : ℝ)
      ≤ 8 * (K : ℝ) * ρ * (P.parts.card : ℝ) ^ 2 := by
  classical
  -- One relation, one orientation.
  have hone : ∀ k : Fin K, ∀ f : Finset V → Finset V → Prop,
      (∀ C D, f C D → IsBadPair (Rk k) ρ C D) →
      ((∑ C ∈ P.parts, (P.parts.filter (fun D => f C D)).card : ℕ) : ℝ)
        ≤ 4 * ρ * (P.parts.card : ℝ) ^ 2 := by
    intro k f hf
    have hcount : (∑ C ∈ P.parts, (P.parts.filter (fun D => f C D)).card)
        = ((P.parts ×ˢ P.parts).filter (fun p => f p.1 p.2)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun C _ => Finset.card_filter _ _
    rw [hcount]
    refine card_le_of_forall_isBadPair hP hm k (hreg k) _ (Finset.filter_subset _ _) ?_
    intro p hp
    exact hf p.1 p.2 (Finset.mem_filter.mp hp).2
  -- The transposed orientation has the same count.
  have hswap : ∀ k : Fin K,
      ((∑ C ∈ P.parts, (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card : ℕ) : ℝ)
        ≤ 4 * ρ * (P.parts.card : ℝ) ^ 2 := by
    intro k
    have hcomm : (∑ C ∈ P.parts, (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card)
        = ∑ C ∈ P.parts, (P.parts.filter (fun D => IsBadPair (Rk k) ρ C D)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hcomm]
    exact hone k (fun C D => IsBadPair (Rk k) ρ C D) (fun _ _ h => h)
  -- Each symmetrized neighborhood is covered by the `2K` one-directional ones.
  have hcover : ∀ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card
      ≤ ∑ k : Fin K, ((P.parts.filter (fun D => IsBadPair (Rk k) ρ C D)).card
          + (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card) := by
    intro C _
    have hpt : ∀ D ∈ P.parts,
        (if IsFamilyBadPair Rk ρ C D ∨ IsFamilyBadPair Rk ρ D C then 1 else 0)
          ≤ ∑ k : Fin K, ((if IsBadPair (Rk k) ρ C D then 1 else 0)
              + (if IsBadPair (Rk k) ρ D C then 1 else 0)) := by
      intro D _
      split_ifs with hbad
      · obtain ⟨k, hk⟩ | ⟨k, hk⟩ := hbad
        · refine le_trans ?_ (Finset.single_le_sum
            (f := fun k : Fin K => (if IsBadPair (Rk k) ρ C D then 1 else 0)
              + (if IsBadPair (Rk k) ρ D C then 1 else 0))
            (fun j _ => Nat.zero_le _) (Finset.mem_univ k))
          rw [ite_eq_left hk]
          omega
        · refine le_trans ?_ (Finset.single_le_sum
            (f := fun k : Fin K => (if IsBadPair (Rk k) ρ C D then 1 else 0)
              + (if IsBadPair (Rk k) ρ D C then 1 else 0))
            (fun j _ => Nat.zero_le _) (Finset.mem_univ k))
          rw [ite_eq_left hk]
          omega
      · exact Nat.zero_le _
    calc (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card
        = ∑ D ∈ P.parts,
            (if IsFamilyBadPair Rk ρ C D ∨ IsFamilyBadPair Rk ρ D C then 1 else 0) := by
          rw [badNbhd, Finset.card_filter]
      _ ≤ ∑ D ∈ P.parts, ∑ k : Fin K, ((if IsBadPair (Rk k) ρ C D then 1 else 0)
            + (if IsBadPair (Rk k) ρ D C then 1 else 0)) := Finset.sum_le_sum hpt
      _ = ∑ k : Fin K, ((P.parts.filter (fun D => IsBadPair (Rk k) ρ C D)).card
            + (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter]
  -- Sum and add up the `2K` contributions.
  have hstep : (∑ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card)
      ≤ ∑ k : Fin K, ((∑ C ∈ P.parts, (P.parts.filter (fun D => IsBadPair (Rk k) ρ C D)).card)
          + ∑ C ∈ P.parts, (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card) := by
    refine le_trans (Finset.sum_le_sum hcover) ?_
    rw [Finset.sum_comm]
    exact le_of_eq (Finset.sum_congr rfl fun k _ => by rw [Finset.sum_add_distrib])
  have hcast : ((∑ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card : ℕ) : ℝ)
      ≤ ∑ k : Fin K, (((∑ C ∈ P.parts,
            (P.parts.filter (fun D => IsBadPair (Rk k) ρ C D)).card : ℕ) : ℝ)
          + ((∑ C ∈ P.parts,
            (P.parts.filter (fun D => IsBadPair (Rk k) ρ D C)).card : ℕ) : ℝ)) := by
    push_cast
    exact_mod_cast hstep
  refine le_trans hcast ?_
  refine le_trans (Finset.sum_le_sum fun k _ =>
    add_le_add (hone k (fun C D => IsBadPair (Rk k) ρ C D) (fun _ _ h => h)) (hswap k)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-! ### Step 3: the independent-set corollary -/

open scoped Classical in
/-- **At least `t` pairwise-clean cells.** With `ρ ≤ 1/(64(K+1)t)` and `4t ≤ n` the degree
budget `D + 1 = n/(2t)` meets the Markov hypothesis of `exists_clean_subset` and satisfies
`2(D+1)t ≤ n`, so the extraction returns at least `t` cells, no two of which are
family-bad.

The constant `64(K+1)t` is DERIVED, not posited: it is exactly what makes
`16Kρn ≤ n/(4t) ≤ n/(2t)`, and `4t ≤ n` is what makes the natural-number division
`n/(2t)` lose at most half. -/
theorem exists_clean_cells (hP : P.IsEquipartition) (hm : 0 < A.card / P.parts.card)
    (hreg : IsFamilyRegular Rk ρ P) {t : ℕ} (ht : 0 < t)
    (hρK : ρ ≤ 1 / (64 * ((K : ℝ) + 1) * (t : ℝ))) (hl : 4 * t ≤ P.parts.card) :
    ∃ T ⊆ P.parts, t ≤ T.card ∧
      ∀ C ∈ T, ∀ D ∈ T, C ≠ D → ¬ IsFamilyBadPair Rk ρ C D := by
  classical
  set n := P.parts.card with hn
  set q := n / (2 * t) with hq
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h4t : (4 : ℝ) * (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2tn : 2 * t ≤ n := by omega
  have hq1 : 1 ≤ q := Nat.one_le_div_iff (by omega) |>.mpr h2tn
  -- `q` loses at most half of `n/(2t)`.
  have hqreal : (n : ℝ) / (4 * (t : ℝ)) ≤ (q : ℝ) := by
    have hlt : n < q * (2 * t) + 2 * t := Nat.lt_div_mul_add (by omega)
    have hcast : (n : ℝ) < (q : ℝ) * (2 * (t : ℝ)) + 2 * (t : ℝ) := by exact_mod_cast hlt
    rw [div_le_iff₀ (by positivity)]
    have hring : (q : ℝ) * (4 * (t : ℝ)) = 2 * ((q : ℝ) * (2 * (t : ℝ))) := by ring
    linarith
  -- The chunk of the derivation that fixes the constant `64(K+1)t`.
  have hKq : 16 * (K : ℝ) * ρ * (n : ℝ) ≤ (q : ℝ) := by
    have h1 : ρ * (16 * (K : ℝ) * (n : ℝ))
        ≤ 1 / (64 * ((K : ℝ) + 1) * (t : ℝ)) * (16 * (K : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hρK (by positivity)
    have h2 : 1 / (64 * ((K : ℝ) + 1) * (t : ℝ)) * (16 * (K : ℝ) * (n : ℝ))
        ≤ (n : ℝ) / (4 * (t : ℝ)) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      have hrw : (n : ℝ) / (4 * (t : ℝ)) * (64 * ((K : ℝ) + 1) * (t : ℝ))
          = 16 * (n : ℝ) * ((K : ℝ) + 1) := by
        field_simp
        ring
      rw [hrw]
      nlinarith [Nat.cast_nonneg (α := ℝ) K, hnpos]
    nlinarith [h1, h2, hqreal]
  -- The Markov hypothesis of the greedy extraction.
  have hsum := sum_card_badNbhd_le hP hm hreg
  rw [← hn] at hsum
  have hE : 2 * ∑ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card ≤ n * q := by
    have hstep : 8 * (K : ℝ) * ρ * (n : ℝ) ^ 2 * 2 ≤ (n : ℝ) * (q : ℝ) := by
      nlinarith [hKq, hnpos]
    have hreal : ((2 * ∑ C ∈ P.parts,
        (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by
      push_cast
      push_cast at hsum
      linarith
    exact_mod_cast hreal
  obtain ⟨T, hTsub, hTcard, hTclean⟩ :=
    exists_clean_subset (IsFamilyBadPair Rk ρ) P.parts (D := q - 1)
      (E := ∑ C ∈ P.parts, (badNbhd (IsFamilyBadPair Rk ρ) P.parts C).card) le_rfl
      (by rwa [Nat.sub_add_cancel hq1])
  refine ⟨T, hTsub, ?_, hTclean⟩
  rw [Nat.sub_add_cancel hq1] at hTcard
  -- `2qt ≤ n ≤ 2q·|T|` forces `t ≤ |T|`.
  have hqt : 2 * q * t ≤ n := by
    have := Nat.div_mul_le_self n (2 * t)
    calc 2 * q * t = q * (2 * t) := by ring
      _ ≤ n := this
  have : 2 * q * t ≤ 2 * q * T.card := le_trans hqt hTcard
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-! ### Step 4: trimming, slicing, and the piece family -/

/-- **The extraction summit.** An equitable partition that is `ρ`-regular for every
relation of the family, with at least `4t` cells and a positive common size `m`, yields
`t` pieces of size EXACTLY `m` that are pairwise `τ`-uniform for every relation, provided
`2ρ ≤ τ` and `ρ ≤ 1/2`.

The trimming is what makes the sizes exactly equal; the retention is at least `1/2`
because `|C| ≤ m + 1 ≤ 2m`, and `IsUniformPair.slice` at that retention costs exactly the
factor `2` in the tolerance. No schedule constant appears: `ρ`, `t`, and the part-count
requirement are hypotheses. -/
theorem exists_pieceFamily_of_familyRegular (hP : P.IsEquipartition)
    (hm : 0 < A.card / P.parts.card) (hreg : IsFamilyRegular Rk ρ P)
    {t : ℕ} (ht : 0 < t) (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (hρτ : 2 * ρ ≤ τ)
    (hρK : ρ ≤ 1 / (64 * ((K : ℝ) + 1) * (t : ℝ))) (hl : 4 * t ≤ P.parts.card) :
    ∃ Pc : Fin t → Finset V, IsPieceFamily Rk A τ (A.card / P.parts.card) Pc := by
  classical
  obtain ⟨T, hTsub, hTcard, hTclean⟩ := exists_clean_cells hP hm hreg ht hρK hl
  obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq hTcard
  -- Index `t` of the clean cells.
  let e : {x // x ∈ T'} ≃ Fin t := (Finset.equivFin T').trans (finCongr hT'card)
  set f : Fin t → Finset V := fun i => (e.symm i : Finset V) with hf
  have hfT : ∀ i, f i ∈ T := fun i => hT'sub (e.symm i).2
  have hfparts : ∀ i, f i ∈ P.parts := fun i => hTsub (hfT i)
  have hfinj : Function.Injective f := fun i j hij => e.symm.injective (Subtype.ext hij)
  -- Trim each selected cell to exactly `m`.
  have hsize : ∀ i, A.card / P.parts.card ≤ (f i).card := fun i =>
    (card_part_bounds hP (hfparts i)).1
  choose W hWsub hWcard using fun i : Fin t => Finset.exists_subset_card_eq (hsize i)
  have hmR : (0 : ℝ) < ((A.card / P.parts.card : ℕ) : ℝ) := by exact_mod_cast hm
  -- The retention is at least `1/2`, since `|C| ≤ m + 1 ≤ 2m`.
  have hretain : ∀ i, 1 / 2 * ((f i).card : ℝ) ≤ ((W i).card : ℝ) := by
    intro i
    have hub : ((f i).card : ℝ) ≤ ((A.card / P.parts.card : ℕ) : ℝ) + 1 := by
      exact_mod_cast (card_part_bounds hP (hfparts i)).2
    rw [hWcard i]
    have h1 : (1 : ℝ) ≤ ((A.card / P.parts.card : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  refine ⟨W, fun i => (hWsub i).trans (P.le (hfparts i)), ?_, hWcard, ?_⟩
  · intro i j hij
    exact Finset.disjoint_of_subset_left (hWsub i)
      (Finset.disjoint_of_subset_right (hWsub j)
        (P.disjoint (hfparts i) (hfparts j) (fun h => hij (hfinj h))))
  · intro k i j hij
    have hne : f i ≠ f j := fun h => hij (hfinj h)
    have huni : IsUniformPair (Rk k) (f i) (f j) ρ :=
      isUniformPair_of_not_isFamilyBadPair hne
        (hTclean _ (hfT i) _ (hfT j) hne) k
    exact huni.slice hρ0.le (hWsub i) (hWsub j) hρhalf hρhalf (hretain i) (hretain j)
      (by linarith) (by linarith) hρτ

/-! ### Tests and adversarial examples -/

section Tests

-- The equipartition sandwich on a concrete host: the discrete partition of a
-- four-element host has `m = 1` and every cell of size exactly `m`.
example : ∀ C ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin 4))).parts,
    (Finset.univ : Finset (Fin 4)).card / (⊥ : Finpartition
        (Finset.univ : Finset (Fin 4))).parts.card ≤ C.card ∧
      C.card ≤ (Finset.univ : Finset (Fin 4)).card / (⊥ : Finpartition
        (Finset.univ : Finset (Fin 4))).parts.card + 1 :=
  fun _ hC => card_part_bounds (Finpartition.bot_isEquipartition _) hC

-- **Exact `m`, not `m` or `m + 1`**: a piece family's pieces all have the SAME size,
-- which is what the trimming buys and what the mass floor is stated against.
example {t m : ℕ} (Rk : Fin 1 → Fin 3 → Fin 3 → Prop) [∀ k, DecidableRel (Rk k)]
    (A : Finset (Fin 3)) (τ : ℝ) (Pc : Fin t → Finset (Fin 3))
    (h : IsPieceFamily Rk A τ m Pc) (i j : Fin t) : (Pc i).card = (Pc j).card := by
  rw [h.2.2.1 i, h.2.2.1 j]

-- **Both orientations** for a possibly ASYMMETRIC relation: `IsPieceFamily` quantifies
-- ORDERED pairs, so `(i, j)` and `(j, i)` are both uniform.
example {m : ℕ} (Rk : Fin 1 → Fin 3 → Fin 3 → Prop) [∀ k, DecidableRel (Rk k)]
    (A : Finset (Fin 3)) (τ : ℝ) (Pc : Fin 2 → Finset (Fin 3))
    (h : IsPieceFamily Rk A τ m Pc) :
    IsUniformPair (Rk 0) (Pc 0) (Pc 1) τ ∧ IsUniformPair (Rk 0) (Pc 1) (Pc 0) τ :=
  ⟨h.2.2.2 0 0 1 (by decide), h.2.2.2 0 1 0 (by decide)⟩

-- **Concrete `m + 1 → m` trimming.** A five-element host split as `{0,1}` and `{2,3,4}`
-- is an equipartition whose common size is `m = 5/2 = 2`, and whose second cell is
-- genuinely OVERSIZED at `m + 1 = 3`. This is the case the trimming exists for.
example :
    (twoPartition ({0, 1, 2, 3, 4} : Finset (Fin 5)) {0, 1} (by decide) (by decide)
      (by decide)).IsEquipartition := by
  refine Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨2, fun u hu => ?_⟩
  rw [Finset.mem_coe, twoPartition_parts] at hu
  revert hu
  revert u
  decide

example :
    ({0, 1, 2, 3, 4} : Finset (Fin 5)).card
        / (twoPartition ({0, 1, 2, 3, 4} : Finset (Fin 5)) {0, 1} (by decide) (by decide)
          (by decide)).parts.card = 2 := by
  rw [twoPartition_card]
  decide

-- The oversized cell is a genuine `m + 1`, and the sandwich `m ≤ |C| ≤ m + 1` is tight
-- on it.
example : ({2, 3, 4} : Finset (Fin 5)).card = 2 + 1 := by decide

-- Trimming it to `{2,3}` restores the EXACT common size `m`, and the retention
-- `1/2 · |C| ≤ |W|` — the hypothesis `IsUniformPair.slice` consumes at retention `1/2` —
-- holds with the oversized cell, which is the only case where it is not trivial.
example :
    ∃ W ⊆ ({2, 3, 4} : Finset (Fin 5)), W.card = 2 ∧
      (1 : ℝ) / 2 * ((({2, 3, 4} : Finset (Fin 5)).card : ℕ) : ℝ) ≤ ((W.card : ℕ) : ℝ) := by
  refine ⟨{2, 3}, by decide, by decide, ?_⟩
  have h1 : ({2, 3, 4} : Finset (Fin 5)).card = 3 := by decide
  have h2 : ({2, 3} : Finset (Fin 5)).card = 2 := by decide
  rw [h1, h2]
  norm_num

-- The `K = 0` endpoint: the empty family is regular at every tolerance, so the extraction
-- hypothesis is free and the tolerance bound reads `ρ ≤ 1/(64t)`.
example (P : Finpartition (Finset.univ : Finset (Fin 8))) (ρ : ℝ) :
    IsFamilyRegular (fun _ : Fin 0 => fun _ _ : Fin 8 => True) ρ P :=
  isFamilyRegular_zero _

example (t : ℕ) : 1 / (64 * ((0 : ℕ) + 1 : ℝ) * (t : ℝ)) = 1 / (64 * (t : ℝ)) := by
  norm_num

end Tests

end RegularityLemmata
