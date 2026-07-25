/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.EquitableChunk
import RegularityLemmata.Graph.Increment

/-!
# Equitable-supplier ladder, step 3 (approximation)

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence step 3,
**approximation half**: how much of a nonuniformity witness the chunks of
`equitableIncrement` recover, and the resulting block-energy increment with its loss made
explicit. The construction half (`Graph/EquitableChunk.lean`) established the exact
combinatorics first; nothing here revisits part counts or part sizes.

**Two layers, named separately.** `witnessAtoms R ε P C` is the *certifying* layer: the
atomisation of the parent cell `C` by its own witness cuts, in which every chosen witness
side is exactly a union of atoms (`biUnion_witnessAtoms_of_mem_witnessCuts`). The chunks
of `equitableIncrement` are the *produced* layer; they do **not** refine the atoms. The
bridge between the layers is one-directional and quantitative: each atom loses at most one
chunk's worth of elements (`card_sdiff_innerPartUnion_atom_le`), so a witness side — a
union of at most `2 ^ (2·#P.parts)` atoms — loses at most
`chunkWitnessRemainder P = 2 ^ (2·#P.parts) · chunkSize P` elements
(`card_sdiff_innerPartUnion_le`).

The order of the development is the reviewed one: exact remainder calculus first, density
estimates only afterwards.

1. `filter_subset_equitableIncrement` — the global chunks contained in a parent cell are
   exactly that parent's local chunks; `filter_subset_equitableIncrement_of_subset` says
   the same after filtering by any subset of the parent. These keep the dependent-proof
   bookkeeping of `Finpartition.bind` out of every later sum.
2. Per-atom remainder ≤ `chunkSize P`; a witness side is a union of its atoms; at most
   `2 ^ (2·#P.parts)` atoms contribute; hence the witness-side remainder bound. Then
   `chunkWitnessRemainder_mul_pow_le_card_part`: the remainder is smaller than every
   parent cell by the whole equitabilisation factor `4^(n·2^(2n))` — the exact
   structural inequality that discharges the gain theorem's numerical hypotheses.
3. `innerPartUnion Q W` (`Partition/Basic.lean`) is the recovered side: the union of the
   chunks contained in `W`. It is a part union of `Q` by construction, so it can be fed
   straight into the increment bridge.
4. `abs_pairDensity_sub_mul_le` (`Finite/PairDensity.lean`) compares the recovered
   density with the witness density in **multiplication form**, so no denominator
   positivity is needed.
5. `blockEnergy_equitableIncrement_gain` — the approximate one-block increment, in direct
   loss form: the raw gain `ε² · (ε|C|) · (ε|D|)` degrades to
   `(ε − δ)² · (ε|C| − r) · (ε|D| − r)`, with the remainder `r` and the density error `δ`
   both explicit and unsimplified.

**No numerical constant is chosen here.** The density error `δ` is a parameter, certified
by the caller through `hδbound`, whose left side keeps the witness-size lower bound
`ε|C| − r` visible rather than simplifying against `|s|` — the conversion that would
otherwise cost a power of `ε`. Step 4 fixes `δ`, hence the retained fraction `c` of
`blockEnergy_equitableIncrement_gain_of_retained`, and only then the chunk threshold `C`
of `familyInitialBound`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)
variable {P : Finpartition s}

/-! ### The local/global bridge -/

/-- **The chunks inside a parent cell are exactly that parent's local chunks.** The
inclusion `⊇` is the definition of the bind; `⊆` uses that a chunk is nonempty and so
meets only one cell of `P`. -/
theorem filter_subset_equitableIncrement (hP : P.IsEquipartition) {C : Finset α}
    (hC : C ∈ P.parts) :
    (equitableIncrement R ε hP).parts.filter (· ⊆ C) = (equitableChunk R ε hP hC).parts := by
  ext b
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hb, hbC⟩
    obtain ⟨C', hC', hb'⟩ := (mem_equitableIncrement R ε).mp hb
    obtain ⟨x, hx⟩ := (equitableChunk R ε hP hC').nonempty_of_mem_parts hb'
    have hCC' : C = C' :=
      P.eq_of_mem_parts hC hC' (hbC hx) ((equitableChunk R ε hP hC').le hb' hx)
    subst hCC'
    exact hb'
  · intro hb
    exact ⟨(mem_equitableIncrement R ε).mpr ⟨C, hC, hb⟩, (equitableChunk R ε hP hC).le hb⟩

/-- Filtering the global chunks by a subset of one parent cell agrees with filtering that
parent's local chunks. -/
theorem filter_subset_equitableIncrement_of_subset (hP : P.IsEquipartition) {C B : Finset α}
    (hC : C ∈ P.parts) (hBC : B ⊆ C) :
    (equitableIncrement R ε hP).parts.filter (· ⊆ B)
      = (equitableChunk R ε hP hC).parts.filter (· ⊆ B) := by
  rw [← filter_subset_equitableIncrement R ε hP hC]
  ext b
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨⟨h.1, h.2.trans hBC⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

/-! ### The certifying layer: witness atoms -/

/-- **The certifying layer**: the parent cell atomised by its own witness cuts. Every
chosen witness side is exactly a union of these atoms. This partition is the INPUT to the
equitabilisation, not a coarsening of its output — the chunks do not refine it. -/
noncomputable def witnessAtoms (P : Finpartition s) (C : Finset α) : Finpartition C :=
  Finpartition.atomise C (witnessCuts R ε P C)

/-- **Step 1: the per-atom remainder.** Each atom of a parent cell loses at most one
chunk's worth of elements to chunks that straddle its boundary — mathlib's
`Finpartition.card_parts_equitabilise_subset_le`, transported through the chunk's case
split. -/
theorem card_sdiff_innerPartUnion_atom_le (hP : P.IsEquipartition) {C : Finset α}
    (hC : C ∈ P.parts) {B : Finset α} (hB : B ∈ (witnessAtoms R ε P C).parts) :
    (B \ (((equitableChunk R ε hP hC).parts.filter (· ⊆ B)).biUnion id)).card
      ≤ chunkSize P := by
  rw [equitableChunk]
  split_ifs with h
  · exact equitabilise_uncovered_card_le hB
  · exact equitabilise_uncovered_card_le hB

/-- **Step 2: a witness side is a union of its atoms.** -/
theorem biUnion_witnessAtoms_of_mem_witnessCuts {C W : Finset α}
    (hW : W ∈ witnessCuts R ε P C) :
    ((witnessAtoms R ε P C).parts.filter (fun B => B ⊆ W ∧ B.Nonempty)).biUnion id = W :=
  Finpartition.biUnion_filter_atomise hW (witnessCuts_subset R ε P hW)

/-- **Step 3: at most `2 ^ (2·#P.parts)` atoms contribute to a witness side**, because a
parent cell receives at most `2·#P.parts` cuts. -/
theorem card_filter_witnessAtoms_le {C W : Finset α} (hW : W ∈ witnessCuts R ε P C) :
    ((witnessAtoms R ε P C).parts.filter (fun B => B ⊆ W ∧ B.Nonempty)).card
      ≤ 2 ^ (2 * P.parts.card) := by
  refine le_trans (Finpartition.card_filter_atomise_le_two_pow hW) ?_
  have := witnessCuts_card_le R ε P C
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The witness-side remainder -/

/-- The per-witness-side chunk remainder: at most `2 ^ (2·#P.parts)` atoms, each losing at
most `chunkSize P`. Deliberately unsharpened — halving the atom count would not change
what step 4 needs. -/
def chunkWitnessRemainder (P : Finpartition s) : ℕ :=
  2 ^ (2 * P.parts.card) * chunkSize P

theorem chunkWitnessRemainder_eq_zero_iff : chunkWitnessRemainder P = 0 ↔ chunkSize P = 0 := by
  have h : (2 : ℕ) ^ (2 * P.parts.card) ≠ 0 := (pow_pos (by norm_num : (0 : ℕ) < 2) _).ne'
  rw [chunkWitnessRemainder, Nat.mul_eq_zero]
  tauto

/-- **The remainder-to-cell inequality.** The witness-side remainder is smaller than every
parent cell by the full equitabilisation factor: `r · 4^(n·2^(2n)) ≤ |C|`, because
`r · 4^(n·2^(2n)) = chunkSize P · familyChunksPerPart n`, which is what one parent cell's
share of the host is built from.

This is the exact structural bridge between the remainder and the cell sizes: it is what
lets a caller discharge the `r < ε|C|` and density-error hypotheses of the gain theorem
below, since the ratio `r / |C|` is at most `4^(−n·2^(2n))`. It chooses no `δ`, no
retained fraction, and no threshold — those are step 4's, where this is combined with
`le_pow_mul_of_familyInitialBound_le`. -/
theorem chunkWitnessRemainder_mul_pow_le_card_part (hP : P.IsEquipartition) {C : Finset α}
    (hC : C ∈ P.parts) :
    chunkWitnessRemainder P * 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card)) ≤ C.card := by
  have hfactor : chunkWitnessRemainder P * 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card))
      = chunkSize P * familyChunksPerPart P.parts.card := by
    rw [chunkWitnessRemainder, familyChunksPerPart]
    ring
  rw [hfactor]
  calc chunkSize P * familyChunksPerPart P.parts.card
      ≤ chunkSize P * familyChunksPerPart P.parts.card + chunkRem P := Nat.le_add_right _ _
    _ = s.card / P.parts.card := chunkSize_mul_add_chunkRem
    _ ≤ C.card := hP.average_le_card_part hC

/-- The real-cast form of the remainder-to-cell inequality, the shape the numerical
hypotheses of the gain theorem are stated in. -/
theorem chunkWitnessRemainder_mul_pow_le_card_part_cast (hP : P.IsEquipartition)
    {C : Finset α} (hC : C ∈ P.parts) :
    (chunkWitnessRemainder P : ℝ) * 4 ^ (P.parts.card * 2 ^ (2 * P.parts.card))
      ≤ (C.card : ℝ) := by
  exact_mod_cast chunkWitnessRemainder_mul_pow_le_card_part hP hC

/-- **Step 4: the witness-side remainder bound.** A chosen witness side is, up to
`chunkWitnessRemainder P` elements, a union of chunks. This is the exact sense in which
the produced layer approximates the certifying layer. -/
theorem card_sdiff_innerPartUnion_le (hP : P.IsEquipartition) {C W : Finset α}
    (hC : C ∈ P.parts) (hW : W ∈ witnessCuts R ε P C) :
    (W \ innerPartUnion (equitableIncrement R ε hP) W).card ≤ chunkWitnessRemainder P := by
  classical
  set Q := equitableIncrement R ε hP with hQ
  set 𝒜 := (witnessAtoms R ε P C).parts.filter (fun B => B ⊆ W ∧ B.Nonempty) with h𝒜
  have hWC : W ⊆ C := witnessCuts_subset R ε P hW
  have hcover : 𝒜.biUnion id = W := biUnion_witnessAtoms_of_mem_witnessCuts R ε hW
  have hsub : W \ innerPartUnion Q W ⊆ 𝒜.biUnion fun B => B \ innerPartUnion Q B := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxW, hxout⟩ := hx
    rw [← hcover, Finset.mem_biUnion] at hxW
    obtain ⟨B, hB, hxB⟩ := hxW
    have hBW : B ⊆ W := (Finset.mem_filter.mp hB).2.1
    refine Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_sdiff.mpr ⟨hxB, fun hxin => ?_⟩⟩
    exact hxout (innerPartUnion_mono hBW hxin)
  have hatom : ∀ B ∈ 𝒜, (B \ innerPartUnion Q B).card ≤ chunkSize P := by
    intro B hB
    rw [h𝒜, Finset.mem_filter] at hB
    obtain ⟨hBatom, hBW, -⟩ := hB
    rw [innerPartUnion, hQ, filter_subset_equitableIncrement_of_subset R ε hP hC
      (hBW.trans hWC)]
    exact card_sdiff_innerPartUnion_atom_le R ε hP hC hBatom
  calc (W \ innerPartUnion Q W).card
      ≤ (𝒜.biUnion fun B => B \ innerPartUnion Q B).card := Finset.card_le_card hsub
    _ ≤ ∑ B ∈ 𝒜, (B \ innerPartUnion Q B).card := Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ 𝒜, chunkSize P := Finset.sum_le_sum hatom
    _ = 𝒜.card * chunkSize P := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ (2 * P.parts.card) * chunkSize P :=
        Nat.mul_le_mul_right _ (card_filter_witnessAtoms_le R ε hW)

/-- **Step 5: the recovered witness side is nearly as large as the original.** -/
theorem card_le_card_innerPartUnion_add (hP : P.IsEquipartition) {C W : Finset α}
    (hC : C ∈ P.parts) (hW : W ∈ witnessCuts R ε P C) :
    (W.card : ℝ)
      ≤ ((innerPartUnion (equitableIncrement R ε hP) W).card : ℝ)
        + (chunkWitnessRemainder P : ℝ) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (innerPartUnion_subset (P := equitableIncrement R ε hP) (S := W))
  have hrem := card_sdiff_innerPartUnion_le R ε hP hC hW
  have : W.card
      ≤ (innerPartUnion (equitableIncrement R ε hP) W).card + chunkWitnessRemainder P := by
    omega
  exact_mod_cast this

/-! ### The approximate one-block increment -/

/-- **The approximate one-block energy increment, in direct loss form.** For a bad ordered
pair of cells, the equitabilised refinement gains
`(ε|C| − r) · (ε|D| − r) · (ε − δ)²` where `r = chunkWitnessRemainder P` is the chunk
remainder and `δ` is any certified bound on the density error. The raw exact-refinement
gain is `ε⁴|C||D| = (ε|C|) · (ε|D|) · ε²`, so each of the three factors is visibly
degraded and nothing else is lost.

The hypothesis `hδbound` is the multiplication-form conversion: the discarded mass
`r·|D| + |C|·r` measured against the RECOVERED rectangle, whose sides are bounded below by
the witness sizes `ε|C| − r` and `ε|D| − r`. Keeping those lower bounds — rather than
simplifying against `|s|` — is what prevents an extra power of `ε` from being lost when
step 4 chooses `δ`.

No `0 < ε` hypothesis is needed: `hrC` already forces it, since the remainder is a
natural number and `|C| ≥ 0`. -/
theorem blockEnergy_equitableIncrement_gain (hP : P.IsEquipartition)
    {C D : Finset α} (hC : C ∈ P.parts) (hD : D ∈ P.parts) (hbad : IsBadPair R ε C D)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε)
    (hrC : (chunkWitnessRemainder P : ℝ) < ε * (C.card : ℝ))
    (hrD : (chunkWitnessRemainder P : ℝ) < ε * (D.card : ℝ))
    (hδbound : (chunkWitnessRemainder P : ℝ) * (D.card : ℝ)
        + (C.card : ℝ) * (chunkWitnessRemainder P : ℝ)
      ≤ δ * ((ε * (C.card : ℝ) - (chunkWitnessRemainder P : ℝ))
          * (ε * (D.card : ℝ) - (chunkWitnessRemainder P : ℝ)))) :
    blockEnergy R C D
        + (ε * (C.card : ℝ) - (chunkWitnessRemainder P : ℝ))
          * (ε * (D.card : ℝ) - (chunkWitnessRemainder P : ℝ)) * (ε - δ) ^ 2
      ≤ ∑ C' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ C),
          ∑ D' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ D), blockEnergy R C' D' := by
  classical
  set Q := equitableIncrement R ε hP with hQ
  set w := NonuniformWitness.ofNotUniform hbad.2 with hw
  set r := (chunkWitnessRemainder P : ℝ) with hr
  set L := innerPartUnion Q w.left with hL
  set M := innerPartUnion Q w.right with hM
  have hWl : w.left ∈ witnessCuts R ε P C := left_mem_witnessCuts R ε hD hbad
  have hWr : w.right ∈ witnessCuts R ε P D := right_mem_witnessCuts R ε hC hbad
  have hLsub : L ⊆ w.left := innerPartUnion_subset
  have hMsub : M ⊆ w.right := innerPartUnion_subset
  -- Cardinalities of the recovered sides.
  have hcL : ε * (C.card : ℝ) - r ≤ (L.card : ℝ) := by
    have h1 := card_le_card_innerPartUnion_add R ε hP hC hWl
    have h2 := w.left_card
    linarith
  have hcM : ε * (D.card : ℝ) - r ≤ (M.card : ℝ) := by
    have h1 := card_le_card_innerPartUnion_add R ε hP hD hWr
    have h2 := w.right_card
    linarith
  have hLpos : 0 < (L.card : ℝ) := lt_of_lt_of_le (by linarith) hcL
  have hMpos : 0 < (M.card : ℝ) := lt_of_lt_of_le (by linarith) hcM
  have hpos : 0 < (L.card : ℝ) * (M.card : ℝ) := mul_pos hLpos hMpos
  -- The recovered sides are part unions of the increment; so are the parent cells.
  have hCU : IsPartUnion Q C := isPartUnion_of_mem_of_le (equitableIncrement_le R ε hP) hC
  have hDU : IsPartUnion Q D := isPartUnion_of_mem_of_le (equitableIncrement_le R ε hP) hD
  have hLU : IsPartUnion Q L := isPartUnion_innerPartUnion
  have hMU : IsPartUnion Q M := isPartUnion_innerPartUnion
  refine le_trans ?_ (blockEnergy_increment_refined_general R (hLsub.trans w.left_subset)
    (hMsub.trans w.right_subset) hpos hCU hDU hLU hMU)
  -- The density of the recovered rectangle is within `δ` of the witness density.
  have hdens : |pairDensity R L M - pairDensity R w.left w.right| ≤ δ := by
    have hmul := abs_pairDensity_sub_mul_le (R := R) hLsub hMsub
    have h1 : ((w.left \ L).card : ℝ) ≤ r := by
      rw [hL, hQ, hr]
      exact_mod_cast card_sdiff_innerPartUnion_le R ε hP hC hWl
    have h2 : ((w.right \ M).card : ℝ) ≤ r := by
      rw [hM, hQ, hr]
      exact_mod_cast card_sdiff_innerPartUnion_le R ε hP hD hWr
    have h3 : (w.right.card : ℝ) ≤ (D.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card w.right_subset)
    have h4 : (w.left.card : ℝ) ≤ (C.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card w.left_subset)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hstrip : ((w.left \ L).card : ℝ) * (w.right.card : ℝ)
        + (w.left.card : ℝ) * ((w.right \ M).card : ℝ) ≤ r * (D.card : ℝ) + (C.card : ℝ) * r := by
      have hn1 : (0 : ℝ) ≤ (w.right.card : ℝ) := Nat.cast_nonneg _
      have hn2 : (0 : ℝ) ≤ (w.left.card : ℝ) := Nat.cast_nonneg _
      have hn3 : (0 : ℝ) ≤ ((w.right \ M).card : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hmass : (ε * (C.card : ℝ) - r) * (ε * (D.card : ℝ) - r)
        ≤ (L.card : ℝ) * (M.card : ℝ) :=
      mul_le_mul hcL hcM (by linarith) (le_of_lt hLpos)
    have hfinal : |pairDensity R L M - pairDensity R w.left w.right|
        * ((L.card : ℝ) * (M.card : ℝ)) ≤ δ * ((L.card : ℝ) * (M.card : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hmass hδ0
      linarith
    exact le_of_mul_le_mul_right hfinal hpos
  -- Hence the recovered rectangle still deviates by more than `ε − δ`.
  have hgap : ε - δ ≤ |pairDensity R L M - pairDensity R C D| := by
    have htri : |pairDensity R w.left w.right - pairDensity R C D|
        ≤ |pairDensity R w.left w.right - pairDensity R L M|
          + |pairDensity R L M - pairDensity R C D| :=
      abs_sub_le _ _ _
    have hcomm : |pairDensity R w.left w.right - pairDensity R L M|
        = |pairDensity R L M - pairDensity R w.left w.right| := abs_sub_comm _ _
    have hdev := w.dev
    linarith [hcomm ▸ htri, hdens, hdev]
  have hsq : (ε - δ) ^ 2 ≤ (pairDensity R L M - pairDensity R C D) ^ 2 := by
    nlinarith [hgap, sq_abs (pairDensity R L M - pairDensity R C D),
      abs_nonneg (pairDensity R L M - pairDensity R C D)]
  have hmass : (ε * (C.card : ℝ) - r) * (ε * (D.card : ℝ) - r)
      ≤ (L.card : ℝ) * (M.card : ℝ) :=
    mul_le_mul hcL hcM (by linarith) (le_of_lt hLpos)
  have hgain : (ε * (C.card : ℝ) - r) * (ε * (D.card : ℝ) - r) * (ε - δ) ^ 2
      ≤ (L.card : ℝ) * (M.card : ℝ) * (pairDensity R L M - pairDensity R C D) ^ 2 :=
    mul_le_mul hmass hsq (sq_nonneg _) (le_of_lt hpos)
  linarith

/-- **The retained-fraction form** step 4 consumes: if the degraded product retains a
fraction `c` of the raw `ε⁴|C||D|` gain, the equitabilised refinement gains `c` times the
raw gain. No value of `c` is chosen here. -/
theorem blockEnergy_equitableIncrement_gain_of_retained (hP : P.IsEquipartition)
    {C D : Finset α} (hC : C ∈ P.parts) (hD : D ∈ P.parts) (hbad : IsBadPair R ε C D)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε)
    (hrC : (chunkWitnessRemainder P : ℝ) < ε * (C.card : ℝ))
    (hrD : (chunkWitnessRemainder P : ℝ) < ε * (D.card : ℝ))
    (hδbound : (chunkWitnessRemainder P : ℝ) * (D.card : ℝ)
        + (C.card : ℝ) * (chunkWitnessRemainder P : ℝ)
      ≤ δ * ((ε * (C.card : ℝ) - (chunkWitnessRemainder P : ℝ))
          * (ε * (D.card : ℝ) - (chunkWitnessRemainder P : ℝ))))
    {c : ℝ}
    (hretain : c * (ε ^ 4 * (C.card : ℝ) * (D.card : ℝ))
      ≤ (ε * (C.card : ℝ) - (chunkWitnessRemainder P : ℝ))
        * (ε * (D.card : ℝ) - (chunkWitnessRemainder P : ℝ)) * (ε - δ) ^ 2) :
    blockEnergy R C D + c * (ε ^ 4 * (C.card : ℝ) * (D.card : ℝ))
      ≤ ∑ C' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ C),
          ∑ D' ∈ (equitableIncrement R ε hP).parts.filter (· ⊆ D), blockEnergy R C' D' := by
  have := blockEnergy_equitableIncrement_gain R ε hP hC hD hbad hδ0 hδε hrC hrD hδbound
  linarith

/-! ### Tests and adversarial examples -/

section Tests

-- The inner approximation is a genuine approximation and can be STRICTLY smaller: the
-- atomisation of `{0,1,2,3}` by the cut `{0}` has atoms `{0}`, `{1,2,3}`, so the inner
-- approximation of `{0,1}` is only `{0}` — one element is lost. This is the phenomenon
-- the remainder calculus above bounds.
example :
    innerPartUnion (Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}})
      ({0, 1} : Finset (Fin 4)) = {0} := by decide

example :
    (({0, 1} : Finset (Fin 4)) \
      innerPartUnion (Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}})
        ({0, 1} : Finset (Fin 4))).card = 1 := by decide

-- A set that IS a part union loses nothing.
example :
    innerPartUnion (Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}})
      ({1, 2, 3} : Finset (Fin 4)) = {1, 2, 3} := by decide

-- The strip bound on pair counts, concretely: shrinking `univ ×ˢ univ` to `{0} ×ˢ univ`
-- on `Fin 3` loses at most `|{1,2}|·3 + 3·0 = 6` related pairs.
example :
    pairCount (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
      ≤ pairCount (fun a b : Fin 3 => a < b) {0} Finset.univ
        + ((Finset.univ : Finset (Fin 3)) \ {0}).card * (Finset.univ : Finset (Fin 3)).card
        + (Finset.univ : Finset (Fin 3)).card
          * ((Finset.univ : Finset (Fin 3)) \ Finset.univ).card := pairCount_le_add

-- The multiplication-form density comparison at a concrete shrinking: densities `1/2`
-- (on `{0} ×ˢ {1,2}`) and `3/9` (on the full square) differ by `1/6`, and `1/6 · 2 ≤ 6`.
example :
    |pairDensity (fun a b : Fin 3 => a < b) {0} {1, 2}
        - pairDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ|
      * ((({0} : Finset (Fin 3)).card : ℝ) * (({1, 2} : Finset (Fin 3)).card : ℝ))
    ≤ ((((Finset.univ : Finset (Fin 3)) \ {0}).card : ℝ)
        * ((Finset.univ : Finset (Fin 3)).card : ℝ))
      + ((Finset.univ : Finset (Fin 3)).card : ℝ)
        * ((((Finset.univ : Finset (Fin 3)) \ {1, 2}).card : ℝ)) :=
  abs_pairDensity_sub_mul_le (by decide) (by decide)

-- The general increment with NO witness: any nondegenerate sub-rectangle gains at least
-- its own weighted squared deviation (the other three cells may add more). Here the
-- sub-rectangle `{0} ×ˢ {1,2}` of the full square.
example :
    blockEnergy (fun a b : Fin 3 => a < b) Finset.univ Finset.univ
        + ((({0} : Finset (Fin 3)).card : ℝ) * (({1, 2} : Finset (Fin 3)).card : ℝ))
          * (pairDensity (fun a b : Fin 3 => a < b) {0} {1, 2}
            - pairDensity (fun a b : Fin 3 => a < b) Finset.univ Finset.univ) ^ 2
      ≤ blockEnergy (fun a b : Fin 3 => a < b) {0} {1, 2}
        + blockEnergy (fun a b : Fin 3 => a < b) {0} (Finset.univ \ {1, 2})
        + blockEnergy (fun a b : Fin 3 => a < b) (Finset.univ \ {0}) {1, 2}
        + blockEnergy (fun a b : Fin 3 => a < b) (Finset.univ \ {0}) (Finset.univ \ {1, 2}) :=
  blockEnergy_increment_general (by decide) (by decide) (by norm_num)

-- **Zero loss is the exact-refinement gain.** With no remainder and no density error the
-- degraded product is literally `ε⁴|C||D|` — so the theorem's three degraded factors are
-- exactly the three factors of the raw gain, and nothing else has been given away.
example (ε mC mD : ℝ) : (ε * mC - 0) * (ε * mD - 0) * (ε - 0) ^ 2 = ε ^ 4 * mC * mD := by
  ring

-- Consistently, the remainder vanishes exactly when the common chunk size does — both
-- directions (the degenerate regime, where the chunks are singletons and DO refine the
-- atoms).
example (P : Finpartition (Finset.univ : Finset (Fin 4))) :
    chunkWitnessRemainder P = 0 ↔ chunkSize P = 0 := chunkWitnessRemainder_eq_zero_iff

-- The degenerate regime the gain theorem excludes: if the remainder swallows the witness
-- lower bound (`r ≥ ε|C|`), the recovered side may be empty and no gain survives. The
-- hypothesis `hrC` is exactly this exclusion, and it is not vacuous.
example (P : Finpartition (Finset.univ : Finset (Fin 4))) (ε : ℝ)
    (h : ¬ ((chunkWitnessRemainder P : ℝ) < ε * ((Finset.univ : Finset (Fin 4)).card : ℝ))) :
    ε * ((Finset.univ : Finset (Fin 4)).card : ℝ) ≤ (chunkWitnessRemainder P : ℝ) :=
  not_lt.mp h

end Tests

end RegularityLemmata
