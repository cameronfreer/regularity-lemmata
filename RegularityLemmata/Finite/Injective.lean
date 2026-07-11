/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Tuple
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Injective tuples and collision bounds

The number of injective tuples `Fin n → α` is the falling factorial
`(Fintype.card α).descFactorial n` (bridged to mathlib's `Fintype.card_embedding_eq`).
Non-injective ("collision") maps are counted by an ordered-pair union bound: at most
`|ι|² · |β|^(|ι| - 1)` of them, so collisions lose one ambient power of `|β|` — the form
consumed by counting and removal arguments. Once `2n² ≤ |α|`, at least half of all
`n`-tuples are injective.

Conventions: raw counts in `ℕ`, ratio bounds in `ℝ` with explicit positivity hypotheses.
-/

namespace RegularityLemmata

variable {α ι β : Type*}

/-! ### Injective tuples -/

/-- The finset of injective `n`-tuples over `α`. -/
def injectiveTuples (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ) :
    Finset (Fin n → α) :=
  Finset.univ.filter Function.Injective

@[simp] theorem mem_injectiveTuples [Fintype α] [DecidableEq α] {n : ℕ} {f : Fin n → α} :
    f ∈ injectiveTuples α n ↔ Function.Injective f := by
  simp [injectiveTuples]

/-- The number of injective `n`-tuples over `α` (the falling factorial `(|α|)_n`;
see `injectiveTupleCount_eq_descFactorial`). -/
def injectiveTupleCount (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ) : ℕ :=
  (injectiveTuples α n).card

theorem injectiveTupleCount_le_pow [Fintype α] [DecidableEq α] (n : ℕ) :
    injectiveTupleCount α n ≤ Fintype.card α ^ n := by
  refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
  simp

/-- Positivity of the injective tuple count: an injection `Fin n ↪ α` exists
whenever `n ≤ |α|`. -/
theorem injectiveTupleCount_pos_of_le [Fintype α] [DecidableEq α] {n : ℕ}
    (h : n ≤ Fintype.card α) : 0 < injectiveTupleCount α n := by
  rw [injectiveTupleCount, Finset.card_pos]
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using h : Fintype.card (Fin n) ≤ Fintype.card α)
  exact ⟨emb, mem_injectiveTuples.mpr emb.injective⟩

/-- The injective tuple count is the falling factorial. -/
theorem injectiveTupleCount_eq_descFactorial [Fintype α] [DecidableEq α] (n : ℕ) :
    injectiveTupleCount α n = (Fintype.card α).descFactorial n := by
  rw [injectiveTupleCount, injectiveTuples, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin n) α),
    Fintype.card_embedding_eq, Fintype.card_fin]

/-! ### Ordered range of a tuple -/

/-- The underlying finset of values of a tuple. -/
def tupleRange [DecidableEq α] {n : ℕ} (v : Fin n → α) : Finset α :=
  Finset.univ.image v

theorem card_tupleRange_of_injective [DecidableEq α] {n : ℕ} {v : Fin n → α}
    (hv : Function.Injective v) : (tupleRange v).card = n := by
  rw [tupleRange, Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]

-- `hv` is kept for API symmetry; it is derivable (equal ranges force equal
-- cardinalities of images), and only `hw` does real work.
set_option linter.unusedVariables false in
/-- **Enumeration of orderings**: two injective tuples with the same underlying set
differ by a permutation of the index type. -/
theorem exists_comp_perm_of_tupleRange_eq [DecidableEq α] {n : ℕ} {v w : Fin n → α}
    (hv : Function.Injective v) (hw : Function.Injective w)
    (h : tupleRange v = tupleRange w) : ∃ σ : Equiv.Perm (Fin n), w = v ∘ ⇑σ := by
  classical
  have hmem : ∀ i, w i ∈ tupleRange v := by
    intro i
    rw [h, tupleRange]
    exact Finset.mem_image_of_mem w (Finset.mem_univ i)
  choose f hf using fun i => Finset.mem_image.mp (hmem i)
  have hfv : ∀ i, v (f i) = w i := fun i => (hf i).2
  have hfinj : Function.Injective f := by
    intro i i' hii
    apply hw
    rw [← hfv i, ← hfv i', hii]
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  refine ⟨Equiv.ofBijective f hfbij, ?_⟩
  funext i
  exact (hfv i).symm

/-! ### Non-injective (collision) maps -/

/-- The finset of non-injective maps `ι → β`. -/
def nonInjectiveMaps (ι β : Type*) [Fintype ι] [DecidableEq ι] [Fintype β]
    [DecidableEq β] : Finset (ι → β) :=
  Finset.univ.filter fun f => ¬ Function.Injective f

variable [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

@[simp] theorem mem_nonInjectiveMaps {f : ι → β} :
    f ∈ nonInjectiveMaps ι β ↔ ¬ Function.Injective f := by
  simp [nonInjectiveMaps]

/-- For `i ≠ j`, the count of maps `f : ι → β` with `f i = f j` is at most
`|β|^(|ι| - 1)`, via the injective restriction `f ↦ f|_{≠ i}`. -/
private lemma card_filter_eq_le_pow {i j : ι} (hne : i ≠ j) :
    ((Finset.univ : Finset (ι → β)).filter (fun f => f i = f j)).card
      ≤ Fintype.card β ^ (Fintype.card ι - 1) := by
  have hbound : Fintype.card ({k : ι // k ≠ i} → β)
      = Fintype.card β ^ (Fintype.card ι - 1) := by
    rw [Fintype.card_fun]
    simp [Fintype.card_subtype_compl]
  calc ((Finset.univ : Finset (ι → β)).filter (fun f => f i = f j)).card
      = Fintype.card {f : ι → β // f i = f j} := (Fintype.card_subtype _).symm
    _ ≤ Fintype.card ({k : ι // k ≠ i} → β) := by
        refine Fintype.card_le_of_injective
          (fun f : {f : ι → β // f i = f j} => fun k : {k : ι // k ≠ i} => f.val k.val) ?_
        intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hfg
        apply Subtype.ext
        funext k
        show f₁ k = f₂ k
        by_cases hki : k = i
        · have hjne : j ≠ i := hne.symm
          have hjeval : f₁ j = f₂ j := congr_fun hfg ⟨j, hjne⟩
          rw [hki, hf₁, hf₂, hjeval]
        · exact congr_fun hfg ⟨k, hki⟩
    _ = Fintype.card β ^ (Fintype.card ι - 1) := hbound

/-- Cardinality bound on non-injective maps: `#nonInj ≤ |ι|² · |β|^(|ι| - 1)`
(ordered-pair union bound). -/
theorem card_nonInjectiveMaps_le :
    (nonInjectiveMaps ι β).card
      ≤ Fintype.card ι * Fintype.card ι * Fintype.card β ^ (Fintype.card ι - 1) := by
  set pairsFinset : Finset (ι × ι) := (Finset.univ : Finset ι).offDiag with hpairs_def
  set cover : ι × ι → Finset (ι → β) := fun p =>
    (Finset.univ : Finset (ι → β)).filter (fun f => f p.1 = f p.2) with hcover_def
  have hsubset : nonInjectiveMaps ι β ⊆ pairsFinset.biUnion cover := by
    intro f hf
    rw [mem_nonInjectiveMaps, Function.not_injective_iff] at hf
    obtain ⟨a, b, heq, hne⟩ := hf
    rw [Finset.mem_biUnion]
    refine ⟨(a, b), ?_, ?_⟩
    · rw [hpairs_def, Finset.mem_offDiag]
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩
    · rw [hcover_def]
      simp [heq]
  calc (nonInjectiveMaps ι β).card
      ≤ (pairsFinset.biUnion cover).card := Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ pairsFinset, (cover p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairsFinset, Fintype.card β ^ (Fintype.card ι - 1) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [hpairs_def, Finset.mem_offDiag] at hp
        obtain ⟨_, _, hne⟩ := hp
        exact card_filter_eq_le_pow hne
    _ = pairsFinset.card * Fintype.card β ^ (Fintype.card ι - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card ι * Fintype.card ι * Fintype.card β ^ (Fintype.card ι - 1) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [hpairs_def, Finset.offDiag_card, Finset.card_univ]
        exact Nat.sub_le _ _

/-- Collisions lose one ambient power: `#nonInj / |β|^|ι| ≤ |ι|² / |β|`. -/
theorem nonInjectiveMaps_ratio_le (hβ : 0 < Fintype.card β) :
    ((nonInjectiveMaps ι β).card : ℝ) / (Fintype.card β : ℝ) ^ Fintype.card ι
      ≤ (Fintype.card ι : ℝ) ^ 2 / (Fintype.card β : ℝ) := by
  have h_card_le_nat := card_nonInjectiveMaps_le (ι := ι) (β := β)
  have h_card_le : ((nonInjectiveMaps ι β).card : ℝ)
      ≤ (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)
        * (Fintype.card β : ℝ) ^ (Fintype.card ι - 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr h_card_le_nat
    push_cast at this
    exact this
  have h_β_pos : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr hβ
  have h_pow_pos : (0 : ℝ) < (Fintype.card β : ℝ) ^ Fintype.card ι := pow_pos h_β_pos _
  by_cases h_ι_zero : Fintype.card ι = 0
  · have h_empty : (nonInjectiveMaps ι β).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply le_trans card_nonInjectiveMaps_le
      rw [h_ι_zero]; simp
    rw [h_empty, Nat.cast_zero, zero_div]
    have : (Fintype.card ι : ℝ) ^ 2 / (Fintype.card β : ℝ) ≥ 0 := by
      apply div_nonneg <;> positivity
    linarith
  · have h_ι_pos : 1 ≤ Fintype.card ι := Nat.one_le_iff_ne_zero.mpr h_ι_zero
    have h_pow_split : (Fintype.card β : ℝ) ^ (Fintype.card ι - 1) * (Fintype.card β : ℝ)
        = (Fintype.card β : ℝ) ^ Fintype.card ι := by
      rw [← pow_succ, Nat.sub_add_cancel h_ι_pos]
    rw [div_le_div_iff₀ h_pow_pos h_β_pos]
    calc ((nonInjectiveMaps ι β).card : ℝ) * (Fintype.card β : ℝ)
        ≤ ((Fintype.card ι : ℝ) * Fintype.card ι
            * (Fintype.card β : ℝ) ^ (Fintype.card ι - 1)) * (Fintype.card β : ℝ) :=
          mul_le_mul_of_nonneg_right h_card_le h_β_pos.le
      _ = (Fintype.card ι : ℝ) * Fintype.card ι * (Fintype.card β : ℝ) ^ Fintype.card ι := by
          rw [mul_assoc, h_pow_split]
      _ = (Fintype.card ι : ℝ) ^ 2 * (Fintype.card β : ℝ) ^ Fintype.card ι := by ring

/-! ### The injective/non-injective split -/

/-- Every map is injective or not: the counts split the full power. -/
theorem injectiveTupleCount_add_card_nonInjectiveMaps [Fintype α] [DecidableEq α] {n : ℕ} :
    injectiveTupleCount α n + (nonInjectiveMaps (Fin n) α).card = Fintype.card α ^ n := by
  rw [injectiveTupleCount, injectiveTuples, nonInjectiveMaps,
    Finset.card_filter_add_card_filter_not, Finset.card_univ]
  simp

/-- Once `2n² ≤ |α|`, at least half of all `n`-tuples are injective. -/
theorem half_pow_le_injectiveTupleCount [Fintype α] [DecidableEq α] {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 2 * n ^ 2 ≤ Fintype.card α) :
    (Fintype.card α : ℝ) ^ n / 2 ≤ (injectiveTupleCount α n : ℝ) := by
  have hN : 0 < Fintype.card α := by
    have : 0 < 2 * n ^ 2 := by positivity
    omega
  have hNr : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hN
  have hpow : (0 : ℝ) < (Fintype.card α : ℝ) ^ n := pow_pos hNr n
  have hn_real : (2 : ℝ) * (n : ℝ) ^ 2 ≤ (Fintype.card α : ℝ) := by exact_mod_cast hn
  have hsum := injectiveTupleCount_add_card_nonInjectiveMaps (α := α) (n := n)
  have hsum_r : (injectiveTupleCount α n : ℝ)
      = (Fintype.card α : ℝ) ^ n - ((nonInjectiveMaps (Fin n) α).card : ℝ) := by
    have : (injectiveTupleCount α n : ℝ) + ((nonInjectiveMaps (Fin n) α).card : ℝ)
        = (Fintype.card α : ℝ) ^ n := by exact_mod_cast hsum
    linarith
  have hratio := nonInjectiveMaps_ratio_le (ι := Fin n) (β := α) hN
  rw [Fintype.card_fin] at hratio
  have hmul : ((nonInjectiveMaps (Fin n) α).card : ℝ) * (Fintype.card α : ℝ)
      ≤ (n : ℝ) ^ 2 * (Fintype.card α : ℝ) ^ n :=
    (div_le_div_iff₀ hpow hNr).mp hratio
  have hkey : 2 * ((n : ℝ) ^ 2 * (Fintype.card α : ℝ) ^ n)
      ≤ (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ n := by
    nlinarith [mul_le_mul_of_nonneg_right hn_real hpow.le]
  rw [hsum_r]
  nlinarith [hmul, hkey, hNr, hpow, mul_pos hNr hpow]

/-! ### Tests and adversarial examples -/

-- Exact counts: `(3)_0 = 1`, `(3)_1 = 3`, `(3)_2 = 6`, `(3)_3 = 6`.
example : injectiveTupleCount (Fin 3) 0 = 1 := by decide
example : injectiveTupleCount (Fin 3) 1 = 3 := by decide
example : injectiveTupleCount (Fin 3) 2 = 6 := by decide
example : injectiveTupleCount (Fin 3) 3 = 6 := by decide

-- No injective tuple into a strictly smaller type.
example : injectiveTupleCount (Fin 2) 3 = 0 := by decide

-- Falling-factorial agreement, computed.
example : injectiveTupleCount (Fin 3) 2 = Nat.descFactorial 3 2 := by decide
example : injectiveTupleCount (Fin 4) 3 = Nat.descFactorial 4 3 := by decide

-- The unique map `Fin 2 → Fin 1` collides.
example : (nonInjectiveMaps (Fin 2) (Fin 1)).card = 1 := by decide

-- Half-bound instantiated at `n = 1`, `α = Fin 2` (hypothesis `2·1² ≤ 2` tight).
example : (Fintype.card (Fin 2) : ℝ) ^ 1 / 2 ≤ (injectiveTupleCount (Fin 2) 1 : ℝ) :=
  half_pow_le_injectiveTupleCount le_rfl (by decide)

-- Ordered range of an injective tuple.
example : tupleRange (![0, 2] : Fin 2 → Fin 3) = {0, 2} := by decide
example : (tupleRange (![0, 2] : Fin 2 → Fin 3)).card = 2 :=
  card_tupleRange_of_injective (by decide)

end RegularityLemmata
