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
Non-injective ("collision") maps are characterized by a strictly ordered coordinate pair `i < j`
with `T i = T j` (`not_injective_iff_exists_lt_eq`) and counted by an ordered-pair union bound:
at most `|ι|² · |β|^(|ι| - 1)` of them, so collisions lose one ambient power of `|β|` — the form
consumed by counting and removal arguments. Once `2n² ≤ |α|`, at least half of all
`n`-tuples are injective.

The `s`-restricted layer (`injectiveTuplesOn`, `nonInjectiveTuplesOn`) counts tuples through a
finset: the injective ones by the restricted falling factorial `(|s|)_k`
(`card_injectiveTuplesOn`), the collisions by `(k.choose 2)·|s|^(k−1)`
(`card_nonInjectiveTuplesOn_le`). The injective/all-tuple **normalization conversion** follows:
`n^k ≤ (n)_k + (k.choose 2)·n^(k−1)` (`pow_le_descFactorial_add_choose_mul`), and for a count
`0 ≤ c ≤ (n)_k` the two densities `c / (n)_k` and `c / n^k` differ by at most `(k.choose 2) / n`,
guard-free under `x / 0 = 0` (`div_pow_le_div_descFactorial`,
`div_descFactorial_sub_div_pow_le`).

Conventions: raw counts in `ℕ`, ratio bounds in `ℝ`; positivity appears only when a denominator
must be inverted, while the normalization conversions are totalized at zero.
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

/-- **Collision characterization.** A `Fin k`-indexed tuple fails to be injective exactly when
two coordinates `i < j` collide. The strict order orients the collision witness (a tuple may have
several collisions; the theorem provides some strictly ordered one), which is what lets a
nontransversal charge be counted by *unordered* coordinate pairs (`k.choose 2`) rather than
ordered ones. -/
theorem not_injective_iff_exists_lt_eq {k : ℕ} {T : Fin k → α} :
    ¬ Function.Injective T ↔ ∃ i j, i < j ∧ T i = T j := by
  rw [Function.not_injective_iff]
  constructor
  · rintro ⟨a, b, hab, hne⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  · rintro ⟨i, j, hij, hT⟩
    exact ⟨i, j, hT, hij.ne⟩

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

/-! ### Injective tuples through a finset -/

/-- The injective `ι`-tuples drawn from `s`: the injective maps `ι → α` landing in the box
`fun _ ↦ s`. `injectiveTuples α n` is the full-carrier case `s = univ`, `ι = Fin n`. -/
def injectiveTuplesOn (ι : Type*) [Fintype ι] [DecidableEq ι] [DecidableEq α] (s : Finset α) :
    Finset (ι → α) :=
  (Fintype.piFinset fun _ => s).filter Function.Injective

/-- The non-injective `ι`-tuples drawn from `s`. -/
def nonInjectiveTuplesOn (ι : Type*) [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : Finset α) : Finset (ι → α) :=
  (Fintype.piFinset fun _ => s).filter fun f => ¬ Function.Injective f

section TuplesOn

variable [DecidableEq α] {s : Finset α}

@[simp] theorem mem_injectiveTuplesOn {f : ι → α} :
    f ∈ injectiveTuplesOn ι s ↔ (∀ i, f i ∈ s) ∧ Function.Injective f := by
  simp [injectiveTuplesOn, Fintype.mem_piFinset]

@[simp] theorem mem_nonInjectiveTuplesOn {f : ι → α} :
    f ∈ nonInjectiveTuplesOn ι s ↔ (∀ i, f i ∈ s) ∧ ¬ Function.Injective f := by
  simp [nonInjectiveTuplesOn, Fintype.mem_piFinset]

/-- **The restricted falling factorial.** The injective tuples through `s` are counted by
`(|s|)_{|ι|}`; at `s = univ` this is `injectiveTupleCount_eq_descFactorial`. -/
theorem card_injectiveTuplesOn (s : Finset α) :
    (injectiveTuplesOn ι s).card = s.card.descFactorial (Fintype.card ι) := by
  classical
  have himg : injectiveTuplesOn ι s
      = (Finset.univ.filter fun g : ι → s => Function.Injective g).image
          fun g => Subtype.val ∘ g := by
    ext f
    rw [mem_injectiveTuplesOn, Finset.mem_image]
    constructor
    · rintro ⟨hf, hinj⟩
      refine ⟨fun i => ⟨f i, hf i⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact fun i j h => hinj (congrArg Subtype.val h)
    · rintro ⟨g, hg, rfl⟩
      exact ⟨fun i => (g i).2, Subtype.val_injective.comp (Finset.mem_filter.mp hg).2⟩
  have hinj : Function.Injective fun g : ι → s => Subtype.val ∘ g :=
    fun g g' h => funext fun i => Subtype.ext (congr_fun h i)
  rw [himg, Finset.card_image_of_injective _ hinj, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding ι s), Fintype.card_embedding_eq,
    Fintype.card_coe]

/-- Every tuple through `s` is injective or not: the counts split `|s|^{|ι|}`. -/
theorem card_injectiveTuplesOn_add_card_nonInjectiveTuplesOn (s : Finset α) :
    (injectiveTuplesOn ι s).card + (nonInjectiveTuplesOn ι s).card
      = s.card ^ Fintype.card ι := by
  rw [injectiveTuplesOn, nonInjectiveTuplesOn, Finset.card_filter_add_card_filter_not,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

/-- **Where positivity lives.** The restricted falling factorial is positive exactly when
`|ι| ≤ |s|`; this is the only place the normalization layer needs a size hypothesis (inverting a
density bound into a count bound), never on the guard-free conversions below. -/
theorem card_injectiveTuplesOn_pos_iff (s : Finset α) :
    0 < (injectiveTuplesOn ι s).card ↔ Fintype.card ι ≤ s.card := by
  rw [card_injectiveTuplesOn, Nat.pos_iff_ne_zero, ne_eq, Nat.descFactorial_eq_zero_iff_lt,
    not_lt]

end TuplesOn

section CollisionOn

variable [DecidableEq α] {s : Finset α} {k : ℕ}

/-- One collision event on the `s`-box: for `i ≠ j`, at most `|s|^(k−1)` tuples through `s`
have `f i = f j` (dropping coordinate `j` is injective on the event). -/
private theorem card_filter_eq_on_le {i j : Fin k} (hij : i ≠ j) :
    ((Fintype.piFinset fun _ : Fin k => s).filter fun f => f i = f j).card
      ≤ s.card ^ (k - 1) := by
  classical
  set drop : (Fin k → α) → ({l : Fin k // l ≠ j} → α) := fun f l => f l.val with hdrop
  set event := (Fintype.piFinset fun _ : Fin k => s).filter fun f => f i = f j with hevent
  set box := Fintype.piFinset fun _ : {l : Fin k // l ≠ j} => s with hbox
  have hmaps : Set.MapsTo drop event box := by
    intro f hf
    rw [Finset.mem_coe, hevent, Finset.mem_filter, Fintype.mem_piFinset] at hf
    exact Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun l => hf.1 l.val)
  have hinj : Set.InjOn drop event := by
    intro f hf f' hf' h
    rw [Finset.mem_coe, hevent, Finset.mem_filter] at hf hf'
    funext l
    by_cases hl : l = j
    · subst hl
      rw [← hf.2, ← hf'.2]
      exact congr_fun h ⟨i, hij⟩
    · exact congr_fun h ⟨l, hl⟩
  refine (Finset.card_le_card_of_injOn drop hmaps hinj).trans (le_of_eq ?_)
  rw [hbox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
  simp [Fintype.card_subtype_compl]

/-- **Collisions on the `s`-box lose one power, with the unordered-pair coefficient.** At most
`(k.choose 2)·|s|^(k−1)` of the `k`-tuples through `s` are non-injective: each has some strictly
ordered collision `i < j` (`not_injective_iff_exists_lt_eq`), and each of the `k.choose 2`
collision events has at most `|s|^(k−1)` members. Sharper than `card_nonInjectiveMaps_le`'s
ordered-pair `|ι|²`. -/
theorem card_nonInjectiveTuplesOn_le (s : Finset α) (k : ℕ) :
    (nonInjectiveTuplesOn (Fin k) s).card ≤ k.choose 2 * s.card ^ (k - 1) := by
  classical
  set pairs : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2) with hpairs
  have hsub : nonInjectiveTuplesOn (Fin k) s ⊆ pairs.biUnion fun p =>
      (Fintype.piFinset fun _ : Fin k => s).filter fun f => f p.1 = f p.2 := by
    intro f hf
    rw [nonInjectiveTuplesOn, Finset.mem_filter] at hf
    obtain ⟨i, j, hij, hfij⟩ := not_injective_iff_exists_lt_eq.mp hf.2
    rw [Finset.mem_biUnion]
    exact ⟨(i, j), by rw [hpairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨hf.1, hfij⟩⟩
  have hcard : pairs.card = k.choose 2 := by
    simpa [hpairs] using Fintype.card_product_filter_lt (α := Fin k)
  calc (nonInjectiveTuplesOn (Fin k) s).card
      ≤ (pairs.biUnion fun p =>
          (Fintype.piFinset fun _ : Fin k => s).filter fun f => f p.1 = f p.2).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs,
          ((Fintype.piFinset fun _ : Fin k => s).filter fun f => f p.1 = f p.2).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, s.card ^ (k - 1) :=
        Finset.sum_le_sum fun p hp => card_filter_eq_on_le
          (by rw [hpairs, Finset.mem_filter] at hp; exact hp.2.ne)
    _ = k.choose 2 * s.card ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul, hcard]

end CollisionOn

/-! ### The injective/all-tuple normalization conversion -/

/-- **Additive conversion between the power and the falling factorial**:
`n^k ≤ (n)_k + (k.choose 2)·n^(k−1)`. Together with `Nat.descFactorial_le_pow` this pins the
all-tuple count to within `(k.choose 2)·n^(k−1)` of the injective count, in either direction. -/
theorem pow_le_descFactorial_add_choose_mul (n k : ℕ) :
    n ^ k ≤ n.descFactorial k + k.choose 2 * n ^ (k - 1) := by
  have h := card_injectiveTuplesOn_add_card_nonInjectiveTuplesOn
    (ι := Fin k) (Finset.univ : Finset (Fin n))
  have h2 := card_nonInjectiveTuplesOn_le (Finset.univ : Finset (Fin n)) k
  rw [card_injectiveTuplesOn, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- **Density conversion, lower half.** A count `c` of injective tuples (`0 ≤ c ≤ (n)_k`) has
power-normalized density at most its falling-factorial density. Guard-free under `x / 0 = 0`:
when `(n)_k = 0` the hypotheses force `c = 0`. -/
theorem div_pow_le_div_descFactorial {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ (n.descFactorial k : ℝ)) :
    c / (n : ℝ) ^ k ≤ c / (n.descFactorial k : ℝ) := by
  rcases Nat.eq_zero_or_pos (n.descFactorial k) with h0 | hpos
  · have hc0' : c = 0 := le_antisymm (by rw [h0] at hc; exact_mod_cast hc) hc0
    rw [hc0']; simp
  · exact div_le_div_of_nonneg_left hc0 (by exact_mod_cast hpos)
      (by exact_mod_cast Nat.descFactorial_le_pow n k)

/-- **Density conversion, upper half.** The falling-factorial density exceeds the
power-normalized density by at most `(k.choose 2) / n`. Guard-free under `x / 0 = 0`. -/
theorem div_descFactorial_sub_div_pow_le {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ (n.descFactorial k : ℝ)) :
    c / (n.descFactorial k : ℝ) - c / (n : ℝ) ^ k ≤ (k.choose 2 : ℝ) / n := by
  rcases Nat.eq_zero_or_pos (n.descFactorial k) with h0 | hpos
  · have hc0' : c = 0 := le_antisymm (by rw [h0] at hc; exact_mod_cast hc) hc0
    rw [hc0']
    simp only [zero_div, sub_zero]
    positivity
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `(0)_k > 0` forces `k = 0`, where both densities are `c`.
    have hk : k = 0 := by
      by_contra hk
      rw [hn0, Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.pos_of_ne_zero hk)] at hpos
      exact lt_irrefl _ hpos
    subst hk; simp
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; simp
  have hD : (0 : ℝ) < n.descFactorial k := by exact_mod_cast hpos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hnr k
  have hgap : (n : ℝ) ^ k - n.descFactorial k ≤ (k.choose 2 : ℝ) * (n : ℝ) ^ (k - 1) := by
    have := pow_le_descFactorial_add_choose_mul n k
    have h' : ((n ^ k : ℕ) : ℝ) ≤ ((n.descFactorial k + k.choose 2 * n ^ (k - 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hpow : (n : ℝ) ^ (k - 1) * n = (n : ℝ) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [div_sub_div _ _ hD.ne' hP.ne', div_le_div_iff₀ (mul_pos hD hP) hnr]
  calc (c * (n : ℝ) ^ k - (n.descFactorial k : ℝ) * c) * n
      = c * ((n : ℝ) ^ k - n.descFactorial k) * n := by ring
    _ ≤ c * ((k.choose 2 : ℝ) * (n : ℝ) ^ (k - 1)) * n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hc0) hnr.le
    _ = c * (k.choose 2 : ℝ) * (n : ℝ) ^ k := by rw [← hpow]; ring
    _ ≤ (n.descFactorial k : ℝ) * (k.choose 2 : ℝ) * (n : ℝ) ^ k := by
        gcongr
    _ = (k.choose 2 : ℝ) * ((n.descFactorial k : ℝ) * (n : ℝ) ^ k) := by ring

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

-- **Collision witnesses are reordered to `i < j`.** The collision `T 2 = T 0` is presented in the
-- wrong order; the characterization still applies, with the strictly ordered witness `(0, 2)`.
example {T : Fin 3 → ℕ} (h : T 2 = T 0) : ¬ Function.Injective T :=
  not_injective_iff_exists_lt_eq.mpr ⟨0, 2, by decide, h.symm⟩

-- A strictly ordered witness of a concrete collision, extracted and checked.
example : ∃ i j : Fin 3, i < j ∧ (![5, 7, 5] : Fin 3 → ℕ) i = ![5, 7, 5] j :=
  not_injective_iff_exists_lt_eq.mp (by decide)

-- **Degenerate arities**: on `Fin 0` and `Fin 1` every tuple is injective, so no witness exists.
example (T : Fin 0 → ℕ) : ¬ ∃ i j : Fin 0, i < j ∧ T i = T j :=
  fun h => (not_injective_iff_exists_lt_eq.mpr h) (fun a => a.elim0)
example (T : Fin 1 → ℕ) : ¬ ∃ i j : Fin 1, i < j ∧ T i = T j :=
  fun h => (not_injective_iff_exists_lt_eq.mpr h) (fun a b _ => Subsingleton.elim a b)

-- Half-bound instantiated at `n = 1`, `α = Fin 2` (hypothesis `2·1² ≤ 2` tight).
example : (Fintype.card (Fin 2) : ℝ) ^ 1 / 2 ≤ (injectiveTupleCount (Fin 2) 1 : ℝ) :=
  half_pow_le_injectiveTupleCount le_rfl (by decide)

-- **Restricted falling factorial, computed**: the injective pairs through `{0, 2} ⊆ Fin 3`
-- number `(2)_2 = 2`, the non-injective ones (the two constant pairs) also `2`, totalling `2²`.
example : (injectiveTuplesOn (Fin 2) ({0, 2} : Finset (Fin 3))).card = 2 := by decide
example : (injectiveTuplesOn (Fin 2) ({0, 2} : Finset (Fin 3))).card
    = Nat.descFactorial 2 2 := card_injectiveTuplesOn _
example : (nonInjectiveTuplesOn (Fin 2) ({0, 2} : Finset (Fin 3))).card = 2 := by decide

-- **The collision bound is attained at `k = 2`**: `2 = (2.choose 2) · 2¹`.
example : (nonInjectiveTuplesOn (Fin 2) ({0, 2} : Finset (Fin 3))).card
    = Nat.choose 2 2 * ({0, 2} : Finset (Fin 3)).card ^ (2 - 1) := by decide

-- **Degenerate arities**: no non-injective `0`- or `1`-tuples, and the bound is `0`.
example (s : Finset (Fin 3)) : (nonInjectiveTuplesOn (Fin 0) s).card = 0 := by
  simp [nonInjectiveTuplesOn, Function.injective_of_subsingleton]
example (s : Finset (Fin 3)) : (nonInjectiveTuplesOn (Fin 1) s).card = 0 := by
  simp [nonInjectiveTuplesOn, Function.injective_of_subsingleton]
example (s : Finset (Fin 3)) : Nat.choose 1 2 * s.card ^ (1 - 1) = 0 := by simp

-- **Additive conversion, tight at `n = 3`, `k = 2`**: `9 = 6 + 1·3`; and `27 ≤ 6 + 3·9` at `k = 3`.
example : 3 ^ 2 ≤ Nat.descFactorial 3 2 + Nat.choose 2 2 * 3 ^ (2 - 1) := by decide
example : 3 ^ 2 = Nat.descFactorial 3 2 + Nat.choose 2 2 * 3 ^ (2 - 1) := by decide
example : 3 ^ 3 ≤ Nat.descFactorial 3 3 + Nat.choose 3 2 * 3 ^ (3 - 1) := by decide

-- **Positivity lives on the inversion side only**: `(|s|)_k > 0 ↔ k ≤ |s|`.
example : 0 < (injectiveTuplesOn (Fin 2) ({0, 2} : Finset (Fin 3))).card :=
  (card_injectiveTuplesOn_pos_iff _).mpr (by decide)
example : ¬ 0 < (injectiveTuplesOn (Fin 3) ({0, 2} : Finset (Fin 3))).card :=
  fun h => absurd ((card_injectiveTuplesOn_pos_iff _).mp h) (by decide)

-- **The density conversion is guard-free at the `n < k` endpoint**: with `(2)_3 = 0` the only
-- admissible count is `c = 0`, and both sides are `0` under `x / 0 = 0`.
example : (0 : ℝ) / (Nat.descFactorial 2 3 : ℝ) - 0 / (2 : ℝ) ^ 3 ≤ (Nat.choose 3 2 : ℝ) / 2 :=
  div_descFactorial_sub_div_pow_le le_rfl (by simp)
example : (0 : ℝ) / (2 : ℝ) ^ 3 ≤ 0 / (Nat.descFactorial 2 3 : ℝ) :=
  div_pow_le_div_descFactorial le_rfl (by simp)

-- **The two halves bracket the falling-factorial density** by `(k.choose 2) / n`, statement-level.
example {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ (n.descFactorial k : ℝ)) :
    c / (n : ℝ) ^ k ≤ c / (n.descFactorial k : ℝ)
      ∧ c / (n.descFactorial k : ℝ) ≤ c / (n : ℝ) ^ k + (k.choose 2 : ℝ) / n :=
  ⟨div_pow_le_div_descFactorial hc0 hc,
    by linarith [div_descFactorial_sub_div_pow_le hc0 hc]⟩

-- Ordered range of an injective tuple.
example : tupleRange (![0, 2] : Fin 2 → Fin 3) = {0, 2} := by decide
example : (tupleRange (![0, 2] : Fin 2 → Fin 3)).card = 2 :=
  card_tupleRange_of_injective (by decide)

end RegularityLemmata
