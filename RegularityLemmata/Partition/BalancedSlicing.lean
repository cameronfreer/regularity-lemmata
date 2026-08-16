/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.PrefixBlockSampling

/-!
# Balanced slicing

The consumer surface of the sampling stack (see
[regularity-lemmata#87](https://github.com/cameronfreer/regularity-lemmata/issues/87) for the
frozen contract): partition a finite set `A` into blocks of exact size `s` plus a leftover of
size `A.card % s < s`, so that every test set in a finite family keeps its density within `β`
on every block. The certificate object is `SliceCert` (from `Partition/PrefixBlockSampling`);
this file adds the **two-sided real-density reading** and the packaged existence theorem with a
single consumer-dischargeable inequality.

## Conventions (frozen)

* **Rounding.** Block size `s` is exact; the canonical block count is `A.card / s` (`ℕ` floor);
  the leftover is exactly `A.card % s`, bounded `< s` for `0 < s`
  (`SliceCert.card_leftover_eq_mod`, `SliceCert.card_leftover_lt`). The certificate's window
  `(A ∩ T).card * s / A.card + t` uses `ℕ`-floor division; the real-density corollary below
  absorbs that rounding.
* **Degenerate cases.** `s = 0` or `s > A.card` gives block count `0` and leftover `A`;
  existence needs no `A.Nonempty` — only the density corollaries do (they divide by `A.card`
  and `s`). See the tests.
* **Truncated subtraction.** In the ratio hypothesis, `2 * s - t` never truncates: `t < s`
  forces `s ≤ 2 * s - t`.
* **Rounding loss.** The frozen contract allowed a `β + 1/s` bound; the delivered bound is
  plain `β`: the `ℕ`-floor in the window is *favorable* in both directions (it rounds the
  upper target down, and rounds the complement window — hence the lower target's slack — down
  as well), so no `1/s` term survives. An improvement over the frozen text, not a deviation.
* **Two-sidedness.** The primitive control is one-sided; the corollary instantiates the
  certificate at the complement closure `traceComplementClosure A F` (size at most
  `2 * F.card`), which is why the packaged hypothesis carries the factor `2 * F.card`.
* **Simultaneity.** `F` is arbitrary: separate-carrier consumers pass one family per carrier; a
  synchronized same-carrier consumer passes row- and column-test sets in a single family and
  slices once.
* **No stability, no VC.** The family's cardinality enters only through the ratio hypothesis;
  a downstream consumer supplies its bound (e.g. by Sauer–Shelah from a VC bound). The
  threshold lemmas in `Partition/ExplicitPolyGeometricThreshold` are auxiliary conveniences
  for discharging the ratio hypothesis; nothing here fixes any downstream constant.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α]

/-- Splitting a block along a test set and its in-`A` complement: since blocks sit inside `A`,
the two intersections partition the block. -/
theorem card_inter_add_card_sdiff_inter {A T Q : Finset α} (hQ : Q ⊆ A) :
    (T ∩ Q).card + ((A \ T) ∩ Q).card = Q.card := by
  have h1 : T ∩ Q = Q.filter (fun x ↦ x ∈ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact and_comm
  have h2 : (A \ T) ∩ Q = Q.filter (fun x ↦ x ∉ T) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, hT⟩, hQ'⟩
      exact ⟨hQ', hT⟩
    · rintro ⟨hQ', hT⟩
      exact ⟨⟨hQ hQ', hT⟩, hQ'⟩
  rw [h1, h2, Finset.card_filter_add_card_filter_not]

/-- **Two-sided density control from a complement-closed certificate.** A slicing certificate
over `traceComplementClosure A F` keeps every `T ∈ F` within `β` of its `A`-density on every
block, provided `(t : ℝ) ≤ β * s`. The `ℕ`-floor window rounding is absorbed (see the module
docstring). -/
theorem SliceCert.abs_block_density_sub_le
    {A : Finset α} {F : Finset (Finset α)} {m s t : ℕ} {β : ℝ}
    (cert : SliceCert A (traceComplementClosure A F) m s t)
    (hA : A.Nonempty) (hs : 0 < s) (htβ : (t : ℝ) ≤ β * s)
    {T : Finset α} (hT : T ∈ F) (j : Fin m) :
    |((T ∩ cert.block j).card : ℝ) / s - ((A ∩ T).card : ℝ) / A.card| ≤ β := by
  obtain ⟨hTc, hTcompl⟩ := mem_traceComplementClosure A F hT
  have hn : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  -- Upper window on `T`, multiplied through by `A.card` (all in `ℕ`, then cast).
  have hupN : ((T ∩ cert.block j).card : ℝ) * A.card
      ≤ ((A ∩ T).card : ℝ) * s + (t : ℝ) * A.card := by
    have h1 : (T ∩ cert.block j).card * A.card
        ≤ (A ∩ T).card * s + t * A.card := by
      calc (T ∩ cert.block j).card * A.card
          ≤ ((A ∩ T).card * s / A.card + t) * A.card :=
            Nat.mul_le_mul_right _ (cert.trace_upper T hTc j)
        _ = ((A ∩ T).card * s / A.card) * A.card + t * A.card := add_mul _ _ _
        _ ≤ (A ∩ T).card * s + t * A.card :=
            Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    exact_mod_cast h1
  -- Lower bound via the complement's upper window and the block split.
  have hloN : ((A ∩ T).card : ℝ) * s
      ≤ ((T ∩ cert.block j).card : ℝ) * A.card + (t : ℝ) * A.card := by
    have hsplit : (T ∩ cert.block j).card + ((A \ T) ∩ cert.block j).card = s := by
      rw [card_inter_add_card_sdiff_inter (cert.block_subset j), cert.block_card j]
    have hAT : (A ∩ (A \ T)) = A \ T := Finset.inter_eq_right.mpr Finset.sdiff_subset
    have hcards : (A ∩ T).card + (A \ T).card = A.card := Finset.card_inter_add_card_sdiff A T
    have h1 : ((A \ T) ∩ cert.block j).card * A.card
        ≤ (A \ T).card * s + t * A.card := by
      calc ((A \ T) ∩ cert.block j).card * A.card
          ≤ ((A ∩ (A \ T)).card * s / A.card + t) * A.card :=
            Nat.mul_le_mul_right _ (cert.trace_upper (A \ T) hTcompl j)
        _ = ((A ∩ (A \ T)).card * s / A.card) * A.card + t * A.card := add_mul _ _ _
        _ ≤ (A ∩ (A \ T)).card * s + t * A.card :=
            Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        _ = (A \ T).card * s + t * A.card := by rw [hAT]
    have h1R : (((A \ T) ∩ cert.block j).card : ℝ) * A.card
        ≤ ((A \ T).card : ℝ) * s + (t : ℝ) * A.card := by exact_mod_cast h1
    have hsplitR : ((T ∩ cert.block j).card : ℝ)
        + (((A \ T) ∩ cert.block j).card : ℝ) = (s : ℝ) := by exact_mod_cast hsplit
    have hcardsR : ((A ∩ T).card : ℝ) + ((A \ T).card : ℝ) = (A.card : ℝ) := by
      exact_mod_cast hcards
    nlinarith [h1R, hsplitR, hcardsR]
  -- Combine and divide.
  rw [abs_sub_le_iff]
  have htn : (t : ℝ) * A.card ≤ β * s * A.card :=
    mul_le_mul_of_nonneg_right htβ hn.le
  constructor
  · rw [div_sub_div _ _ (ne_of_gt hsR) (ne_of_gt hn), div_le_iff₀ (by positivity)]
    nlinarith [hupN, htn]
  · rw [div_sub_div _ _ (ne_of_gt hn) (ne_of_gt hsR), div_le_iff₀ (by positivity)]
    nlinarith [hloN, htn]

/-- **Balanced slicing** (the packaged consumer theorem): under the single geometric ratio
hypothesis, `A` splits into `A.card / s` blocks of exact size `s` (leftover `A.card % s < s`,
via the certificate's `SliceCert.card_leftover_*` API) with every `T ∈ F` within `β` of its
`A`-density on every block. -/
theorem exists_balanced_slicing (A : Finset α) (F : Finset (Finset α)) {s t : ℕ} {β : ℝ}
    (hA : A.Nonempty) (hs : 0 < s) (ht : t < s) (htβ : (t : ℝ) ≤ β * s)
    (hratio : (A.card / s) * (2 * F.card) * (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8)) :
    ∃ cert : SliceCert A (traceComplementClosure A F) (A.card / s) s t,
      ∀ T ∈ F, ∀ j, |((T ∩ cert.block j).card : ℝ) / s - ((A ∩ T).card : ℝ) / A.card| ≤ β := by
  classical
  have hcard : ((traceFamilyOnParent A (traceComplementClosure A F)).filter
      fun T ↦ T.card * s / A.card + t < s).card ≤ 2 * F.card :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _))
      (le_trans (card_traceFamilyOnParent_le _ _) (card_traceComplementClosure_le A F))
  have hratio' : (A.card / s) * ((traceFamilyOnParent A (traceComplementClosure A F)).filter
      fun T ↦ T.card * s / A.card + t < s).card * (2 * s - t) ^ (t / 8)
      < (2 * s) ^ (t / 8) := by
    refine lt_of_le_of_lt ?_ hratio
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard)
  obtain ⟨cert⟩ := sliceCert_floor_exists A (traceComplementClosure A F) hs ht hratio'
  exact ⟨cert, fun T hT j ↦ cert.abs_block_density_sub_le hA hs htβ hT j⟩

/-! ### Tests and adversarial examples -/

section Tests

-- Empty test family: the ratio hypothesis degenerates to `0 < (2s)^(t/8)` and the density
-- clause is vacuous. (`β = 1`, `s = 2`, `t = 1`, so `t/8 = 0` and both powers are `1`.)
example : ∃ cert : SliceCert (Finset.univ : Finset (Fin 4))
    (traceComplementClosure Finset.univ ∅) (4 / 2) 2 1,
    ∀ T ∈ (∅ : Finset (Finset (Fin 4))), ∀ j,
      |((T ∩ cert.block j).card : ℝ) / 2
        - ((Finset.univ ∩ T).card : ℝ) / (Finset.univ : Finset (Fin 4)).card| ≤ 1 :=
  exists_balanced_slicing Finset.univ ∅ Finset.univ_nonempty (by norm_num) (by norm_num)
    (by norm_num) (by decide)

-- Degenerate block size `s = 0` (convention: block count `A.card / 0 = 0`, no blocks, the
-- whole set is leftover). Existence is trivial and needs no hypotheses at all.
example : Nonempty (SliceCert (Finset.univ : Finset (Fin 3)) ∅ 0 0 5) :=
  ⟨⟨Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun {i} ↦ i.elim0,
    fun T hT ↦ by simp at hT⟩⟩

-- Thin host `s > A.card` (convention: block count `2 / 5 = 0`, leftover is everything).
example : Nonempty (SliceCert (Finset.univ : Finset (Fin 2))
    (traceComplementClosure Finset.univ ∅) (2 / 5) 5 1) :=
  sliceCert_floor_exists _ _ (by norm_num) (by norm_num) (by decide)

-- NOTE (adversarial, documented): `2 * s - t` never truncates under `t < s` — at the boundary
-- `t = s - 1` it equals `s + 1`. The convention is enforced by the `ht` hypotheses, not by
-- normalizing the subtraction.
example : 2 * 3 - 2 = 3 + 1 := by decide

end Tests

end RegularityLemmata
