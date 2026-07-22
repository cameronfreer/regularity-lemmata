/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Route (b) supplier checkpoint, item 1: greedy independent sets under a degree cap

`ARCHITECTURE.md` route (b), supplier checkpoint (2026-07-22): the abstract
greedy/independent-set substrate, with the equal-weight discipline EXPLICIT.

* `badNbhd B S v` — the symmetrized bad-neighborhood (`B v u ∨ B u v`): cleanliness
  of the extracted set controls BOTH orientations, so an asymmetric bad-pair
  predicate (some palette color nonuniform in some direction) is symmetrized here,
  once, rather than in every caller.
* `exists_clean_subset_of_degree_le` — greedy core: a degree cap `D` yields a
  pairwise-clean subset carrying a `1/(D+1)` fraction (each greedy step spends the
  chosen vertex and its at most `D` bad neighbors).
* `card_filter_degree_le` — the Markov half: if the summed symmetrized bad-degree is
  at most `E` and `2·E ≤ |S|·(D+1)`, at least half of `S` has bad-degree at most
  `D`.
* `exists_clean_subset` — the summit: under the same counting hypotheses, a
  pairwise-clean subset with `|S| ≤ 2·(D+1)·|T|`.

**Equal weights are a hypothesis of the conversion feeding `E`, not a
convenience** (supplier checkpoint finding, 2026-07-22): a regular partition
controls bad pairs by WEIGHTED mass `|C|·|D|`, and with one large cell and many
tiny cells almost every distinct cell pair can be bad while the weighted mass stays
small — weighted bad mass does NOT bound the unweighted bad-pair count that `E`
measures. The route (b) supplier must deliver equal-cardinality (or
fixed-comparability `Λ`) cells BEFORE this substrate applies. In the intended
instantiation `E` also carries the palette/orientation factor explicitly: the
bad-pair predicate is the union over the `K` palette colors and both ordered
directions, so `E` sums `2·K` per-color one-direction counts.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V]

/-- The symmetrized bad-neighborhood of `v` within `S`. -/
def badNbhd (B : V → V → Prop) [DecidableRel B] (S : Finset V) (v : V) : Finset V :=
  S.filter (fun u => B v u ∨ B u v)

omit [DecidableEq V] in
theorem badNbhd_subset {B : V → V → Prop} [DecidableRel B] {S : Finset V} {v : V} :
    badNbhd B S v ⊆ S :=
  Finset.filter_subset _ _

omit [DecidableEq V] in
theorem badNbhd_mono {B : V → V → Prop} [DecidableRel B] {S S' : Finset V}
    (h : S' ⊆ S) (v : V) : badNbhd B S' v ⊆ badNbhd B S v :=
  Finset.filter_subset_filter _ h

omit [DecidableEq V] in
/-- Membership outside the bad-neighborhood cleans both orientations. -/
theorem not_bad_of_mem_of_notMem_badNbhd {B : V → V → Prop} [DecidableRel B]
    {S : Finset V} {v u : V} (hu : u ∈ S) (h : u ∉ badNbhd B S v) :
    ¬ B v u ∧ ¬ B u v := by
  rw [badNbhd, Finset.mem_filter] at h
  push Not at h
  exact h hu

/-- **Greedy core**: a symmetrized bad-degree cap `D` on `S` yields a pairwise-clean
subset carrying a `1/(D+1)` fraction of `S`. -/
theorem exists_clean_subset_of_degree_le (B : V → V → Prop) [DecidableRel B]
    (D : ℕ) (S : Finset V) (hdeg : ∀ v ∈ S, (badNbhd B S v).card ≤ D) :
    ∃ T ⊆ S, S.card ≤ (D + 1) * T.card ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ B x y := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, subset_rfl, by simp, by simp⟩
    have hstrict : S \ insert v (badNbhd B S v) ⊂ S :=
      Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.mpr
        ⟨v, hv, fun hmem =>
          (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self _ _)⟩
    obtain ⟨T', hT'sub, hT'card, hT'clean⟩ :=
      ih _ hstrict (fun u hu =>
        le_trans
          (Finset.card_le_card
            (badNbhd_mono Finset.sdiff_subset u))
          (hdeg u (Finset.mem_sdiff.mp hu).1))
    have hvT' : v ∉ T' := fun hmem =>
      (Finset.mem_sdiff.mp (hT'sub hmem)).2 (Finset.mem_insert_self _ _)
    refine ⟨insert v T', ?_, ?_, ?_⟩
    · exact Finset.insert_subset hv (hT'sub.trans Finset.sdiff_subset)
    · have h1 : S.card ≤ (S \ insert v (badNbhd B S v)).card
          + (insert v (badNbhd B S v)).card :=
        Finset.card_le_card_sdiff_add_card
      have h2 : (insert v (badNbhd B S v)).card ≤ D + 1 :=
        le_trans (Finset.card_insert_le _ _)
          (Nat.add_le_add_right (hdeg v hv) 1)
      rw [Finset.card_insert_of_notMem hvT']
      calc S.card ≤ (S \ insert v (badNbhd B S v)).card + (D + 1) := by omega
        _ ≤ (D + 1) * T'.card + (D + 1) := by omega
        _ = (D + 1) * (T'.card + 1) := by ring
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact absurd rfl hxy
        · have hyS := Finset.mem_sdiff.mp (hT'sub hy')
          exact (not_bad_of_mem_of_notMem_badNbhd hyS.1 fun hbad =>
            hyS.2 (Finset.mem_insert_of_mem hbad)).1
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · have hxS := Finset.mem_sdiff.mp (hT'sub hx')
          exact (not_bad_of_mem_of_notMem_badNbhd hxS.1 fun hbad =>
            hxS.2 (Finset.mem_insert_of_mem hbad)).2
        · exact hT'clean x hx' y hy' hxy

omit [DecidableEq V] in
/-- **The Markov half**: if the summed symmetrized bad-degree is at most `E` and
`2·E ≤ |S|·(D+1)`, at least half of `S` has bad-degree at most `D`. -/
theorem card_filter_degree_le (B : V → V → Prop) [DecidableRel B] (S : Finset V)
    {E D : ℕ} (hE : ∑ v ∈ S, (badNbhd B S v).card ≤ E)
    (hD : 2 * E ≤ S.card * (D + 1)) :
    S.card ≤ 2 * (S.filter (fun v => (badNbhd B S v).card ≤ D)).card := by
  classical
  have hsplit : (S.filter (fun v => (badNbhd B S v).card ≤ D)).card
      + (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card = S.card :=
    Finset.card_filter_add_card_filter_not (fun v => (badNbhd B S v).card ≤ D)
  have h1 : (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card * (D + 1)
      ≤ ∑ v ∈ S.filter (fun v => ¬ (badNbhd B S v).card ≤ D),
          (badNbhd B S v).card := by
    calc (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card * (D + 1)
        = ∑ _v ∈ S.filter (fun v => ¬ (badNbhd B S v).card ≤ D), (D + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ ∑ v ∈ S.filter (fun v => ¬ (badNbhd B S v).card ≤ D),
            (badNbhd B S v).card :=
          Finset.sum_le_sum fun v hv => by
            have h := (Finset.mem_filter.mp hv).2
            omega
  have h2 : ∑ v ∈ S.filter (fun v => ¬ (badNbhd B S v).card ≤ D),
        (badNbhd B S v).card ≤ ∑ v ∈ S, (badNbhd B S v).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 : 2 * (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card * (D + 1)
      ≤ S.card * (D + 1) := by
    calc 2 * (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card * (D + 1)
        = 2 * ((S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card * (D + 1)) :=
          by ring
      _ ≤ 2 * E := by omega
      _ ≤ S.card * (D + 1) := hD
  have h4 : 2 * (S.filter (fun v => ¬ (badNbhd B S v).card ≤ D)).card ≤ S.card :=
    Nat.le_of_mul_le_mul_right h3 (Nat.succ_pos D)
  omega

/-- **The equal-weight independent-set extraction summit.** From a symmetrized
bad-degree total of at most `E` over `S` with `2·E ≤ |S|·(D+1)`, a pairwise-clean
subset carrying at least a `1/(2·(D+1))` fraction of `S`. The counting feeding `E`
must already be UNWEIGHTED — see the module docstring for why equal (or
fixed-comparability) cell sizes are a genuine precondition of the route (b)
supplier, and how `E` carries the `2·K` palette/orientation factor. -/
theorem exists_clean_subset (B : V → V → Prop) [DecidableRel B] (S : Finset V)
    {E D : ℕ} (hE : ∑ v ∈ S, (badNbhd B S v).card ≤ E)
    (hD : 2 * E ≤ S.card * (D + 1)) :
    ∃ T ⊆ S, S.card ≤ 2 * (D + 1) * T.card ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ B x y := by
  classical
  have h0 := card_filter_degree_le B S hE hD
  obtain ⟨T, hTsub, hTcard, hTclean⟩ :=
    exists_clean_subset_of_degree_le B D
      (S.filter (fun v => (badNbhd B S v).card ≤ D))
      (fun v hv =>
        le_trans
          (Finset.card_le_card (badNbhd_mono (Finset.filter_subset _ _) v))
          (Finset.mem_filter.mp hv).2)
  refine ⟨T, hTsub.trans (Finset.filter_subset _ _), ?_, hTclean⟩
  calc S.card ≤ 2 * (S.filter (fun v => (badNbhd B S v).card ≤ D)).card := h0
    _ ≤ 2 * ((D + 1) * T.card) := by omega
    _ = 2 * (D + 1) * T.card := by ring

/-! ### Tests -/

section Tests

-- The symmetrized neighborhood, concretely: `B` relating only `0 → 1` inside
-- `{0, 1, 2}` gives both `1 ∈ badNbhd 0` and `0 ∈ badNbhd 1` (symmetrization),
-- and `badNbhd 2 = ∅`.
example : badNbhd (fun a b : Fin 3 => a = 0 ∧ b = 1) {0, 1, 2} 0 = {1} := by decide

example : badNbhd (fun a b : Fin 3 => a = 0 ∧ b = 1) {0, 1, 2} 1 = {0} := by decide

example : badNbhd (fun a b : Fin 3 => a = 0 ∧ b = 1) {0, 1, 2} 2 = ∅ := by decide

-- Degenerate sanity: with no bad pairs, `D = 0` and `E = 0` return at least half of
-- `S` (the greedy core alone would return all of it).
example (S : Finset (Fin 5)) :
    ∃ T ⊆ S, S.card ≤ 2 * (0 + 1) * T.card ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ (fun _ _ : Fin 5 => False) x y :=
  exists_clean_subset _ S (E := 0)
    (by simp [badNbhd]) (by omega)

end Tests

end RegularityLemmata
