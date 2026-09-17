/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.AlmostRefines

/-!
# Representative maps and displaced sets

The **owner/displacement contract** between a new partition `Q` and an old partition `P` of the
same host `s`: a `RepresentativeMap P Q` is a map `rep : α → α` that is constant on the parts
of `Q` and lands in `s`, together with a displaced set `D ⊆ s`, such that every non-displaced
`x` has its representative in its own old part, `P.part (rep x) = P.part x`. The **owner** of
the new part of `x` is the old part `P.part (rep x)`; outside `D`, old label = owner (new label)
(`part_eq_owner`).

**This charge is not the almost-refinement charge.** `exceptionalMass Q P`
(`RegularityLemmata/Partition/AlmostRefines.lean`) counts every point of a new part not wholly contained in an old
part. A representative map may keep a *core* of such a crossing part (the points in its owner's
old part) and displace only the rest, so `|D|` can be strictly smaller: the regression below has
`exceptionalMass = 3` and `|D| = 1`. The two are related by one-way bridges, each under the exact
hypothesis that makes it valid:

* `ofExceptional` (mass → map): displacing every point of every crossing part, with the
  crossing parts owned by a designated old part `t₀`, gives a representative map with
  `|D| = exceptionalMass Q P` (`card_displaced_ofExceptional`).
* `ofExceptionalFree` (the **one free old part**): the same representatives, but the crossing
  points *inside* `t₀` already have the right owner and are not displaced,
  `D = crossingSet P Q \ t₀`. Its displaced set is the sum of the uncovered remainders of the
  *other* old parts (`card_displaced_ofExceptionalFree`), hence at most `(K − 1) · m` under a
  per-parent remainder `m` (`card_displaced_ofExceptionalFree_le`), and `0` for a single old
  part. Composed with mathlib's equitabilisation this is the **equitable construction**
  `exists_equitable_representativeMap`: for every requested part count `0 < t ≤ |s|`, an
  equipartition `Q` with exactly `t` parts and a representative map into `P` whose displaced
  set has size at most `(#P.parts − 1) · ⌊|s|/t⌋`, the per-old-part remainder `⌊|s|/t⌋` of
  `Finpartition.equitabilise` summed over the `K − 1` old parts other than `t₀`; stated with the
  floor visible, no divisibility assumed.
* `exceptionalMass_le_mul_card_displaced` (map → mass): if every part of `Q` has at most `b`
  elements, `exceptionalMass Q P ≤ b · |D|` (each crossing part contains a displaced point).

The singleton fallback is `bot`: `Q = ⊥` (all singletons, `|s|` parts) with `rep = id` and
`D = ∅`; more generally `ofLE` for any refinement `Q ≤ P`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The owner/displacement contract: `rep` is constant on the parts of `Q`, lands in `s`, and
sends every non-displaced element into its own old part. -/
structure RepresentativeMap (P Q : Finpartition s) where
  /-- The representative of (the new part of) an element. -/
  rep : α → α
  /-- The displaced set `D`. -/
  displaced : Finset α
  displaced_subset : displaced ⊆ s
  rep_mem : ∀ x ∈ s, rep x ∈ s
  rep_const : ∀ x ∈ s, ∀ y ∈ s, Q.part x = Q.part y → rep x = rep y
  part_rep : ∀ x ∈ s, x ∉ displaced → P.part (rep x) = P.part x

namespace RepresentativeMap

variable {P Q : Finpartition s} (r : RepresentativeMap P Q)

/-- The owner of the new part of `x`: the old part of its representative. -/
def owner (x : α) : Finset α := P.part (r.rep x)

theorem owner_mem_parts {x : α} (hx : x ∈ s) : r.owner x ∈ P.parts :=
  P.part_mem.mpr (r.rep_mem x hx)

/-- The owner depends only on the new part. -/
theorem owner_eq_of_part_eq {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : Q.part x = Q.part y) :
    r.owner x = r.owner y := by
  unfold owner; rw [r.rep_const x hx y hy h]

/-- Outside the displaced set, old label = owner (new label). -/
theorem part_eq_owner {x : α} (hx : x ∈ s) (hxD : x ∉ r.displaced) : P.part x = r.owner x :=
  (r.part_rep x hx hxD).symm

/-- **Singleton fallback.** `Q = ⊥` with the identity representative and nothing displaced. -/
def bot (P : Finpartition s) : RepresentativeMap P ⊥ where
  rep := id
  displaced := ∅
  displaced_subset := Finset.empty_subset _
  rep_mem := fun _ hx ↦ hx
  rep_const := fun x hx y _ h ↦ by
    have hx' : {x} ∈ (⊥ : Finpartition s).parts := by
      rw [Finpartition.parts_bot, Finset.mem_map]; exact ⟨x, hx, rfl⟩
    have := (⊥ : Finpartition s).part_eq_of_mem hx' (Finset.mem_singleton_self x)
    rw [this] at h
    have hy : y ∈ (⊥ : Finpartition s).part y := (⊥ : Finpartition s).mem_part_self.mpr ‹y ∈ s›
    rw [← h, Finset.mem_singleton] at hy
    exact hy.symm
  part_rep := fun _ _ _ ↦ rfl

@[simp] theorem card_displaced_bot (P : Finpartition s) : (bot P).displaced.card = 0 := rfl

/-- A refinement `Q ≤ P` admits a representative map with nothing displaced: represent each
new part by one of its elements. -/
noncomputable def ofLE (hQP : Q ≤ P) : RepresentativeMap P Q where
  rep := fun x ↦ if h : (Q.part x).Nonempty then h.choose else x
  displaced := ∅
  displaced_subset := Finset.empty_subset _
  rep_mem := fun x hx ↦ by
    have h : (Q.part x).Nonempty := ⟨x, Q.mem_part_self.mpr hx⟩
    simp only [h, dite_true]
    exact Q.le (Q.part_mem.mpr hx) h.choose_spec
  rep_const := fun x _ y hy h ↦ by
    have hy' : (Q.part y).Nonempty := ⟨y, Q.mem_part_self.mpr hy⟩
    simp only [h, hy', ↓reduceDIte]
  part_rep := fun x hx _ ↦ by
    have h : (Q.part x).Nonempty := ⟨x, Q.mem_part_self.mpr hx⟩
    simp only [h, dite_true]
    obtain ⟨t, ht, hsub⟩ := hQP (Q.part_mem.mpr hx)
    rw [P.part_eq_of_mem ht (hsub h.choose_spec),
      P.part_eq_of_mem ht (hsub (Q.mem_part_self.mpr hx))]

end RepresentativeMap

/-! ### The crossing set and the almost-refinement charge -/

/-- The points of `s` whose new part is contained in no old part. -/
def crossingSet (P Q : Finpartition s) : Finset α :=
  s.filter fun x ↦ ¬ ∃ t ∈ P.parts, Q.part x ⊆ t

/-- Inside an old part `t`, the uncovered remainder is exactly the crossing points of `t`. -/
theorem uncoveredWithin_eq_filter_crossing (P Q : Finpartition s) {t : Finset α}
    (ht : t ∈ P.parts) :
    uncoveredWithin Q t = (crossingSet P Q).filter (· ∈ t) := by
  ext x
  simp only [uncoveredWithin, crossingSet, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_biUnion, id, not_exists, not_and]
  constructor
  · rintro ⟨hxt, hcov⟩
    have hxs : x ∈ s := P.le ht hxt
    refine ⟨⟨hxs, fun t' ht' hsub ↦ ?_⟩, hxt⟩
    have hxt' : x ∈ t' := hsub (Q.mem_part_self.mpr hxs)
    have : t' = t := P.eq_of_mem_parts ht' ht hxt' hxt
    subst this
    exact hcov (Q.part x) ⟨Q.part_mem.mpr hxs, hsub⟩ (Q.mem_part_self.mpr hxs)
  · rintro ⟨⟨hxs, hcross⟩, hxt⟩
    refine ⟨hxt, fun u hu hxu ↦ ?_⟩
    have : u = Q.part x := (Q.part_eq_of_mem hu.1 hxu).symm
    exact hcross t ht (this ▸ hu.2)

/-- The almost-refinement charge is the number of crossing points. -/
theorem card_crossingSet (P Q : Finpartition s) : (crossingSet P Q).card = exceptionalMass Q P := by
  classical
  unfold exceptionalMass
  rw [Finset.sum_congr rfl fun t ht ↦ by rw [uncoveredWithin_eq_filter_crossing P Q ht]]
  have hmaps : ∀ x ∈ crossingSet P Q, P.part x ∈ P.parts := fun x hx ↦
    P.part_mem.mpr (Finset.mem_filter.mp hx).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  congr 1
  exact Finset.filter_congr fun x _ ↦ P.part_eq_iff_mem ht

/-! ### Bridge: mass → map -/

section OfExceptional

variable (P Q : Finpartition s) {t₀ : Finset α}

/-- The representative of a new part `u`: one of its elements if `u` lies inside an old part,
otherwise an element of the designated old part `t₀`. -/
private noncomputable def repOfPart (ht₀ : t₀ ∈ P.parts) (u : Finset α) : α :=
  if h : u.Nonempty ∧ ∃ t ∈ P.parts, u ⊆ t then h.1.choose
  else (P.nonempty_of_mem_parts ht₀).choose

/-- **Mass → map.** Displace every crossing point; crossing parts are owned by `t₀`. -/
noncomputable def RepresentativeMap.ofExceptional (ht₀ : t₀ ∈ P.parts) :
    RepresentativeMap P Q where
  rep := fun x ↦ repOfPart P ht₀ (Q.part x)
  displaced := crossingSet P Q
  displaced_subset := Finset.filter_subset _ _
  rep_mem := fun x hx ↦ by
    unfold repOfPart
    split_ifs with h
    · exact Q.le (Q.part_mem.mpr hx) h.1.choose_spec
    · exact P.le ht₀ (P.nonempty_of_mem_parts ht₀).choose_spec
  rep_const := fun x _ y _ h ↦ by simp only [h]
  part_rep := fun x hx hxD ↦ by
    simp only [crossingSet, Finset.mem_filter, not_and, not_not] at hxD
    obtain ⟨t, ht, hsub⟩ := hxD hx
    have hne : (Q.part x).Nonempty := ⟨x, Q.mem_part_self.mpr hx⟩
    have h : (Q.part x).Nonempty ∧ ∃ t ∈ P.parts, Q.part x ⊆ t := ⟨hne, t, ht, hsub⟩
    have hmem : repOfPart P ht₀ (Q.part x) ∈ Q.part x := by
      unfold repOfPart
      rw [dite_eq_left_of_eq_true (eq_true h)]
      exact Exists.choose_spec _
    rw [P.part_eq_of_mem ht (hsub hmem), P.part_eq_of_mem ht (hsub (Q.mem_part_self.mpr hx))]

/-- The displaced set of `ofExceptional` is the crossing set, of size `exceptionalMass Q P`. -/
theorem RepresentativeMap.card_displaced_ofExceptional (ht₀ : t₀ ∈ P.parts) :
    (RepresentativeMap.ofExceptional P Q ht₀).displaced.card = exceptionalMass Q P :=
  card_crossingSet P Q

/-- **One free old part.** The representatives of `ofExceptional`, but only the crossing points
outside `t₀` are displaced: a crossing point of `t₀` is represented in `t₀`, its own old part. -/
noncomputable def RepresentativeMap.ofExceptionalFree (ht₀ : t₀ ∈ P.parts) :
    RepresentativeMap P Q where
  rep := (RepresentativeMap.ofExceptional P Q ht₀).rep
  displaced := crossingSet P Q \ t₀
  displaced_subset := (Finset.sdiff_subset).trans (Finset.filter_subset _ _)
  rep_mem := (RepresentativeMap.ofExceptional P Q ht₀).rep_mem
  rep_const := (RepresentativeMap.ofExceptional P Q ht₀).rep_const
  part_rep := fun x hx hxD ↦ by
    rw [Finset.mem_sdiff, not_and, not_not] at hxD
    by_cases hcross : x ∈ crossingSet P Q
    · -- a crossing point of `t₀`: its representative is the chosen element of `t₀`.
      have hxt₀ : x ∈ t₀ := hxD hcross
      have hnot : ¬ ((Q.part x).Nonempty ∧ ∃ t ∈ P.parts, Q.part x ⊆ t) := fun h ↦
        (Finset.mem_filter.mp hcross).2 h.2
      show P.part (repOfPart P ht₀ (Q.part x)) = P.part x
      unfold repOfPart
      rw [dite_eq_right_of_eq_false (eq_false hnot),
        P.part_eq_of_mem ht₀ (P.nonempty_of_mem_parts ht₀).choose_spec, P.part_eq_of_mem ht₀ hxt₀]
    · exact (RepresentativeMap.ofExceptional P Q ht₀).part_rep x hx hcross

/-- The displaced set of `ofExceptionalFree` is the union of the uncovered remainders of the old
parts other than `t₀`. -/
theorem RepresentativeMap.card_displaced_ofExceptionalFree (ht₀ : t₀ ∈ P.parts) :
    (RepresentativeMap.ofExceptionalFree P Q ht₀).displaced.card
      = ∑ t ∈ P.parts.erase t₀, (uncoveredWithin Q t).card := by
  classical
  show (crossingSet P Q \ t₀).card = _
  have hmaps : ∀ x ∈ crossingSet P Q \ t₀, P.part x ∈ P.parts.erase t₀ := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxs : x ∈ s := (Finset.mem_filter.mp hx.1).1
    rw [Finset.mem_erase]
    refine ⟨fun h ↦ hx.2 (h ▸ P.mem_part_self.mpr hxs), P.part_mem.mpr hxs⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finset.mem_erase] at ht
  rw [uncoveredWithin_eq_filter_crossing P Q ht.2]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hc, _⟩, hpt⟩
    exact ⟨hc, (P.part_eq_iff_mem ht.2).mp hpt⟩
  · rintro ⟨hc, hxt⟩
    refine ⟨⟨hc, fun hxt₀ ↦ ht.1 (P.eq_of_mem_parts ht.2 ht₀ hxt hxt₀)⟩,
      (P.part_eq_iff_mem ht.2).mpr hxt⟩

/-- Under a per-parent remainder `m`, the free-part construction displaces at most
`(K − 1) · m` points, `K = #P.parts`; in particular `0` when `P` has a single part. -/
theorem RepresentativeMap.card_displaced_ofExceptionalFree_le (ht₀ : t₀ ∈ P.parts) {m : ℕ}
    (h : AlmostRefinesAt Q P m) :
    (RepresentativeMap.ofExceptionalFree P Q ht₀).displaced.card ≤ (P.parts.card - 1) * m := by
  rw [RepresentativeMap.card_displaced_ofExceptionalFree]
  calc ∑ t ∈ P.parts.erase t₀, (uncoveredWithin Q t).card
      ≤ ∑ _t ∈ P.parts.erase t₀, m :=
        Finset.sum_le_sum fun t ht ↦ h t (Finset.mem_of_mem_erase ht)
    _ = (P.parts.card - 1) * m := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem ht₀]

end OfExceptional

/-! ### Bridge: map → mass -/

/-- **Map → mass.** If every part of `Q` has at most `b` elements, the almost-refinement charge
is at most `b · |D|`: every crossing part contains a displaced point, and a crossing point is
charged to a displaced point of its own part. -/
theorem RepresentativeMap.exceptionalMass_le_mul_card_displaced {P Q : Finpartition s}
    (r : RepresentativeMap P Q) {b : ℕ} (hb : ∀ u ∈ Q.parts, u.card ≤ b) :
    exceptionalMass Q P ≤ b * r.displaced.card := by
  classical
  rw [← card_crossingSet]
  -- every crossing part contains a displaced point
  have hpick : ∀ x ∈ crossingSet P Q, ∃ d ∈ r.displaced, d ∈ Q.part x := by
    intro x hx
    rw [crossingSet, Finset.mem_filter] at hx
    obtain ⟨hxs, hcross⟩ := hx
    by_contra hnone
    push Not at hnone
    apply hcross
    refine ⟨P.part x, P.part_mem.mpr hxs, fun y hy ↦ ?_⟩
    have hys : y ∈ s := Q.le (Q.part_mem.mpr hxs) hy
    have hxD : x ∉ r.displaced := fun h ↦ hnone x h (Q.mem_part_self.mpr hxs)
    have hyD : y ∉ r.displaced := fun h ↦ hnone y h hy
    have hpart : Q.part x = Q.part y :=
      ((Q.mem_part_iff_part_eq_part hys hxs).mp hy).symm
    have : P.part y = P.part x := by
      rw [r.part_eq_owner hys hyD, r.part_eq_owner hxs hxD,
        r.owner_eq_of_part_eq hxs hys hpart]
    rw [← this]
    exact P.mem_part_self.mpr hys
  choose! d hdD hdpart using hpick
  calc (crossingSet P Q).card ≤ b * ((crossingSet P Q).image d).card := by
        refine Finset.card_le_mul_card_image _ _ fun y hy ↦ ?_
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
        calc ((crossingSet P Q).filter fun z ↦ d z = d x).card ≤ (Q.part (d x)).card := by
              refine Finset.card_le_card fun z hz ↦ ?_
              rw [Finset.mem_filter] at hz
              have hzs : z ∈ s := (Finset.mem_filter.mp hz.1).1
              have := hdpart z hz.1
              rw [hz.2] at this
              have hds : d x ∈ s := Q.le (Q.part_mem.mpr hxs) (hdpart x hx)
              rw [(Q.mem_part_iff_part_eq_part hds hzs).mp this]
              exact Q.mem_part_self.mpr hzs
          _ ≤ b := hb _ (Q.part_mem.mpr
                (Q.le (Q.part_mem.mpr hxs) (hdpart x hx)))
    _ ≤ b * r.displaced.card := by
        refine Nat.mul_le_mul_left b (Finset.card_le_card fun y hy ↦ ?_)
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact hdD x hx

/-! ### The equitable construction -/

/-- **Equitable representative map.** For a requested part count `0 < t ≤ |s|` and a designated
(free) old part `t₀`, an equipartition `Q` with exactly `t` parts and a representative map into
`P` whose displaced set has at most `(#P.parts − 1) · ⌊|s|/t⌋` elements: the per-old-part
remainder of mathlib's equitabilisation, summed over the old parts other than `t₀`. -/
theorem exists_equitable_representativeMap (P : Finpartition s) {t₀ : Finset α}
    (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card) :
    ∃ (Q : Finpartition s) (r : RepresentativeMap P Q), Q.IsEquipartition ∧ Q.parts.card = t ∧
      r.displaced.card ≤ (P.parts.card - 1) * (s.card / t) := by
  obtain ⟨Q, hQ, hcard, hat⟩ := exists_equipartition_almostRefinesAt P ht hts
  exact ⟨Q, RepresentativeMap.ofExceptionalFree P Q ht₀, hQ, hcard,
    RepresentativeMap.card_displaced_ofExceptionalFree_le P Q ht₀ hat⟩

/-- The `ε`-form: displaced mass at most `ε · |s|` once `⌊|s|/t⌋ · (#P.parts − 1) ≤ ε · |s|`. -/
theorem exists_equitable_representativeMap_of_le (P : Finpartition s) {t₀ : Finset α}
    (ht₀ : t₀ ∈ P.parts) {t : ℕ} (ht : 0 < t) (hts : t ≤ s.card) {ε : ℝ}
    (hbound : ((s.card / t : ℕ) : ℝ) * ((P.parts.card - 1 : ℕ) : ℝ) ≤ ε * s.card) :
    ∃ (Q : Finpartition s) (r : RepresentativeMap P Q), Q.IsEquipartition ∧ Q.parts.card = t ∧
      (r.displaced.card : ℝ) ≤ ε * s.card := by
  obtain ⟨Q, r, hQ, hcard, hD⟩ := exists_equitable_representativeMap P ht₀ ht hts
  refine ⟨Q, r, hQ, hcard, le_trans ?_ hbound⟩
  calc (r.displaced.card : ℝ) ≤ (((P.parts.card - 1) * (s.card / t) : ℕ) : ℝ) := by
        exact_mod_cast hD
    _ = ((s.card / t : ℕ) : ℝ) * ((P.parts.card - 1 : ℕ) : ℝ) := by push_cast; ring

/-! ### Tests and the crossing regression -/

section Tests

/-- The old partition `{{0, 1}, {2}}` of `{0, 1, 2}`, as the kernel partition of `![0, 0, 1]`. -/
private def lab : Fin 3 → Fin 2 := ![0, 0, 1]
private instance : DecidableRel (Setoid.ker lab).r := fun a b ↦
  inferInstanceAs (Decidable (lab a = lab b))
private def P₀ : Finpartition ({0, 1, 2} : Finset (Fin 3)) :=
  Finpartition.ofSetSetoid (Setoid.ker lab) {0, 1, 2}

example : P₀.parts = {{0, 1}, {2}} := by decide

-- **The crossing regression.** The indiscrete new partition `⊤` crosses both old parts. Its
-- almost-refinement charge is the whole host, `3`; the representative map owning the single new
-- part by the old part `{0, 1}` (representative `0`) displaces only `{2}`. So `|D| = 1 < 3`: the
-- representative-map charge is not the almost-refinement charge.
example : exceptionalMass (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) P₀ = 3 := by decide

private def rCross : RepresentativeMap P₀ (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) where
  rep := fun _ ↦ 0
  displaced := {2}
  displaced_subset := by decide
  rep_mem := by decide
  rep_const := by decide
  part_rep := by decide

example : rCross.displaced.card = 1 := by decide
example : rCross.displaced.card < exceptionalMass (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) P₀ := by
  decide
-- The map → mass bridge is tight here: the single part has `3` elements and `3 ≤ 3 · 1`.
example : exceptionalMass (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) P₀ ≤ 3 * rCross.displaced.card :=
  rCross.exceptionalMass_le_mul_card_displaced fun u hu ↦ by
    have := Finpartition.parts_top_subset _ hu
    rw [Finset.mem_singleton] at this
    subst this; decide
-- The mass → map direction displaces all three points.
example : (RepresentativeMap.ofExceptional P₀ (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
    (t₀ := {0, 1}) (by decide)).displaced.card = 3 := by
  rw [RepresentativeMap.card_displaced_ofExceptional]; decide
-- **The free-part construction** with `t₀ = {0, 1}` displaces exactly `{2}`, not all three points.
example : (RepresentativeMap.ofExceptionalFree P₀ (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3)))
    (t₀ := {0, 1}) (by decide)).displaced = {2} := by
  show crossingSet P₀ ⊤ \ {0, 1} = {2}
  decide
-- **One old part**: with `P = ⊤` the improved bound is `(1 − 1) · m = 0`, so nothing is displaced.
example (Q : Finpartition ({0, 1, 2} : Finset (Fin 3))) (m : ℕ)
    (h : AlmostRefinesAt Q (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) m) :
    (RepresentativeMap.ofExceptionalFree (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))) Q
      (t₀ := {0, 1, 2}) (by decide)).displaced.card = 0 := by
  have := RepresentativeMap.card_displaced_ofExceptionalFree_le _ Q (t₀ := {0, 1, 2}) (by decide) h
  have hcard : (⊤ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts.card = 1 := by decide
  rw [hcard] at this
  simpa using this

-- **Singleton fallback**: `⊥` has `|s|` parts and nothing displaced.
example : (RepresentativeMap.bot P₀).displaced = ∅ := rfl
example : (⊥ : Finpartition ({0, 1, 2} : Finset (Fin 3))).parts.card = 3 := by decide

-- **Owner reading** on the regression: outside `D`, old label = owner.
example : rCross.owner 0 = {0, 1} := by decide
example : P₀.part 1 = rCross.owner 1 := rCross.part_eq_owner (by decide) (by decide)

end Tests

end RegularityLemmata
