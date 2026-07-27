/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPattern

/-!
# Route (b) ladder step 2: the generic proxy move

`ARCHITECTURE.md` route (b) ladder step 2 (2026-07-27). `Relational/CloneProxyProbe.lean`
exhibited, on one configuration, that each of the five placement strata can be moved to a
triple in three distinct proxy cells without changing the induced pattern. This file
generalizes those five moves, and **names the hypothesis that makes them sound** so that a
later rounding inherits it as an obligation rather than discovering it.

**Statement only — no construction.** No partition is built, no rounding, no
representative selection, no edits, no cleaning. `IsTransversalizable` remains unachieved
and `11B` remains closed.

## The hypothesis package

`IsOrderDeterminedProxyPalette M owner rank d` says the model's local data is determined by
the coarse owner and the proxy-lexicographic order, and by nothing else:

* **profiles depend only on the coarse owner**;
* **cross-owner palettes depend only on the ordered owner pair**;
* **within an owner** the palette is the diagonal palette `d` forwards, hence
  `swapBinaryPairPalette d` backwards by the reversal law, according to the strict order
  `ProxyLt`.

`ProxyLt rank x y` is proxy rank first, local vertex order within a proxy — lexicographic.
That refinement is the point: **across sibling proxies orientation comes from the proxy
rank, and within one proxy it comes from the local vertex order.** A rounding that orients
by vertex order alone would not satisfy this package, and the probe's third sharpness test
is why that matters.

## The moves

* `preservesAndReflects_proxy_move` — the transport step: any `g` preserving owners and
  same-owner relative order realizes exactly the patterns `f` does. This is where the
  hypothesis package is consumed, and it needs no proxy-distinctness at all.
* `exists_proxyDistinct_move` — the supply step: if every owner offers three vertices of
  strictly increasing proxy rank, such a `g` exists that is moreover **proxy-distinct**,
  i.e. the pairs `(owner, rank)` are pairwise distinct.
* `exists_proxyDistinct_preservesAndReflects_iff` — the two combined, which is the generic
  form of the probe's five cases. No case analysis on the placement strata survives: the
  strata are just the fibres of `owner ∘ f`, and the predecessor count handles them
  uniformly.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] [AtMostBinary L]
  {V : Type*} [LinearOrder V] {ι : Type*} [DecidableEq ι]

/-! ### The proxy-lexicographic order -/

/-- **Proxy-lexicographic order**: proxy rank first, local vertex order inside a proxy.
Across sibling proxies the orientation comes from the rank; within one proxy, from the
vertex order. -/
def ProxyLt (rank : V → ℕ) (x y : V) : Prop :=
  rank x < rank y ∨ (rank x = rank y ∧ x < y)

instance decidableProxyLt (rank : V → ℕ) (x y : V) : Decidable (ProxyLt rank x y) :=
  inferInstanceAs (Decidable (rank x < rank y ∨ (rank x = rank y ∧ x < y)))

theorem proxyLt_irrefl (rank : V → ℕ) (x : V) : ¬ ProxyLt rank x x := by
  rintro (h | ⟨-, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

theorem proxyLt_trans {rank : V → ℕ} {x y z : V} (hxy : ProxyLt rank x y)
    (hyz : ProxyLt rank y z) : ProxyLt rank x z := by
  rcases hxy with h1 | ⟨h1, h1'⟩ <;> rcases hyz with h2 | ⟨h2, h2'⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, lt_trans h1' h2'⟩

/-- Distinct vertices are comparable. -/
theorem proxyLt_total {rank : V → ℕ} {x y : V} (hxy : x ≠ y) :
    ProxyLt rank x y ∨ ProxyLt rank y x := by
  rcases lt_trichotomy (rank x) (rank y) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy x y with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd h' hxy
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem proxyLt_asymm {rank : V → ℕ} {x y : V} (h : ProxyLt rank x y) :
    ¬ ProxyLt rank y x := fun h' => proxyLt_irrefl rank x (proxyLt_trans h h')

/-- A strictly rank-increasing pair is `ProxyLt`-increasing. -/
theorem proxyLt_of_rank_lt {rank : V → ℕ} {x y : V} (h : rank x < rank y) :
    ProxyLt rank x y := Or.inl h

/-! ### The hypothesis package -/

/-- **The order-determined proxy palette.** The model's local data is a function of the
coarse owner and the proxy-lexicographic order and of nothing else. This is exactly the
constraint a later rounding must discharge; it is named here so that it cannot be
discovered implicitly. -/
structure IsOrderDeterminedProxyPalette (M : FiniteRelModel L V) (owner : V → ι)
    (rank : V → ℕ) (d : BinaryPairPalette L) : Prop where
  /-- Vertex profiles depend only on the coarse owner. -/
  profile_of_owner : ∀ x y, owner x = owner y →
    binaryVertexProfile M x = binaryVertexProfile M y
  /-- Cross-owner palettes depend only on the ordered owner pair. -/
  cross_of_owner : ∀ x y x' y', owner x ≠ owner y → owner x = owner x' →
    owner y = owner y' → binaryPairPalette M x y = binaryPairPalette M x' y'
  /-- Within an owner the palette is `d` forwards on the proxy-lexicographic order. -/
  within_forward : ∀ x y, owner x = owner y → ProxyLt rank x y →
    binaryPairPalette M x y = d

variable {M : FiniteRelModel L V} {owner : V → ι} {rank : V → ℕ} {d : BinaryPairPalette L}

omit [AtMostBinary L] [DecidableEq ι] in
/-- Backwards within an owner, the palette is the swap of `d` — the reversal law. -/
theorem IsOrderDeterminedProxyPalette.within_backward
    (h : IsOrderDeterminedProxyPalette M owner rank d) {x y : V} (hxy : owner x = owner y)
    (hlt : ProxyLt rank y x) : binaryPairPalette M x y = swapBinaryPairPalette d := by
  rw [binaryPairPalette_swap M y x, h.within_forward y x hxy.symm hlt]

/-! ### The transport step -/

/-- **The generic proxy move.** A map `g` that preserves coarse owners and same-owner
relative order realizes exactly the patterns `f` does. Proxy-distinctness plays no role
here — it is what the SUPPLY step below adds, and the two are kept apart deliberately. -/
theorem preservesAndReflects_proxy_move (h : IsOrderDeterminedProxyPalette M owner rank d)
    {P : FiniteRelModel L (Fin 3)} {f g : Fin 3 → V} (hf : Function.Injective f)
    (howner : ∀ i, owner (g i) = owner (f i))
    (horder : ∀ i j, owner (f i) = owner (f j) →
      ProxyLt rank (f i) (f j) → ProxyLt rank (g i) (g j)) :
    PreservesAndReflects P M f ↔ PreservesAndReflects P M g := by
  refine preservesAndReflects_transport (fun i => ?_) (fun i j hij => ?_)
  · exact h.profile_of_owner _ _ (howner i).symm
  · by_cases hown : owner (f i) = owner (f j)
    · have hgown : owner (g i) = owner (g j) := by rw [howner i, howner j]; exact hown
      have hne : f i ≠ f j := fun hEq => hij (hf hEq)
      rcases proxyLt_total (rank := rank) hne with hlt | hlt
      · rw [h.within_forward _ _ hown hlt,
          h.within_forward _ _ hgown (horder i j hown hlt)]
      · rw [h.within_backward hown hlt,
          h.within_backward hgown (horder j i hown.symm hlt)]
    · have hgown : owner (g i) ≠ owner (g j) := by
        rw [howner i, howner j]; exact hown
      exact h.cross_of_owner _ _ _ _ hown (howner i).symm (howner j).symm

/-! ### The supply step -/

section Supply

open scoped Classical in
/-- The number of same-owner coordinates strictly below `i` in the proxy order — the index
of `f i` inside its own owner class. -/
private noncomputable def ownerIndex (owner : V → ι) (rank : V → ℕ) (f : Fin 3 → V)
    (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun j : Fin 3 =>
    owner (f j) = owner (f i) ∧ ProxyLt rank (f j) (f i)).card

open scoped Classical in
private theorem ownerIndex_le_two (owner : V → ι) (rank : V → ℕ) (f : Fin 3 → V)
    (i : Fin 3) : ownerIndex owner rank f i ≤ 2 := by
  rw [ownerIndex]
  have hsub : (Finset.univ.filter fun j : Fin 3 =>
      owner (f j) = owner (f i) ∧ ProxyLt rank (f j) (f i)) ⊆ Finset.univ.erase i := by
    intro j hj
    rw [Finset.mem_filter] at hj
    refine Finset.mem_erase.mpr ⟨fun hEq => ?_, Finset.mem_univ _⟩
    exact proxyLt_irrefl rank (f i) (hEq ▸ hj.2.2)
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin] at this
  omega

open scoped Classical in
/-- The index is strictly monotone along the proxy order inside an owner class. -/
private theorem ownerIndex_lt_of_proxyLt (owner : V → ι) (rank : V → ℕ) {f : Fin 3 → V}
    {i j : Fin 3} (hown : owner (f i) = owner (f j)) (hlt : ProxyLt rank (f i) (f j)) :
    ownerIndex owner rank f i < ownerIndex owner rank f j := by
  rw [ownerIndex, ownerIndex]
  refine Finset.card_lt_card ⟨fun k hk => ?_, ?_⟩
  · rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_univ _, hk.2.1.trans hown, proxyLt_trans hk.2.2 hlt⟩
  · intro hsub
    have hi : i ∈ Finset.univ.filter fun k : Fin 3 =>
        owner (f k) = owner (f j) ∧ ProxyLt rank (f k) (f j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hown, hlt⟩
    have := hsub hi
    rw [Finset.mem_filter] at this
    exact proxyLt_irrefl rank (f i) this.2.2

/-- **The proxy supply**: every owner class offers three vertices of strictly increasing
proxy rank. Stated on `ℕ` indices with the monotonicity restricted to the first three, so
no dependent index bookkeeping enters the move. -/
def HasProxySupply (owner : V → ι) (rank : V → ℕ) : Prop :=
  ∃ p : ι → ℕ → V, (∀ o k, owner (p o k) = o) ∧
    ∀ o k l, k < l → l ≤ 2 → rank (p o k) < rank (p o l)

open scoped Classical in
/-- **The supply step.** Under `HasProxySupply`, every injective triple admits a move that
preserves owners and same-owner relative order and lands in three DISTINCT proxy cells. -/
theorem exists_proxyDistinct_move (owner : V → ι) (rank : V → ℕ)
    (hsupply : HasProxySupply owner rank) {f : Fin 3 → V} (hf : Function.Injective f) :
    ∃ g : Fin 3 → V, (∀ i, owner (g i) = owner (f i)) ∧
      (∀ i j, owner (f i) = owner (f j) →
        ProxyLt rank (f i) (f j) → ProxyLt rank (g i) (g j)) ∧
      (∀ i j, i ≠ j → (owner (g i), rank (g i)) ≠ (owner (g j), rank (g j))) := by
  obtain ⟨p, hpown, hprank⟩ := hsupply
  refine ⟨fun i => p (owner (f i)) (ownerIndex owner rank f i), fun i => hpown _ _, ?_, ?_⟩
  · intro i j hown hlt
    refine proxyLt_of_rank_lt ?_
    have hidx := ownerIndex_lt_of_proxyLt owner rank hown hlt
    have hle := ownerIndex_le_two owner rank f j
    have hstep := hprank (owner (f j)) (ownerIndex owner rank f i)
      (ownerIndex owner rank f j) hidx hle
    show rank (p (owner (f i)) (ownerIndex owner rank f i))
      < rank (p (owner (f j)) (ownerIndex owner rank f j))
    rw [hown]
    exact hstep
  · intro i j hij hEq
    dsimp only at hEq
    obtain ⟨h1, hrank⟩ := Prod.ext_iff.mp hEq
    rw [hpown, hpown] at h1
    have hown : owner (f i) = owner (f j) := h1
    have hne : f i ≠ f j := fun hEqf => hij (hf hEqf)
    rcases proxyLt_total (rank := rank) hne with hlt | hlt
    · have hidx := ownerIndex_lt_of_proxyLt owner rank hown hlt
      have hstep := hprank (owner (f j)) (ownerIndex owner rank f i)
        (ownerIndex owner rank f j) hidx (ownerIndex_le_two owner rank f j)
      rw [hown] at hrank
      omega
    · have hidx := ownerIndex_lt_of_proxyLt owner rank hown.symm hlt
      have hstep := hprank (owner (f i)) (ownerIndex owner rank f j)
        (ownerIndex owner rank f i) hidx (ownerIndex_le_two owner rank f i)
      rw [← hown] at hrank
      omega

/-- **The generic form of the probe's five cases.** Every injective triple has a
proxy-distinct triple realizing exactly the same patterns. No case analysis on the
placement strata appears: they are the fibres of `owner ∘ f`, and the predecessor count
treats them uniformly. -/
theorem exists_proxyDistinct_preservesAndReflects_iff
    (h : IsOrderDeterminedProxyPalette M owner rank d)
    (hsupply : HasProxySupply owner rank)
    {f : Fin 3 → V} (hf : Function.Injective f) :
    ∃ g : Fin 3 → V,
      (∀ i j, i ≠ j → (owner (g i), rank (g i)) ≠ (owner (g j), rank (g j))) ∧
      ∀ P : FiniteRelModel L (Fin 3),
        PreservesAndReflects P M f ↔ PreservesAndReflects P M g := by
  obtain ⟨g, howner, horder, hdist⟩ := exists_proxyDistinct_move owner rank hsupply hf
  exact ⟨g, hdist, fun P => preservesAndReflects_proxy_move h hf howner horder⟩

end Supply

/-! ### Tests -/

section Tests

/-- A three-vertex-per-proxy rank on `Fin 9`: proxies `{0,1,2}`, `{3,4,5}`, `{6,7,8}`. -/
private abbrev testRank (v : Fin 9) : ℕ := (v : ℕ) / 3

-- **Across sibling proxies the orientation comes from the RANK**, overriding the vertex
-- order: `2 < 3` in rank even though both comparisons could be read the other way round.
example : ProxyLt testRank 2 3 := by decide

example : ¬ ProxyLt testRank 3 2 := by decide

-- **Within one proxy the orientation comes from the LOCAL VERTEX ORDER.**
example : ProxyLt testRank 0 1 := by decide

example : ¬ ProxyLt testRank 1 0 := by decide

-- Rank strictly dominates: a low-rank vertex precedes every higher-rank one regardless of
-- how the vertex order compares inside the proxies.
example : ∀ x y : Fin 9, testRank x < testRank y → ProxyLt testRank x y := by decide

-- The order is irreflexive, transitive and total on distinct vertices, so a same-owner
-- pair is always comparable — which is what the transport step's case split needs.
example : ∀ x y : Fin 9, x ≠ y → (ProxyLt testRank x y ∨ ProxyLt testRank y x) := by decide

example : ∀ x y : Fin 9, ProxyLt testRank x y → ¬ ProxyLt testRank y x := by decide

-- A supply of three strictly increasing ranks exists in this configuration, one per
-- proxy — the shape `HasProxySupply` asks for, with representatives `0`, `3`, `6`.
example : ∀ k l : Fin 3, k < l →
    testRank (⟨3 * (k : ℕ), by omega⟩ : Fin 9) < testRank ⟨3 * (l : ℕ), by omega⟩ := by
  decide

end Tests

end RegularityLemmata
