/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.BinaryTreeProperEmbedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# The additive two-color subtree theorem, and its multicolor form

Two-color the internal nodes of a full binary tree of height `a + b + 1`. Then it contains
either a color-`0` subtree of height `a + 1` or a color-`1` subtree of height `b + 1`, where
"subtree" means the image of an `InternalEmbedding`: arbitrary root, branch direction preserved,
depth unconstrained.

## A precise upper theorem, without an optimality claim

The theorem states the explicit height `a + b + 1`. No matching lower-bound coloring is
formalized, so no optimality claim is made; upgrading this to a Ramsey-number equality would be
separate work.

## The induction

On `a + b`. At a chosen root of color `0`, apply the `(a - 1, b)` case inside each of the two
branches. If either branch returns the color-`1` alternative, that alternative already answers
the whole tree. Otherwise both branches return color-`0` subtrees of height `a`, and `fork`
attaches them under the root to give height `a + 1`. A root of color `1` is symmetric.

This is where the embedding conventions earn their keep. The two subtrees are found at unknown
depth inside the branches and are then attached under a shallower node, so the assembled
embedding sends its root below the host root and turns source edges into long host paths. An
embedding notion requiring either root or depth preservation would make this step impossible,
which is why neither is a field of `InternalEmbedding`.

## Statement shape

The heights appear as `a + 1`, `b + 1`, and `a + b + 1`, never as truncated subtraction. The
recursion is carried by an auxiliary indexed by the host height, so that the arithmetic relating
`a`, `b`, and the height lives in ordinary hypotheses rather than in types.

## The multicolor theorem

`binaryTreeRamsey` is the `m`-color form: subtree heights `t i + 1` for `t : Fin m → ℕ`, host
height `(∑ i, t i) + 1` (the successor of the sum — the parenthesization is load-bearing, and at
`m = 2`, `t = ![a, b]` it is `a + b + 1`). The recursion `ramsey_aux_multi` generalizes
`ramsey_aux`: at a root of color `c` with `t c = 0` the root alone answers; otherwise the entry
`t c` is shrunk by one with `Function.update` and both branches are recursed into — a branch
answering with a color other than `c` already answers at that color's full height, and two
branches answering with `c` are joined under the root by `fork`. The returned height travels as
an equation `k = t i + 1`, so the arithmetic of `Function.update` never enters a type. The
whole-tree form `binaryTreeRamsey_proper` and the equal-height form
`binaryTreeRamsey_proper_const` (host `m * t + 1`) follow. The two-color statements are
unchanged and recovered as a test.

## Provenance

N. Alon, R. Livni, M. Malliaris, S. Moran, *Private PAC learning implies finite Littlestone
dimension*, [arXiv:1806.00949](https://arxiv.org/abs/1806.00949), **Lemma 16**. Their statement
uses positive integers `p, q` and host height `p + q - 1`; substituting `p = a + 1` and
`q = b + 1` gives the `a + b + 1` here. The mathematics is theirs; the word-indexed formulation
and Lean proof are this repository's own.

`binaryTreeRamsey_two` is also the two-color specialization of G. Conant and C. Terry,
*Encoding orders and trees in real-valued functions*,
[arXiv:2607.21761](https://arxiv.org/abs/2607.21761), **Lemma 2.6**, the tree-Ramsey ingredient
used in their proof of Theorem 1.11. `binaryTreeRamsey` is a **reformulated variant** of their
Lemma 2.6: the coloring form of their cover statement (a cover `C₁ ∪ … ∪ C_m` of the internal
nodes becomes a coloring, so a cover with overlaps is handled by choosing one color per node),
with heights in successor form (`t i + 1`, host `(∑ i, t i) + 1`, their
`t = t₁ + … + t_m − m + 1`). The cover equivalence is not formalized, so the label stays
"reformulated variant". Theorem 1.11 is a downstream application, not a Ramsey statement.

See `PROVENANCE.md`.
-/

namespace RegularityLemmata

open InternalEmbedding

/-- A two-coloring of the internal nodes of a tree of height `h`. -/
abbrev BinaryTreeTwoColoring (h : ℕ) : Type := InternalNode h → Fin 2

private theorem fin_two_cases (c : Fin 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- The recursion, indexed by the **host height** rather than by `a + b`.

Keeping the height a single variable is what keeps every arithmetic fact about `a`, `b`, and the
height in a hypothesis instead of in a type: the branches of a height-`n + 1` tree have height
`n` definitionally, and the relation `a + b = n` is then an ordinary `Nat` equation that `omega`
discharges. -/
private theorem ramsey_aux : ∀ (n a b : ℕ), a + b = n → ∀ color : BinaryTreeTwoColoring (n + 1),
    (∃ e : InternalEmbedding (a + 1) (n + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (n + 1), ∀ x, color (e x) = 1) := by
  intro n
  induction n with
  | zero =>
      intro a b hab color
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      -- A height-one tree has exactly one internal node, its root.
      have hroot : ∀ x : InternalNode 1, x = root 0 := by
        intro x
        rcases internalNode_cases x with h | ⟨_, y, _⟩
        · exact h
        · exact absurd y.2 (by omega)
      rcases fin_two_cases (color (root 0)) with hc | hc
      · exact Or.inl ⟨InternalEmbedding.id 1, fun x => by rw [id_apply, hroot x]; exact hc⟩
      · exact Or.inr ⟨InternalEmbedding.id 1, fun x => by rw [id_apply, hroot x]; exact hc⟩
  | succ m ih =>
      intro a b hab color
      -- Assembling two branch embeddings under the root keeps a color that the root and both
      -- pieces already have.
      have hfork : ∀ (k : ℕ) (c : Fin 2) (F G : InternalEmbedding k (m + 1 + 1))
          (hf : ∀ y, BranchBelow false (root (m + 1)).1 (F y).1)
          (hg : ∀ y, BranchBelow true (root (m + 1)).1 (G y).1),
          color (root (m + 1)) = c → (∀ y, color (F y) = c) → (∀ y, color (G y) = c) →
          ∀ z, color (fork (root (m + 1)) F G hf hg z) = c := by
        intro k c F G hf hg hr hF hG z
        rcases internalNode_cases z with rfl | ⟨d, y, rfl⟩
        · rw [fork_root]; exact hr
        · rw [fork_cons]; cases d
          · simpa using hF y
          · simpa using hG y
      rcases a with _ | a' <;> rcases b with _ | b'
      · omega
      · -- `a = 0`: one color-`0` node suffices, and otherwise the whole tree is color `1`.
        obtain rfl : b' = m := by omega
        by_cases hex : ∃ x, color x = 0
        · obtain ⟨x, hx⟩ := hex
          exact Or.inl ⟨singleton x, fun y => by rw [singleton_apply]; exact hx⟩
        · push Not at hex
          refine Or.inr ⟨InternalEmbedding.id _, fun x => ?_⟩
          rw [id_apply]
          rcases fin_two_cases (color x) with hc | hc
          · exact absurd hc (hex x)
          · exact hc
      · -- `b = 0`: symmetric.
        obtain rfl : a' = m := by omega
        by_cases hex : ∃ x, color x = 1
        · obtain ⟨x, hx⟩ := hex
          exact Or.inr ⟨singleton x, fun y => by rw [singleton_apply]; exact hx⟩
        · push Not at hex
          refine Or.inl ⟨InternalEmbedding.id _, fun x => ?_⟩
          rw [id_apply]
          rcases fin_two_cases (color x) with hc | hc
          · exact hc
          · exact absurd hc (hex x)
      · -- Both heights positive: recurse into the two branches below the root.
        rcases fin_two_cases (color (root (m + 1))) with hr | hr
        · -- Root color `0`: shrink `a`.
          have hstep : ∀ d : Bool,
              (∃ e : InternalEmbedding (a' + 1) (m + 1),
                ∀ x, color (consInternal d (e x)) = 0) ∨
              (∃ e : InternalEmbedding (b' + 1 + 1) (m + 1),
                ∀ x, color (consInternal d (e x)) = 1) :=
            fun d => ih a' (b' + 1) (by omega) (fun y => color (consInternal d y))
          rcases hstep false with ⟨ef, hef⟩ | ⟨e, he⟩
          · rcases hstep true with ⟨eg, heg⟩ | ⟨e, he⟩
            · refine Or.inl ⟨fork (root (m + 1))
                (comp (branchLift (m + 1) false) ef) (comp (branchLift (m + 1) true) eg)
                (fun y => branchBelow_root_branchLift (m + 1) false (ef y))
                (fun y => branchBelow_root_branchLift (m + 1) true (eg y)), ?_⟩
              exact hfork _ 0 _ _ _ _ hr hef heg
            · exact Or.inr ⟨comp (branchLift (m + 1) true) e, he⟩
          · exact Or.inr ⟨comp (branchLift (m + 1) false) e, he⟩
        · -- Root color `1`: shrink `b`.
          have hstep : ∀ d : Bool,
              (∃ e : InternalEmbedding (a' + 1 + 1) (m + 1),
                ∀ x, color (consInternal d (e x)) = 0) ∨
              (∃ e : InternalEmbedding (b' + 1) (m + 1),
                ∀ x, color (consInternal d (e x)) = 1) :=
            fun d => ih (a' + 1) b' (by omega) (fun y => color (consInternal d y))
          rcases hstep false with ⟨e, he⟩ | ⟨ef, hef⟩
          · exact Or.inl ⟨comp (branchLift (m + 1) false) e, he⟩
          · rcases hstep true with ⟨e, he⟩ | ⟨eg, heg⟩
            · exact Or.inl ⟨comp (branchLift (m + 1) true) e, he⟩
            · refine Or.inr ⟨fork (root (m + 1))
                (comp (branchLift (m + 1) false) ef) (comp (branchLift (m + 1) true) eg)
                (fun y => branchBelow_root_branchLift (m + 1) false (ef y))
                (fun y => branchBelow_root_branchLift (m + 1) true (eg y)), ?_⟩
              exact hfork _ 1 _ _ _ _ hr hef heg

/-- **The additive two-color subtree theorem.**

Every two-coloring of the internal nodes of a tree of height `a + b + 1` admits either a
color-`0` subtree of height `a + 1` or a color-`1` subtree of height `b + 1`.

The subtrees are `InternalEmbedding` images: their roots may sit at any host node and their
edges may span many host levels, but branch direction is preserved. Both freedoms are used by
the proof and neither may be removed. -/
theorem binaryTreeRamsey_two (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + b + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (a + b + 1), ∀ x, color (e x) = 1) :=
  ramsey_aux (a + b) a b rfl color

/-- **The whole-tree form.** The monochromatic subtree can be taken with its leaves placed, so
what is exhibited is a copy of the full tree of the stated height and not only of its interior.

The coloring constrains only internal nodes, so the leaf placement is unconstrained; it is
supplied by `InternalEmbedding.extendProper`, whose restriction to the interior is the embedding
the previous theorem produces. -/
theorem binaryTreeRamsey_two_proper (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : ProperEmbedding (a + 1) (a + b + 1), ∀ x, color (e.internal x) = 0) ∨
    (∃ e : ProperEmbedding (b + 1) (a + b + 1), ∀ x, color (e.internal x) = 1) := by
  rcases binaryTreeRamsey_two a b color with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨extendProper e, he⟩
  · exact Or.inr ⟨extendProper e, he⟩

/-! ### The multicolor theorem (companion Lemma 2.6, coloring form) -/

/-- The multicolor recursion, indexed by the **host height**, generalizing `ramsey_aux`. The
subtree height is returned as a variable `k` with the equation `k = t i + 1` kept as a
hypothesis, so that the arithmetic never enters a type: the induction shrinks one entry of `t`
by `Function.update`, and the returned height is reconciled with `t i + 1` by rewriting the
equation, never the embedding. -/
private theorem ramsey_aux_multi : ∀ (n : ℕ) {m : ℕ} (t : Fin m → ℕ), ∑ i, t i = n →
    ∀ color : InternalNode (n + 1) → Fin m,
    ∃ (i : Fin m) (k : ℕ), k = t i + 1 ∧
      ∃ e : InternalEmbedding k (n + 1), ∀ x, color (e x) = i := by
  intro n
  induction n with
  | zero =>
      intro m t hsum color
      have hroot : ∀ x : InternalNode 1, x = root 0 := by
        intro x
        rcases internalNode_cases x with h | ⟨_, y, _⟩
        · exact h
        · exact absurd y.2 (by omega)
      -- The root's color picks the expert; every `t i` is `0`, so its height is `1`.
      have htc : t (color (root 0)) = 0 :=
        (Finset.sum_eq_zero_iff.mp hsum) _ (Finset.mem_univ _)
      exact ⟨color (root 0), 1, by omega, InternalEmbedding.id 1,
        fun x => by rw [id_apply, hroot x]⟩
  | succ n ih =>
      intro m t hsum color
      have hfork : ∀ (k : ℕ) (c : Fin m) (F G : InternalEmbedding k (n + 1 + 1))
          (hf : ∀ y, BranchBelow false (root (n + 1)).1 (F y).1)
          (hg : ∀ y, BranchBelow true (root (n + 1)).1 (G y).1),
          color (root (n + 1)) = c → (∀ y, color (F y) = c) → (∀ y, color (G y) = c) →
          ∀ z, color (fork (root (n + 1)) F G hf hg z) = c := by
        intro k c F G hf hg hr hF hG z
        rcases internalNode_cases z with rfl | ⟨d, y, rfl⟩
        · rw [fork_root]; exact hr
        · rw [fork_cons]; cases d
          · simpa using hF y
          · simpa using hG y
      set c := color (root (n + 1)) with hc
      rcases Nat.eq_zero_or_pos (t c) with h0 | hpos
      · -- The root's color asks for height one: the root alone.
        exact ⟨c, 1, by omega, singleton (root (n + 1)), fun y => by rw [singleton_apply]⟩
      · -- Shrink the root color's height by one and recurse into both branches.
        obtain ⟨t', ht'⟩ : ∃ t', t c = t' + 1 := ⟨t c - 1, by omega⟩
        set t'' := Function.update t c t' with ht''
        have hsum' : ∑ i, t'' i = n := by
          have h1 := Finset.sum_update_of_mem (Finset.mem_univ c) t (t c)
          rw [Function.update_eq_self] at h1
          have h2 := Finset.sum_update_of_mem (Finset.mem_univ c) t t'
          rw [ht'', h2]
          omega
        have hstep : ∀ d : Bool, ∃ (i : Fin m) (k : ℕ), k = t'' i + 1 ∧
            ∃ e : InternalEmbedding k (n + 1), ∀ x, color (consInternal d (e x)) = i :=
          fun d => ih t'' hsum' (fun y => color (consInternal d y))
        obtain ⟨i₀, k₀, hk₀, e₀, he₀⟩ := hstep false
        obtain ⟨i₁, k₁, hk₁, e₁, he₁⟩ := hstep true
        by_cases h₀ : i₀ = c
        · by_cases h₁ : i₁ = c
          · -- Both branches answer with the root's color: fork under the root.
            have hk : k₀ = t' + 1 := by rw [hk₀, h₀, ht'', Function.update_self]
            have hk' : k₁ = t' + 1 := by rw [hk₁, h₁, ht'', Function.update_self]
            subst hk hk'
            exact ⟨c, t' + 1 + 1, by omega, fork (root (n + 1))
              (comp (branchLift (n + 1) false) e₀) (comp (branchLift (n + 1) true) e₁)
              (fun y => branchBelow_root_branchLift (n + 1) false (e₀ y))
              (fun y => branchBelow_root_branchLift (n + 1) true (e₁ y)),
              hfork _ c _ _ _ _ hc.symm (fun y => (he₀ y).trans h₀) (fun y => (he₁ y).trans h₁)⟩
          · -- The true branch answers with another color, at that color's full height.
            exact ⟨i₁, k₁, by rw [hk₁, ht'', Function.update_of_ne h₁],
              comp (branchLift (n + 1) true) e₁, he₁⟩
        · exact ⟨i₀, k₀, by rw [hk₀, ht'', Function.update_of_ne h₀],
            comp (branchLift (n + 1) false) e₀, he₀⟩

/-- **The multicolor subtree theorem** — companion Lemma 2.6 in coloring form. An `m`-coloring
of the internal nodes of a tree of height `(∑ i, t i) + 1` admits, for some color `i`, a
color-`i` subtree of height `t i + 1`. The parenthesization of the host height is load-bearing:
it is the successor of the sum, matching `a + b + 1` at `m = 2`. -/
theorem binaryTreeRamsey (m : ℕ) (t : Fin m → ℕ)
    (color : InternalNode ((∑ i, t i) + 1) → Fin m) :
    ∃ (i : Fin m) (e : InternalEmbedding (t i + 1) ((∑ i, t i) + 1)),
      ∀ x, color (e x) = i := by
  obtain ⟨i, k, hk, e, he⟩ := ramsey_aux_multi (∑ i, t i) t rfl color
  subst hk
  exact ⟨i, e, he⟩

/-- **The multicolor whole-tree form**: the monochromatic subtree with its leaves placed, via
`InternalEmbedding.extendProper` as in `binaryTreeRamsey_two_proper`. -/
theorem binaryTreeRamsey_proper (m : ℕ) (t : Fin m → ℕ)
    (color : InternalNode ((∑ i, t i) + 1) → Fin m) :
    ∃ (i : Fin m) (e : ProperEmbedding (t i + 1) ((∑ i, t i) + 1)),
      ∀ x, color (e.internal x) = i := by
  obtain ⟨i, e, he⟩ := binaryTreeRamsey m t color
  exact ⟨i, extendProper e, he⟩

/-- **Equal heights**: `m` colors, every subtree of height `t + 1`, host height `m * t + 1`.
Stated at the host height `m * t + 1` directly (the recursion is entered with `∑ i : Fin m, t =
m * t` as a hypothesis, so no coloring is transported along that identity). -/
theorem binaryTreeRamsey_proper_const (m t : ℕ) (color : InternalNode (m * t + 1) → Fin m) :
    ∃ (c : Fin m) (e : ProperEmbedding (t + 1) (m * t + 1)), ∀ x, color (e.internal x) = c := by
  obtain ⟨c, k, hk, e, he⟩ := ramsey_aux_multi (m * t) (fun _ : Fin m => t)
    (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]) color
  subst hk
  exact ⟨c, extendProper e, he⟩

/-! ### Tests -/

section Tests

-- **`a = b = 0`.** Host height one: the single root is one color or the other, and the answer
-- is a height-one subtree of that color.
example (color : BinaryTreeTwoColoring 1) :
    (∃ e : InternalEmbedding 1 1, ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 1, ∀ x, color (e x) = 1) :=
  binaryTreeRamsey_two 0 0 color

-- **`a = 0`.** Either some node is color `0`, or the whole tree of height `b + 1` is color
-- `1`.
--
-- Stated the way a consumer would hold it, at height `b + 1`. Instantiating the theorem at
-- `a = 0` gives host height `0 + b + 1`, and `0 + b` is *not* definitionally `b`, because `Nat`
-- addition recurses on its second argument. So the conversion is a real step.
--
-- It is **not** a `simp [Nat.zero_add]` step. The height occurs in the type of the bound
-- coloring, which the body then depends on, so rewriting it would require transporting that
-- body — a cast `simp` will not build, and it reports no progress. What a consumer must do
-- instead is what is written out here: restrict the coloring along the height inequality on
-- the way in, and rebuild the embedding on the way out. Both directions are `omega` on lengths
-- plus proof irrelevance, and nothing about the branch law changes.
example (b : ℕ) (color : BinaryTreeTwoColoring (b + 1)) :
    (∃ e : InternalEmbedding 1 (b + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (b + 1), ∀ x, color (e x) = 1) := by
  have hnode : ∀ x : InternalNode (0 + b + 1), x.1.length < b + 1 := fun x => by
    have := x.2; omega
  rcases binaryTreeRamsey_two 0 b (fun x => color ⟨x.1, hnode x⟩) with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩
  · exact Or.inr ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩

-- **`b = 0`.** The mirror statement.
example (a : ℕ) (color : BinaryTreeTwoColoring (a + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 (a + 1), ∀ x, color (e x) = 1) :=
  binaryTreeRamsey_two a 0 color

-- **Host height one**, stated directly at the numeral rather than through `a + b + 1`.
example (color : BinaryTreeTwoColoring 1) :
    (∃ e : InternalEmbedding 1 1, ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 1, ∀ x, color (e x) = 1) :=
  binaryTreeRamsey_two 0 0 color

-- **A concrete coloring at host height two.** The root is color `0` and both nodes below it
-- are color `1`. Host height two is `a + b + 1` with `a = 0`, `b = 1`; the coloring is not
-- constant, so the statement is not answered by a trivial whole-tree embedding at either color.
private def sampleColor : BinaryTreeTwoColoring 2 := fun x => if x.1 = [] then 0 else 1

example : sampleColor (root 1) = 0 := by decide
example : sampleColor (consInternal true (⟨[], by decide⟩ : InternalNode 1)) = 1 := by decide

example :
    (∃ e : InternalEmbedding 1 2, ∀ x, sampleColor (e x) = 0) ∨
    (∃ e : InternalEmbedding 2 2, ∀ x, sampleColor (e x) = 1) :=
  binaryTreeRamsey_two 0 1 sampleColor

/-- The constant colorings, used to exercise both root colors. -/
private def constColor (h : ℕ) (c : Fin 2) : BinaryTreeTwoColoring h := fun _ => c

-- **Both root colors are covered**, at the smallest host height where the root has a choice:
-- the constantly-`0` and constantly-`1` colorings of a height-two tree both resolve.
example :
    (∃ e : InternalEmbedding 2 2, ∀ x, constColor 2 0 (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 2, ∀ x, constColor 2 0 (e x) = 1) :=
  binaryTreeRamsey_two 1 0 (constColor 2 0)

example :
    (∃ e : InternalEmbedding 1 2, ∀ x, constColor 2 1 (e x) = 0) ∨
    (∃ e : InternalEmbedding 2 2, ∀ x, constColor 2 1 (e x) = 1) :=
  binaryTreeRamsey_two 0 1 (constColor 2 1)

-- **The whole-tree form**, whose leaf placement comes from `extendProper`. Restricting it
-- returns the interior embedding, so the two forms agree where they overlap.
example (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : ProperEmbedding (a + 1) (a + b + 1), ∀ x, color (e.internal x) = 0) ∨
    (∃ e : ProperEmbedding (b + 1) (a + b + 1), ∀ x, color (e.internal x) = 1) :=
  binaryTreeRamsey_two_proper a b color

example (a b : ℕ) (e : InternalEmbedding a b) : (extendProper e).toInternal = e :=
  extendProper_toInternal e

/-! #### The multicolor theorem -/

-- **`m = 2` recovers the two-color theorem through the public API.** With `t = ![a, b]` the
-- host height is `(∑ i, ![a, b] i) + 1`, which is `a + b + 1` after `Fin.sum_univ_two` but not
-- definitionally so; the coloring is restricted along the height identity on the way in and
-- the embedding rebuilt on the way out (`omega` on lengths plus proof irrelevance), exactly as
-- the `a = 0` example above does. The source heights `![a, b] 0 + 1` and `![a, b] 1 + 1` are
-- `a + 1` and `b + 1` definitionally.
example (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + b + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (a + b + 1), ∀ x, color (e x) = 1) := by
  have hsum : (∑ i, ![a, b] i) = a + b := by simp [Fin.sum_univ_two]
  have hnode : ∀ x : InternalNode ((∑ i, ![a, b] i) + 1), x.1.length < a + b + 1 :=
    fun x => by have := x.2; omega
  obtain ⟨i, e, he⟩ := binaryTreeRamsey 2 ![a, b] (fun x => color ⟨x.1, hnode x⟩)
  rcases fin_two_cases i with rfl | rfl
  · exact Or.inl ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩
  · exact Or.inr ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩

-- **The whole-tree form is recovered the same way** from `binaryTreeRamsey_proper`: leaves are
-- transported along the height identity as well (a leaf of the host of height
-- `(∑ i, ![a, b] i) + 1` has length exactly `a + b + 1`).
example (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : ProperEmbedding (a + 1) (a + b + 1), ∀ x, color (e.internal x) = 0) ∨
    (∃ e : ProperEmbedding (b + 1) (a + b + 1), ∀ x, color (e.internal x) = 1) := by
  have hsum : (∑ i, ![a, b] i) = a + b := by simp [Fin.sum_univ_two]
  have hnode : ∀ x : InternalNode ((∑ i, ![a, b] i) + 1), x.1.length < a + b + 1 :=
    fun x => by have := x.2; omega
  have hleaf : ∀ l : LeafNode ((∑ i, ![a, b] i) + 1), l.1.length = a + b + 1 :=
    fun l => by have := l.2; omega
  obtain ⟨i, e, he⟩ := binaryTreeRamsey_proper 2 ![a, b] (fun x => color ⟨x.1, hnode x⟩)
  rcases fin_two_cases i with rfl | rfl
  · exact Or.inl ⟨⟨fun x => ⟨(e.internal x).1, hnode _⟩, fun l => ⟨(e.leaf l).1, hleaf _⟩,
      fun d x y h => e.branch_internal d x y h, fun d x l h => e.branch_leaf d x l h⟩, he⟩
  · exact Or.inr ⟨⟨fun x => ⟨(e.internal x).1, hnode _⟩, fun l => ⟨(e.leaf l).1, hleaf _⟩,
      fun d x y h => e.branch_internal d x y h, fun d x l h => e.branch_leaf d x l h⟩, he⟩

-- The private recursion agrees with the two-color theorem's disjunction directly, without any
-- height transport: entered at `n = a + b`, the returned height rewrites to `a + 1` or `b + 1`.
example (a b : ℕ) (color : BinaryTreeTwoColoring (a + b + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + b + 1), ∀ x, color (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (a + b + 1), ∀ x, color (e x) = 1) := by
  obtain ⟨i, k, hk, e, he⟩ := ramsey_aux_multi (a + b) ![a, b] (by simp [Fin.sum_univ_two]) color
  rcases fin_two_cases i with rfl | rfl
  · simp only [Matrix.cons_val_zero] at hk
    subst hk
    exact Or.inl ⟨e, he⟩
  · simp only [Matrix.cons_val_one] at hk
    subst hk
    exact Or.inr ⟨e, he⟩

-- **Three colors, host height `3 · 1 + 1 = 4`**: some color carries a proper subtree of
-- height `2`.
example (color : InternalNode (3 * 1 + 1) → Fin 3) :
    ∃ (c : Fin 3) (e : ProperEmbedding 2 (3 * 1 + 1)), ∀ x, color (e.internal x) = c :=
  binaryTreeRamsey_proper_const 3 1 color

-- **`t = 0` in the constant form**: host height `m * 0 + 1`, the root alone, of some color.
example (m : ℕ) (color : InternalNode (m * 0 + 1) → Fin m) :
    ∃ (c : Fin m) (e : ProperEmbedding 1 (m * 0 + 1)), ∀ x, color (e.internal x) = c :=
  binaryTreeRamsey_proper_const m 0 color

-- **`m = 0` is vacuous**: the host root exists, so there is no coloring into `Fin 0` at all.
example (t : Fin 0 → ℕ) (color : InternalNode ((∑ i, t i) + 1) → Fin 0) : False :=
  (color (root _)).elim0

-- **`m = 1`: existence at equal heights.** One color, so the subtree height `t + 1` equals
-- the host height; the theorem asserts existence of some embedding of that height.
example (t : ℕ) (color : InternalNode ((∑ i : Fin 1, ![t] i) + 1) → Fin 1) :
    ∃ (i : Fin 1) (e : InternalEmbedding (![t] i + 1) ((∑ i : Fin 1, ![t] i) + 1)),
      ∀ x, color (e x) = i :=
  binaryTreeRamsey 1 ![t] color

-- **`m = 1`: the identity embedding is a witness**, exhibited separately: with one color every
-- node has it, so `InternalEmbedding.id` is monochromatic at the only color.
example (h : ℕ) (color : InternalNode h → Fin 1) :
    ∀ x, color (InternalEmbedding.id h x) = 0 :=
  fun _ => Subsingleton.elim _ _

-- **A concrete three-coloring** of the height-`4` tree by depth modulo `3`: not constant, so
-- the theorem is not answered by a whole-tree embedding at any color.
private def depthColor : InternalNode (3 * 1 + 1) → Fin 3 := fun x => ⟨x.1.length % 3, by omega⟩

example : depthColor (root 3) = 0 := by decide
example : depthColor (consInternal true (root 2)) = 1 := by decide
example : ∃ (c : Fin 3) (e : ProperEmbedding 2 (3 * 1 + 1)),
    ∀ x, depthColor (e.internal x) = c :=
  binaryTreeRamsey_proper_const 3 1 depthColor

end Tests

end RegularityLemmata
