/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.BinaryTreeProperEmbedding

/-!
# The additive two-colour subtree theorem

Two-colour the internal nodes of a full binary tree of height `a + b + 1`. Then it contains
either a colour-`0` subtree of height `a + 1` or a colour-`1` subtree of height `b + 1`, where
"subtree" means the image of an `InternalEmbedding`: arbitrary root, branch direction preserved,
depth unconstrained.

## A precise upper theorem, without an optimality claim

The theorem states the explicit height `a + b + 1`. No matching lower-bound colouring is
formalized, so no optimality claim is made; upgrading this to a Ramsey-number equality would be
separate work.

## The induction

On `a + b`. At a chosen root of colour `0`, apply the `(a - 1, b)` case inside each of the two
branches. If either branch returns the colour-`1` alternative, that alternative already answers
the whole tree. Otherwise both branches return colour-`0` subtrees of height `a`, and `fork`
attaches them under the root to give height `a + 1`. A root of colour `1` is symmetric.

This is where the embedding conventions earn their keep. The two subtrees are found at unknown
depth inside the branches and are then attached under a shallower node, so the assembled
embedding sends its root below the host root and turns source edges into long host paths. An
embedding notion requiring either root or depth preservation would make this step impossible,
which is why neither is a field of `InternalEmbedding`.

## Statement shape

The heights appear as `a + 1`, `b + 1`, and `a + b + 1`, never as truncated subtraction. The
recursion is carried by an auxiliary indexed by the host height, so that the arithmetic relating
`a`, `b`, and the height lives in ordinary hypotheses rather than in types.

## Provenance

N. Alon, R. Livni, M. Malliaris, S. Moran, *Private PAC learning implies finite Littlestone
dimension*, [arXiv:1806.00949](https://arxiv.org/abs/1806.00949), **Lemma 16**. Their statement
uses positive integers `p, q` and host height `p + q - 1`; substituting `p = a + 1` and
`q = b + 1` gives the `a + b + 1` here. The mathematics is theirs; the word-indexed formulation
and Lean proof are this repository's own. See `PROVENANCE.md`.
-/

namespace RegularityLemmata

open InternalEmbedding

/-- A two-colouring of the internal nodes of a tree of height `h`. -/
abbrev BinaryTreeTwoColouring (h : ℕ) : Type := InternalNode h → Fin 2

private theorem fin_two_cases (c : Fin 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- The recursion, indexed by the **host height** rather than by `a + b`.

Keeping the height a single variable is what keeps every arithmetic fact about `a`, `b`, and the
height in a hypothesis instead of in a type: the branches of a height-`n + 1` tree have height
`n` definitionally, and the relation `a + b = n` is then an ordinary `Nat` equation that `omega`
discharges. -/
private theorem ramsey_aux : ∀ (n a b : ℕ), a + b = n → ∀ colour : BinaryTreeTwoColouring (n + 1),
    (∃ e : InternalEmbedding (a + 1) (n + 1), ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (n + 1), ∀ x, colour (e x) = 1) := by
  intro n
  induction n with
  | zero =>
      intro a b hab colour
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      -- A height-one tree has exactly one internal node, its root.
      have hroot : ∀ x : InternalNode 1, x = root 0 := by
        intro x
        rcases internalNode_cases x with h | ⟨_, y, _⟩
        · exact h
        · exact absurd y.2 (by omega)
      rcases fin_two_cases (colour (root 0)) with hc | hc
      · exact Or.inl ⟨InternalEmbedding.id 1, fun x => by rw [id_apply, hroot x]; exact hc⟩
      · exact Or.inr ⟨InternalEmbedding.id 1, fun x => by rw [id_apply, hroot x]; exact hc⟩
  | succ m ih =>
      intro a b hab colour
      -- Assembling two branch embeddings under the root keeps a colour that the root and both
      -- pieces already have.
      have hfork : ∀ (k : ℕ) (c : Fin 2) (F G : InternalEmbedding k (m + 1 + 1))
          (hf : ∀ y, BranchBelow false (root (m + 1)).1 (F y).1)
          (hg : ∀ y, BranchBelow true (root (m + 1)).1 (G y).1),
          colour (root (m + 1)) = c → (∀ y, colour (F y) = c) → (∀ y, colour (G y) = c) →
          ∀ z, colour (fork (root (m + 1)) F G hf hg z) = c := by
        intro k c F G hf hg hr hF hG z
        rcases internalNode_cases z with rfl | ⟨d, y, rfl⟩
        · rw [fork_root]; exact hr
        · rw [fork_cons]; cases d
          · simpa using hF y
          · simpa using hG y
      rcases a with _ | a' <;> rcases b with _ | b'
      · omega
      · -- `a = 0`: one colour-`0` node suffices, and otherwise the whole tree is colour `1`.
        obtain rfl : b' = m := by omega
        by_cases hex : ∃ x, colour x = 0
        · obtain ⟨x, hx⟩ := hex
          exact Or.inl ⟨singleton x, fun y => by rw [singleton_apply]; exact hx⟩
        · push Not at hex
          refine Or.inr ⟨InternalEmbedding.id _, fun x => ?_⟩
          rw [id_apply]
          rcases fin_two_cases (colour x) with hc | hc
          · exact absurd hc (hex x)
          · exact hc
      · -- `b = 0`: symmetric.
        obtain rfl : a' = m := by omega
        by_cases hex : ∃ x, colour x = 1
        · obtain ⟨x, hx⟩ := hex
          exact Or.inr ⟨singleton x, fun y => by rw [singleton_apply]; exact hx⟩
        · push Not at hex
          refine Or.inl ⟨InternalEmbedding.id _, fun x => ?_⟩
          rw [id_apply]
          rcases fin_two_cases (colour x) with hc | hc
          · exact hc
          · exact absurd hc (hex x)
      · -- Both heights positive: recurse into the two branches below the root.
        rcases fin_two_cases (colour (root (m + 1))) with hr | hr
        · -- Root colour `0`: shrink `a`.
          have hstep : ∀ d : Bool,
              (∃ e : InternalEmbedding (a' + 1) (m + 1),
                ∀ x, colour (consInternal d (e x)) = 0) ∨
              (∃ e : InternalEmbedding (b' + 1 + 1) (m + 1),
                ∀ x, colour (consInternal d (e x)) = 1) :=
            fun d => ih a' (b' + 1) (by omega) (fun y => colour (consInternal d y))
          rcases hstep false with ⟨ef, hef⟩ | ⟨e, he⟩
          · rcases hstep true with ⟨eg, heg⟩ | ⟨e, he⟩
            · refine Or.inl ⟨fork (root (m + 1))
                (comp (branchLift (m + 1) false) ef) (comp (branchLift (m + 1) true) eg)
                (fun y => branchBelow_root_branchLift (m + 1) false (ef y))
                (fun y => branchBelow_root_branchLift (m + 1) true (eg y)), ?_⟩
              exact hfork _ 0 _ _ _ _ hr hef heg
            · exact Or.inr ⟨comp (branchLift (m + 1) true) e, he⟩
          · exact Or.inr ⟨comp (branchLift (m + 1) false) e, he⟩
        · -- Root colour `1`: shrink `b`.
          have hstep : ∀ d : Bool,
              (∃ e : InternalEmbedding (a' + 1 + 1) (m + 1),
                ∀ x, colour (consInternal d (e x)) = 0) ∨
              (∃ e : InternalEmbedding (b' + 1) (m + 1),
                ∀ x, colour (consInternal d (e x)) = 1) :=
            fun d => ih (a' + 1) b' (by omega) (fun y => colour (consInternal d y))
          rcases hstep false with ⟨e, he⟩ | ⟨ef, hef⟩
          · exact Or.inl ⟨comp (branchLift (m + 1) false) e, he⟩
          · rcases hstep true with ⟨e, he⟩ | ⟨eg, heg⟩
            · exact Or.inl ⟨comp (branchLift (m + 1) true) e, he⟩
            · refine Or.inr ⟨fork (root (m + 1))
                (comp (branchLift (m + 1) false) ef) (comp (branchLift (m + 1) true) eg)
                (fun y => branchBelow_root_branchLift (m + 1) false (ef y))
                (fun y => branchBelow_root_branchLift (m + 1) true (eg y)), ?_⟩
              exact hfork _ 1 _ _ _ _ hr hef heg

/-- **The additive two-colour subtree theorem.**

Every two-colouring of the internal nodes of a tree of height `a + b + 1` admits either a
colour-`0` subtree of height `a + 1` or a colour-`1` subtree of height `b + 1`.

The subtrees are `InternalEmbedding` images: their roots may sit at any host node and their
edges may span many host levels, but branch direction is preserved. Both freedoms are used by
the proof and neither may be removed. -/
theorem binaryTreeRamsey_two (a b : ℕ) (colour : BinaryTreeTwoColouring (a + b + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + b + 1), ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (a + b + 1), ∀ x, colour (e x) = 1) :=
  ramsey_aux (a + b) a b rfl colour

/-- **The whole-tree form.** The monochromatic subtree can be taken with its leaves placed, so
what is exhibited is a copy of the full tree of the stated height and not only of its interior.

The colouring constrains only internal nodes, so the leaf placement is unconstrained; it is
supplied by `InternalEmbedding.extendProper`, whose restriction to the interior is the embedding
the previous theorem produces. -/
theorem binaryTreeRamsey_two_proper (a b : ℕ) (colour : BinaryTreeTwoColouring (a + b + 1)) :
    (∃ e : ProperEmbedding (a + 1) (a + b + 1), ∀ x, colour (e.internal x) = 0) ∨
    (∃ e : ProperEmbedding (b + 1) (a + b + 1), ∀ x, colour (e.internal x) = 1) := by
  rcases binaryTreeRamsey_two a b colour with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨extendProper e, he⟩
  · exact Or.inr ⟨extendProper e, he⟩

/-! ### Tests -/

section Tests

-- **`a = b = 0`.** Host height one: the single root is one colour or the other, and the answer
-- is a height-one subtree of that colour.
example (colour : BinaryTreeTwoColouring 1) :
    (∃ e : InternalEmbedding 1 1, ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 1, ∀ x, colour (e x) = 1) :=
  binaryTreeRamsey_two 0 0 colour

-- **`a = 0`.** Either some node is colour `0`, or the whole tree of height `b + 1` is colour
-- `1`.
--
-- Stated the way a consumer would hold it, at height `b + 1`. Instantiating the theorem at
-- `a = 0` gives host height `0 + b + 1`, and `0 + b` is *not* definitionally `b`, because `Nat`
-- addition recurses on its second argument. So the conversion is a real step.
--
-- It is **not** a `simp [Nat.zero_add]` step. The height occurs in the type of the bound
-- colouring, which the body then depends on, so rewriting it would require transporting that
-- body — a cast `simp` will not build, and it reports no progress. What a consumer must do
-- instead is what is written out here: restrict the colouring along the height inequality on
-- the way in, and rebuild the embedding on the way out. Both directions are `omega` on lengths
-- plus proof irrelevance, and nothing about the branch law changes.
example (b : ℕ) (colour : BinaryTreeTwoColouring (b + 1)) :
    (∃ e : InternalEmbedding 1 (b + 1), ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding (b + 1) (b + 1), ∀ x, colour (e x) = 1) := by
  have hnode : ∀ x : InternalNode (0 + b + 1), x.1.length < b + 1 := fun x => by
    have := x.2; omega
  rcases binaryTreeRamsey_two 0 b (fun x => colour ⟨x.1, hnode x⟩) with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩
  · exact Or.inr ⟨⟨fun x => ⟨(e x).1, hnode (e x)⟩, fun d x y h => e.branch d x y h⟩, he⟩

-- **`b = 0`.** The mirror statement.
example (a : ℕ) (colour : BinaryTreeTwoColouring (a + 1)) :
    (∃ e : InternalEmbedding (a + 1) (a + 1), ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 (a + 1), ∀ x, colour (e x) = 1) :=
  binaryTreeRamsey_two a 0 colour

-- **Host height one**, stated directly at the numeral rather than through `a + b + 1`.
example (colour : BinaryTreeTwoColouring 1) :
    (∃ e : InternalEmbedding 1 1, ∀ x, colour (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 1, ∀ x, colour (e x) = 1) :=
  binaryTreeRamsey_two 0 0 colour

-- **A concrete colouring at host height two.** The root is colour `0` and both nodes below it
-- are colour `1`. Host height two is `a + b + 1` with `a = 0`, `b = 1`; the colouring is not
-- constant, so the statement is not answered by a trivial whole-tree embedding at either colour.
private def sampleColour : BinaryTreeTwoColouring 2 := fun x => if x.1 = [] then 0 else 1

example : sampleColour (root 1) = 0 := by decide
example : sampleColour (consInternal true (⟨[], by decide⟩ : InternalNode 1)) = 1 := by decide

example :
    (∃ e : InternalEmbedding 1 2, ∀ x, sampleColour (e x) = 0) ∨
    (∃ e : InternalEmbedding 2 2, ∀ x, sampleColour (e x) = 1) :=
  binaryTreeRamsey_two 0 1 sampleColour

/-- The constant colourings, used to exercise both root colours. -/
private def constColour (h : ℕ) (c : Fin 2) : BinaryTreeTwoColouring h := fun _ => c

-- **Both root colours are covered**, at the smallest host height where the root has a choice:
-- the constantly-`0` and constantly-`1` colourings of a height-two tree both resolve.
example :
    (∃ e : InternalEmbedding 2 2, ∀ x, constColour 2 0 (e x) = 0) ∨
    (∃ e : InternalEmbedding 1 2, ∀ x, constColour 2 0 (e x) = 1) :=
  binaryTreeRamsey_two 1 0 (constColour 2 0)

example :
    (∃ e : InternalEmbedding 1 2, ∀ x, constColour 2 1 (e x) = 0) ∨
    (∃ e : InternalEmbedding 2 2, ∀ x, constColour 2 1 (e x) = 1) :=
  binaryTreeRamsey_two 0 1 (constColour 2 1)

-- **The whole-tree form**, whose leaf placement comes from `extendProper`. Restricting it
-- returns the interior embedding, so the two forms agree where they overlap.
example (a b : ℕ) (colour : BinaryTreeTwoColouring (a + b + 1)) :
    (∃ e : ProperEmbedding (a + 1) (a + b + 1), ∀ x, colour (e.internal x) = 0) ∨
    (∃ e : ProperEmbedding (b + 1) (a + b + 1), ∀ x, colour (e.internal x) = 1) :=
  binaryTreeRamsey_two_proper a b colour

example (a b : ℕ) (e : InternalEmbedding a b) : (extendProper e).toInternal = e :=
  extendProper_toInternal e

end Tests

end RegularityLemmata
