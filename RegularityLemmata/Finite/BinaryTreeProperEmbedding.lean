/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.BinaryTreeEmbedding

/-!
# Proper embeddings: covering the leaf level

An `InternalEmbedding` places the internal nodes of one tree inside another. A **proper
embedding** additionally sends every source **leaf** to a host leaf — a word of length exactly
the host height — subject to the same branch law. A proper embedding therefore places a whole
tree, not just its interior.

## Why the two levels are separate

A colouring lives on internal nodes, so recursive constructions produce internal embeddings.
But a *tree of height `h`* is only exhibited once its leaves are placed too. `extendProper` is
the bridge: every internal embedding extends, and the extension restricts back to the embedding
it came from.

## The extension, and why it needs no spare height

Each source leaf `l` of positive length splits as `w ++ [b]`, where `w` is an internal node of
the source. Its image is the canonical leaf below the `b`-child of `e w`: enter that child, then
pad with `false` up to the host height. The padding is always available because `e w` is
*internal*, so `(e w).1 ++ [b]` has length at most the host height.

No common-level or spare-height hypothesis is required, and none is hidden in a side condition.
Entering the branch first is what makes that true: a construction that placed the leaf image
somewhere below `e w` without committing to the `b`-child would have needed room to spare.

## Height zero is a different case, not a degenerate one

`InternalNode 0` is empty while `LeafNode 0` holds the empty word, so a height-zero tree is a
single leaf with no interior. The extension has nothing to read there — no last letter, and no
internal node to place it under — so it takes the canonical all-`false` leaf. That is an
explicit branch of the definition, not a general formula that happens to work.
-/

namespace RegularityLemmata

variable {s t : ℕ}

/-! ### Padding a word out to the host height -/

/-- Extend a word to length `t` with `false`s. Total: a word already that long is returned
unchanged, which does not occur at the call sites here. -/
def padTo (t : ℕ) (w : List Bool) : List Bool := w ++ List.replicate (t - w.length) false

theorem padTo_length {t : ℕ} {w : List Bool} (h : w.length ≤ t) : (padTo t w).length = t := by
  rw [padTo, List.length_append, List.length_replicate]
  omega

theorem prefix_padTo (t : ℕ) (w : List Bool) : w <+: padTo t w := List.prefix_append _ _

@[simp] theorem padTo_nil (t : ℕ) : padTo t [] = List.replicate t false := by simp [padTo]

/-! ### Proper embeddings -/

/-- An embedding of a whole height-`s` tree into a height-`t` tree: internal nodes to internal
nodes, leaves to leaves, preserving branch direction in both cases.

As with `InternalEmbedding`, nothing requires roots or depths to be preserved. -/
structure ProperEmbedding (s t : ℕ) where
  /-- The action on internal nodes. -/
  internal : InternalNode s → InternalNode t
  /-- The action on leaves. A source leaf lands on a host leaf, hence at the host's full
  height. -/
  leaf : LeafNode s → LeafNode t
  /-- Branch direction is preserved between internal nodes. -/
  branch_internal : ∀ (b : Bool) (x y : InternalNode s),
    BranchBelow b x.1 y.1 → BranchBelow b (internal x).1 (internal y).1
  /-- Branch direction is preserved from an internal node down to a leaf. -/
  branch_leaf : ∀ (b : Bool) (x : InternalNode s) (l : LeafNode s),
    BranchBelow b x.1 l.1 → BranchBelow b (internal x).1 (leaf l).1

namespace ProperEmbedding

/-- **Restriction to the interior.** -/
def toInternal (e : ProperEmbedding s t) : InternalEmbedding s t :=
  ⟨e.internal, e.branch_internal⟩

@[simp] theorem toInternal_apply (e : ProperEmbedding s t) (x : InternalNode s) :
    e.toInternal x = e.internal x := rfl

theorem ext {e₁ e₂ : ProperEmbedding s t} (hi : ∀ x, e₁.internal x = e₂.internal x)
    (hl : ∀ l, e₁.leaf l = e₂.leaf l) : e₁ = e₂ := by
  cases e₁; cases e₂; congr 1
  · exact funext hi
  · exact funext hl

/-- **The leaf-height equation.** A source leaf's image sits at exactly the host height, not
merely at some length that is large enough. -/
@[simp] theorem length_leaf (e : ProperEmbedding s t) (l : LeafNode s) :
    (e.leaf l).1.length = t := (e.leaf l).2

/-- An internal image sits strictly below the host height. -/
@[simp] theorem length_internal (e : ProperEmbedding s t) (x : InternalNode s) :
    (e.internal x).1.length < t := (e.internal x).2

/-! ### Identity and composition -/

/-- The identity proper embedding. -/
def id (s : ℕ) : ProperEmbedding s s where
  internal := _root_.id
  leaf := _root_.id
  branch_internal _ _ _ h := h
  branch_leaf _ _ _ h := h

@[simp] theorem id_internal (x : InternalNode s) : (id s).internal x = x := rfl

@[simp] theorem id_leaf (l : LeafNode s) : (id s).leaf l = l := rfl

@[simp] theorem toInternal_id (s : ℕ) : (id s).toInternal = InternalEmbedding.id s := rfl

/-- Composition. Both levels compose, and the leaf law composes through the internal one. -/
def comp {u : ℕ} (g : ProperEmbedding t u) (f : ProperEmbedding s t) : ProperEmbedding s u where
  internal x := g.internal (f.internal x)
  leaf l := g.leaf (f.leaf l)
  branch_internal b x y h := g.branch_internal b _ _ (f.branch_internal b x y h)
  branch_leaf b x l h := g.branch_leaf b _ _ (f.branch_leaf b x l h)

@[simp] theorem comp_internal {u : ℕ} (g : ProperEmbedding t u) (f : ProperEmbedding s t)
    (x : InternalNode s) : (comp g f).internal x = g.internal (f.internal x) := rfl

@[simp] theorem comp_leaf {u : ℕ} (g : ProperEmbedding t u) (f : ProperEmbedding s t)
    (l : LeafNode s) : (comp g f).leaf l = g.leaf (f.leaf l) := rfl

@[simp] theorem comp_id (f : ProperEmbedding s t) : comp f (id s) = f := ext (fun _ => rfl)
  (fun _ => rfl)

@[simp] theorem id_comp (f : ProperEmbedding s t) : comp (id t) f = f := ext (fun _ => rfl)
  (fun _ => rfl)

/-- Restriction is functorial: restricting a composite gives the composite of the
restrictions. -/
@[simp] theorem toInternal_comp {u : ℕ} (g : ProperEmbedding t u) (f : ProperEmbedding s t) :
    (comp g f).toInternal = InternalEmbedding.comp g.toInternal f.toInternal := rfl

/-! ### Injectivity and direction preservation -/

theorem internal_injective (e : ProperEmbedding s t) : Function.Injective e.internal :=
  e.toInternal.injective

/-- Branch direction from an internal node to a leaf, restated under the name it is searched
for. -/
theorem branch_leaf_preserved (e : ProperEmbedding s t) (b : Bool) (x : InternalNode s)
    (l : LeafNode s) (h : BranchBelow b x.1 l.1) :
    BranchBelow b (e.internal x).1 (e.leaf l).1 := e.branch_leaf b x l h

/-- **Leaves stay distinct**, and this is a theorem rather than a hypothesis: two distinct
leaves of the same height separate through opposite turns below a common internal node, and the
branch law keeps their images in the two disjoint branches below that node's image. -/
theorem leaf_injective (e : ProperEmbedding s t) : Function.Injective e.leaf := by
  intro l₁ l₂ hl
  by_contra hne
  have hne' : l₁.1 ≠ l₂.1 := fun h => hne (Subtype.ext h)
  have hlen : l₁.1.length = l₂.1.length := by rw [l₁.2, l₂.2]
  rcases prefix_trichotomy l₁.1 l₂.1 with hp | hp | ⟨z, b, h1, h2⟩
  · exact hne' (eq_of_prefix_of_prefix_of_length_eq hp List.prefix_rfl hlen)
  · exact hne' (eq_of_prefix_of_prefix_of_length_eq List.prefix_rfl hp hlen)
  · have hz : z.length < s := by
      have hlt := h1.length_lt
      have := l₁.2
      omega
    refine not_branchBelow_of_branchBelow (b := b) (e.branch_leaf b ⟨z, hz⟩ l₁ h1) ?_
    rw [hl]
    exact e.branch_leaf (!b) ⟨z, hz⟩ l₂ h2

/-- **An internal image is never a leaf image.** Internal host nodes are shorter than the host
height and host leaves sit exactly at it, so the two levels cannot collide. -/
theorem internal_ne_leaf (e : ProperEmbedding s t) (x : InternalNode s) (l : LeafNode s) :
    (e.internal x).1 ≠ (e.leaf l).1 := by
  intro hcon
  have h1 := (e.internal x).2
  have h2 := (e.leaf l).2
  rw [hcon, h2] at h1
  omega

/-- The action on all vertices at once, which is what makes the embedding *proper*. -/
def vertex (e : ProperEmbedding s t) (x : TreeNode s) : TreeNode t :=
  if h : x.1.length < s then internalToTree (e.internal ⟨x.1, h⟩)
  else leafToTree (e.leaf ⟨x.1, le_antisymm x.2 (not_lt.mp h)⟩)

@[simp] theorem vertex_val (e : ProperEmbedding s t) (x : TreeNode s) :
    (e.vertex x).1
      = if h : x.1.length < s then (e.internal ⟨x.1, h⟩).1
        else (e.leaf ⟨x.1, le_antisymm x.2 (not_lt.mp h)⟩).1 := by
  rw [vertex]
  split <;> rfl

@[simp] theorem vertex_of_internal (e : ProperEmbedding s t) (x : InternalNode s) :
    e.vertex (internalToTree x) = internalToTree (e.internal x) := by
  refine Subtype.ext ?_
  rw [vertex_val, dite_eq_left (show (internalToTree x).1.length < s from x.2)]
  rfl

@[simp] theorem vertex_of_leaf (e : ProperEmbedding s t) (l : LeafNode s) :
    e.vertex (leafToTree l) = leafToTree (e.leaf l) := by
  refine Subtype.ext ?_
  have hnl : ¬ (leafToTree l).1.length < s := by rw [leafToTree_val, l.2]; omega
  rw [vertex_val, dite_eq_right hnl]
  rfl

theorem vertex_injective (e : ProperEmbedding s t) : Function.Injective e.vertex := by
  intro x y hxy
  have hval : (e.vertex x).1 = (e.vertex y).1 := congrArg Subtype.val hxy
  rw [vertex_val, vertex_val] at hval
  refine Subtype.ext ?_
  by_cases hx : x.1.length < s <;> by_cases hy : y.1.length < s
  · rw [dite_eq_left hx, dite_eq_left hy] at hval
    simpa using congrArg Subtype.val (e.internal_injective (Subtype.ext hval))
  · rw [dite_eq_left hx, dite_eq_right hy] at hval
    exact absurd hval (e.internal_ne_leaf _ _)
  · rw [dite_eq_right hx, dite_eq_left hy] at hval
    exact absurd hval.symm (e.internal_ne_leaf _ _)
  · rw [dite_eq_right hx, dite_eq_right hy] at hval
    simpa using congrArg Subtype.val (e.leaf_injective (Subtype.ext hval))

end ProperEmbedding

/-! ### Extending an internal embedding through the leaf level -/

namespace InternalEmbedding

/-- **The parent of a leaf**, as an internal node of the source. A leaf of positive length is
one turn below an internal node, and that node is where the extension reads its instructions. -/
def leafParent (l : LeafNode s) (hl : l.1 ≠ []) : InternalNode s :=
  ⟨l.1.dropLast, by
    have hlen := l.2
    have hpos : l.1.length ≠ 0 := fun hz => hl (List.eq_nil_of_length_eq_zero hz)
    rw [List.length_dropLast, hlen]
    omega⟩

@[simp] theorem leafParent_val (l : LeafNode s) (hl : l.1 ≠ []) :
    (leafParent l hl).1 = l.1.dropLast := rfl

/-- The parent, followed by the leaf's own last turn, is the leaf. -/
theorem leafParent_append_getLast (l : LeafNode s) (hl : l.1 ≠ []) :
    (leafParent l hl).1 ++ [l.1.getLast hl] = l.1 := List.dropLast_append_getLast hl

/-- The word a source leaf's image must extend: from the image of the leaf's parent, take the
turn the leaf takes. Empty when the leaf has no parent, which happens exactly at height `0`. -/
def leafPrefix (e : InternalEmbedding s t) (l : LeafNode s) : List Bool :=
  if hl : l.1 = [] then [] else (e (leafParent l hl)).1 ++ [l.1.getLast hl]

theorem leafPrefix_of_ne_nil (e : InternalEmbedding s t) (l : LeafNode s) (hl : l.1 ≠ []) :
    leafPrefix e l = (e (leafParent l hl)).1 ++ [l.1.getLast hl] := dite_eq_right hl

@[simp] theorem leafPrefix_of_nil (e : InternalEmbedding s t) (l : LeafNode s) (hl : l.1 = []) :
    leafPrefix e l = [] := dite_eq_left hl

theorem leafPrefix_length_le (e : InternalEmbedding s t) (l : LeafNode s) :
    (leafPrefix e l).length ≤ t := by
  by_cases hl : l.1 = []
  · rw [leafPrefix_of_nil e l hl]
    simp
  · rw [leafPrefix_of_ne_nil e l hl]
    have := (e (leafParent l hl)).2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- **Every internal embedding extends through the leaf level.**

The leaf image enters the correct branch below the image of the leaf's parent and is then padded
to the host height. No spare-height hypothesis appears. -/
def extendProper (e : InternalEmbedding s t) : ProperEmbedding s t where
  internal := e.toFun
  leaf l := ⟨padTo t (leafPrefix e l), padTo_length (leafPrefix_length_le e l)⟩
  branch_internal := e.branch
  branch_leaf b x l h := by
    -- The leaf lies below something, so it is not the root and does have a parent.
    have hl : l.1 ≠ [] := by
      intro hnil
      have hlt := h.length_lt
      rw [hnil] at hlt
      simp at hlt
    set w := leafParent l hl with hw
    set c := l.1.getLast hl with hc
    have hsplit : w.1 ++ [c] = l.1 := leafParent_append_getLast l hl
    -- Read the hypothesis through the split, so both sides speak about `w.1 ++ [c]`.
    rw [BranchBelow, ← hsplit] at h
    refine List.IsPrefix.trans ?_ (prefix_padTo t _)
    rw [leafPrefix_of_ne_nil e l hl, ← hw, ← hc]
    have hlen : x.1.length ≤ w.1.length := by
      have := h.length_le
      simp at this
      omega
    rcases eq_or_lt_of_le hlen with heq | hlt
    · -- `x` *is* the parent, so the turn `b` is the leaf's own last letter.
      have hpair : x.1 = w.1 ∧ [b] = [c] :=
        List.append_inj (eq_of_prefix_of_prefix_of_length_eq h List.prefix_rfl (by simp [heq]))
          heq
      obtain ⟨hxw, hbc⟩ := hpair
      rw [show x = w from Subtype.ext hxw, show b = c from by simpa using hbc]
    · -- `x` is strictly above the parent, so the turn is taken inside the parent's subtree.
      have hsub : BranchBelow b x.1 w.1 :=
        List.prefix_of_prefix_length_le h (List.prefix_append _ _) (by simp; omega)
      exact (e.branch b x w hsub).trans (List.prefix_append _ _)

/-- **Restriction after extension is the identity.** The extension adds the leaf level and
changes nothing in the interior. -/
@[simp] theorem extendProper_toInternal (e : InternalEmbedding s t) :
    (extendProper e).toInternal = e := rfl

@[simp] theorem extendProper_internal (e : InternalEmbedding s t) (x : InternalNode s) :
    (extendProper e).internal x = e x := rfl

/-- The leaf equation away from height `0`: enter the branch, then pad. -/
theorem extendProper_leaf_val (e : InternalEmbedding s t) (l : LeafNode s) (hl : l.1 ≠ []) :
    ((extendProper e).leaf l).1 = padTo t ((e (leafParent l hl)).1 ++ [l.1.getLast hl]) := by
  rw [show ((extendProper e).leaf l).1 = padTo t (leafPrefix e l) from rfl,
    leafPrefix_of_ne_nil e l hl]

/-- **The height-zero endpoint.** There is no interior to read, so the single source leaf goes
to the canonical all-`false` host leaf. -/
@[simp] theorem extendProper_leaf_zero (e : InternalEmbedding 0 t) (l : LeafNode 0) :
    ((extendProper e).leaf l).1 = List.replicate t false := by
  have hl : l.1 = [] := List.eq_nil_of_length_eq_zero l.2
  rw [show ((extendProper e).leaf l).1 = padTo t (leafPrefix e l) from rfl,
    leafPrefix_of_nil e l hl, padTo_nil]

/-- The unique embedding out of a height-zero tree: it has no internal node to place. -/
def ofHeightZero (t : ℕ) : InternalEmbedding 0 t where
  toFun x := isEmptyElim x
  branch _ x _ _ := isEmptyElim x

end InternalEmbedding

/-! ### Tests -/

section Tests

open InternalEmbedding ProperEmbedding

-- **Restriction after extension**, for an arbitrary embedding: not a computation on an example.
example {s t : ℕ} (e : InternalEmbedding s t) : (extendProper e).toInternal = e :=
  extendProper_toInternal e

-- **Height zero.** The source is a single leaf with no interior; its image is the canonical
-- host leaf, and it does sit at the full host height.
example : ((extendProper (ofHeightZero 2)).leaf ⟨[], rfl⟩).1 = [false, false] := by decide

example : ((extendProper (ofHeightZero 2)).leaf ⟨[], rfl⟩).1.length = 2 := by decide

-- **Height one, tight case.** `singleton ⟨[false], _⟩` puts the source root at the *last*
-- internal level of a height-two host, leaving exactly one level for the leaves. The extension
-- must therefore enter the branch and stop — there is no room to spare, and it still works.
private def tightEmb : InternalEmbedding 1 2 := singleton ⟨[false], by decide⟩

example : ((extendProper tightEmb).leaf ⟨[false], rfl⟩).1 = [false, false] := by decide
example : ((extendProper tightEmb).leaf ⟨[true], rfl⟩).1 = [false, true] := by decide

-- The two leaves of the source land on distinct host leaves, so the extension has not
-- collapsed the leaf level.
example : ((extendProper tightEmb).leaf ⟨[false], rfl⟩).1
    ≠ ((extendProper tightEmb).leaf ⟨[true], rfl⟩).1 := by decide

-- …and the source root's image is still where the internal embedding put it.
example : ((extendProper tightEmb).internal ⟨[], by decide⟩).1 = [false] := rfl

-- **Direction is preserved into the leaf level**: the leaf `[true]` leaves the source root
-- through the true-branch, and its image leaves the root's image through the true-branch too.
example : BranchBelow true (⟨[], by decide⟩ : InternalNode 1).1 (⟨[true], rfl⟩ : LeafNode 1).1 := by
  decide

example :
    BranchBelow true ((extendProper tightEmb).internal ⟨[], by decide⟩).1
      ((extendProper tightEmb).leaf ⟨[true], rfl⟩).1 := by decide

-- Identity and composition.
example (l : LeafNode 3) : (ProperEmbedding.id 3).leaf l = l := rfl

example {s t u : ℕ} (g : ProperEmbedding t u) (f : ProperEmbedding s t) :
    (ProperEmbedding.comp g f).toInternal
      = InternalEmbedding.comp g.toInternal f.toInternal := rfl

-- Injectivity on leaves and on all vertices, for an arbitrary proper embedding.
example {s t : ℕ} (e : ProperEmbedding s t) (l₁ l₂ : LeafNode s) (h : e.leaf l₁ = e.leaf l₂) :
    l₁ = l₂ := e.leaf_injective h

example {s t : ℕ} (e : ProperEmbedding s t) (x y : TreeNode s) (h : e.vertex x = e.vertex y) :
    x = y := e.vertex_injective h

end Tests

end RegularityLemmata
