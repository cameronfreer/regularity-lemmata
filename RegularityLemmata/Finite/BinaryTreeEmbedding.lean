/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.FullBinaryTree

/-!
# Embeddings of finite binary trees

An **internal embedding** of a height-`s` tree into a height-`t` tree maps internal nodes to
internal nodes and preserves branch direction. It has exactly one law:

> if `y` lies in the `b`-branch below `x`, then the image of `y` lies in the `b`-branch below
> the image of `x`.

## What is deliberately not required

There is **no** field asking that

* the source root map to the host root,
* source and host depths agree, or
* an edge map to an edge.

All three are false requirements, not omissions. In a recursive construction the two pieces
being joined are found at unknown depth inside the two branches and are then attached under a
shallower node, so a source edge routinely maps to a long host path and the source root
routinely lands well below the host root. Imposing any of the three would make the
constructions in this file impossible; the tests at the end of the file refute each one on a
concrete example.

## What follows rather than being assumed

Injectivity is a **theorem**, not structure data: it follows from the branch law alone, via the
observation that two words either are prefix-comparable or separate through opposite turns
(`prefix_trichotomy`), together with the disjointness of the two branches below a node. Carrying
it as a field would let a caller supply a proof inconsistent with the branch law.

Ancestry preservation likewise follows, because a strict descent always happens through one
definite turn.
-/

namespace RegularityLemmata

/-- An embedding of the internal nodes of a height-`s` tree into those of a height-`t` tree,
preserving branch direction.

Injectivity and ancestry preservation are consequences, proved below. -/
structure InternalEmbedding (s t : ℕ) where
  /-- The underlying map on internal nodes. -/
  toFun : InternalNode s → InternalNode t
  /-- **The only law**: the first turn is preserved. -/
  branch : ∀ (b : Bool) (x y : InternalNode s),
    BranchBelow b x.1 y.1 → BranchBelow b (toFun x).1 (toFun y).1

namespace InternalEmbedding

variable {s t u : ℕ}

instance : CoeFun (InternalEmbedding s t) fun _ => InternalNode s → InternalNode t := ⟨toFun⟩

@[simp] theorem coe_mk (f : InternalNode s → InternalNode t) (hf) :
    ⇑(mk f hf) = f := rfl

theorem ext {e₁ e₂ : InternalEmbedding s t} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := by
  cases e₁; cases e₂; congr 1; exact funext h

/-- The branch law, restated as a theorem so that it is found by search under the name it is
used by. -/
theorem branch_preserved (e : InternalEmbedding s t) (b : Bool) (x y : InternalNode s)
    (h : BranchBelow b x.1 y.1) : BranchBelow b (e x).1 (e y).1 := e.branch b x y h

/-! ### Identity and composition -/

/-- The identity embedding. -/
def id (s : ℕ) : InternalEmbedding s s := ⟨_root_.id, fun _ _ _ h => h⟩

@[simp] theorem id_apply (x : InternalNode s) : id s x = x := rfl

/-- Composition of embeddings. Branch preservation composes directly, which is the payoff of
stating the law through the first turn rather than through immediate children. -/
def comp (g : InternalEmbedding t u) (f : InternalEmbedding s t) : InternalEmbedding s u :=
  ⟨fun x => g (f x), fun b x y h => g.branch b (f x) (f y) (f.branch b x y h)⟩

@[simp] theorem comp_apply (g : InternalEmbedding t u) (f : InternalEmbedding s t)
    (x : InternalNode s) : comp g f x = g (f x) := rfl

@[simp] theorem comp_id (f : InternalEmbedding s t) : comp f (id s) = f := ext fun _ => rfl

@[simp] theorem id_comp (f : InternalEmbedding s t) : comp (id t) f = f := ext fun _ => rfl

theorem comp_assoc {v : ℕ} (h : InternalEmbedding u v) (g : InternalEmbedding t u)
    (f : InternalEmbedding s t) : comp (comp h g) f = comp h (comp g f) := ext fun _ => rfl

/-! ### Ancestry, disjointness, and injectivity -/

/-- Ancestry is preserved: a node strictly below another maps strictly below its image. -/
theorem isStrictPrefix_preserved (e : InternalEmbedding s t) (x y : InternalNode s)
    (h : IsStrictPrefix x.1 y.1) : IsStrictPrefix (e x).1 (e y).1 := by
  obtain ⟨b, hb⟩ := exists_branchBelow_of_isStrictPrefix h
  exact (e.branch b x y hb).isStrictPrefix

/-- **The two branches below a node stay disjoint under an embedding.** -/
theorem apply_ne_apply_of_branchBelow (e : InternalEmbedding s t) (b : Bool)
    (z x y : InternalNode s) (hx : BranchBelow b z.1 x.1) (hy : BranchBelow (!b) z.1 y.1) :
    e x ≠ e y := by
  intro hxy
  refine not_branchBelow_of_branchBelow (b := b) (e.branch b z x hx) ?_
  rw [hxy]
  exact e.branch (!b) z y hy

/-- **Injectivity is a theorem.** It is a consequence of the branch law, so it is not carried
as structure data where a caller could supply an inconsistent proof. -/
theorem injective (e : InternalEmbedding s t) : Function.Injective e := by
  intro x y hxy
  by_contra hne
  have hne' : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
  rcases prefix_trichotomy x.1 y.1 with hp | hp | ⟨z, b, h1, h2⟩
  · obtain ⟨c, hc⟩ := exists_branchBelow_of_isStrictPrefix ⟨hp, hne'⟩
    have hlt := (e.branch c x y hc).length_lt
    rw [hxy] at hlt
    omega
  · obtain ⟨c, hc⟩ := exists_branchBelow_of_isStrictPrefix ⟨hp, Ne.symm hne'⟩
    have hlt := (e.branch c y x hc).length_lt
    rw [hxy] at hlt
    omega
  · have hz : z.length < s := by
      have h1' := h1.length_lt
      have := x.2
      omega
    exact apply_ne_apply_of_branchBelow e b ⟨z, hz⟩ x y h1 h2 hxy

/-! ### Constructors -/

/-- **A single node.** Any host internal node carries a copy of the height-one tree, whose only
internal node is its root. No hypothesis is needed: the height-one tree has nothing below its
root for the branch law to constrain. -/
def singleton (x : InternalNode t) : InternalEmbedding 1 t where
  toFun _ := x
  branch b y z h := by
    exfalso
    have hy : y.1 = [] := List.eq_nil_of_length_eq_zero (by have := y.2; omega)
    have hz : z.1 = [] := List.eq_nil_of_length_eq_zero (by have := z.2; omega)
    have := h.length_lt
    rw [hy, hz] at this
    omega

@[simp] theorem singleton_apply (x : InternalNode t) (y : InternalNode 1) :
    singleton x y = x := rfl

/-- **Descending into a branch.** A height-`h` tree sits inside the `b`-branch of a height-`h+1`
tree by prefixing every address with `b`. -/
def branchLift (h : ℕ) (b : Bool) : InternalEmbedding h (h + 1) where
  toFun x := consInternal b x
  branch b' x y hb' := by
    rw [BranchBelow, consInternal_val, consInternal_val, List.cons_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, hb'⟩

@[simp] theorem branchLift_apply (h : ℕ) (b : Bool) (x : InternalNode h) :
    branchLift h b x = consInternal b x := rfl

/-- The left branch lift. -/
abbrev left (h : ℕ) : InternalEmbedding h (h + 1) := branchLift h false

/-- The right branch lift. -/
abbrev right (h : ℕ) : InternalEmbedding h (h + 1) := branchLift h true

/-- Everything a branch lift produces lies in the corresponding branch below the root. -/
theorem branchBelow_root_branchLift (h : ℕ) (b : Bool) (x : InternalNode h) :
    BranchBelow b (root h).1 (branchLift h b x).1 := branchBelow_root_cons b x

/-! ### The fork

`fork` is the constructor the recursive arguments are built from: it attaches two embeddings,
already known to land in the two branches below a chosen host node, beneath a new root sent to
that node. It is exactly here that the source root maps below the host root, and exactly here
that a source edge becomes a long host path. -/

private def forkFun (x : InternalNode t) (f g : InternalEmbedding s t) :
    InternalNode (s + 1) → InternalNode t
  | ⟨[], _⟩ => x
  | ⟨false :: w, hw⟩ => f ⟨w, by simp at hw; omega⟩
  | ⟨true :: w, hw⟩ => g ⟨w, by simp at hw; omega⟩

private theorem forkFun_root (x : InternalNode t) (f g : InternalEmbedding s t) :
    forkFun x f g (root s) = x := rfl

private theorem forkFun_cons (x : InternalNode t) (f g : InternalEmbedding s t) (b : Bool)
    (y : InternalNode s) : forkFun x f g (consInternal b y) = bif b then g y else f y := by
  cases b <;> rfl

/-- **Attach two branch embeddings under a chosen node.**

`f` must land in the false-branch below `x` and `g` in the true-branch. The result embeds a
tree one level taller, sending its root to `x`. -/
def fork (x : InternalNode t) (f g : InternalEmbedding s t)
    (hf : ∀ y : InternalNode s, BranchBelow false x.1 (f y).1)
    (hg : ∀ y : InternalNode s, BranchBelow true x.1 (g y).1) :
    InternalEmbedding (s + 1) t where
  toFun := forkFun x f g
  branch b p q hpq := by
    rcases internalNode_cases p with rfl | ⟨c, y, rfl⟩
    · rcases internalNode_cases q with rfl | ⟨d, z, rfl⟩
      · exact absurd hpq.length_lt (by simp)
      · -- From the root, the first turn to `consInternal d z` is `d`, so `b = d`.
        have hbd : b = d := by
          have : [b] <+: d :: z.1 := by simpa [BranchBelow] using hpq
          simpa using (List.cons_prefix_cons.mp this).1
        subst hbd
        rw [forkFun_root, forkFun_cons]
        cases b
        · simpa using hf z
        · simpa using hg z
    · rcases internalNode_cases q with rfl | ⟨d, z, rfl⟩
      · exact absurd hpq.length_lt (by simp)
      · -- Both sides sit in the same branch, and that branch's embedding preserves the turn.
        have hcd : c = d ∧ BranchBelow b y.1 z.1 := by
          have : c :: (y.1 ++ [b]) <+: d :: z.1 := by simpa [BranchBelow] using hpq
          exact List.cons_prefix_cons.mp this
        obtain ⟨rfl, hyz⟩ := hcd
        rw [forkFun_cons, forkFun_cons]
        cases c
        · simpa using f.branch b y z hyz
        · simpa using g.branch b y z hyz

@[simp] theorem fork_root (x : InternalNode t) (f g : InternalEmbedding s t) (hf hg) :
    fork x f g hf hg (root s) = x := rfl

@[simp] theorem fork_cons (x : InternalNode t) (f g : InternalEmbedding s t) (hf hg) (b : Bool)
    (y : InternalNode s) : fork x f g hf hg (consInternal b y) = bif b then g y else f y :=
  forkFun_cons x f g b y

end InternalEmbedding

/-! ### Tests and falsifications -/

section Tests

open InternalEmbedding

-- Identity and composition compute.
example (x : InternalNode 3) : comp (id 3) (id 3) x = x := rfl

-- A branch lift followed by another is a genuine two-step descent: the address grows by both
-- letters, in order.
example (x : InternalNode 1) :
    (comp (branchLift 2 true) (branchLift 1 false) x).1 = true :: false :: x.1 := rfl

/-! Statements about **every** embedding rather than computations on one example. These cannot
close by `rfl`; each consumes a theorem of the file, so a weakening of that theorem would break
them. -/

-- Composition preserves branch direction. Needs the branch law twice.
example {s t u : ℕ} (g : InternalEmbedding t u) (f : InternalEmbedding s t) (b : Bool)
    (x y : InternalNode s) (h : BranchBelow b x.1 y.1) :
    BranchBelow b (comp g f x).1 (comp g f y).1 :=
  (comp g f).branch b x y h

-- Injectivity is available for an arbitrary embedding, with no finiteness or height hypothesis.
example {s t : ℕ} (e : InternalEmbedding s t) (x y : InternalNode s) (h : e x = e y) : x = y :=
  e.injective h

-- Ancestry is preserved for an arbitrary embedding.
example {s t : ℕ} (e : InternalEmbedding s t) (x y : InternalNode s)
    (h : IsStrictPrefix x.1 y.1) : IsStrictPrefix (e x).1 (e y).1 :=
  e.isStrictPrefix_preserved x y h

-- Two nodes in opposite branches below a common node keep distinct images, for an arbitrary
-- embedding. This is the statement that fails if left and right are exchanged.
example {s t : ℕ} (e : InternalEmbedding s t) (z x y : InternalNode s)
    (hx : BranchBelow false z.1 x.1) (hy : BranchBelow true z.1 y.1) : e x ≠ e y :=
  e.apply_ne_apply_of_branchBelow false z x y hx hy

-- **Left and right may not be exchanged.** The lift into the true-branch does not land in the
-- false-branch below the root, so a definition that swapped the two would be refuted here.
example : ¬ BranchBelow false (root 1).1 (branchLift 1 true ⟨[], by decide⟩).1 := by decide

-- …and it does land in the true-branch.
example : BranchBelow true (root 1).1 (branchLift 1 true ⟨[], by decide⟩).1 := by decide

/-- A fork of two singletons under the root of a height-two tree. Its root maps to the root,
its two children map to the two depth-one nodes. -/
private def forkExample : InternalEmbedding 2 2 :=
  fork (root 1) (singleton ⟨[false], by decide⟩) (singleton ⟨[true], by decide⟩)
    (fun _ => by exact (by decide : BranchBelow false [] [false]))
    (fun _ => by exact (by decide : BranchBelow true [] [true]))

example : (forkExample (root 1)).1 = [] := rfl
example : (forkExample (consInternal false (⟨[], by decide⟩ : InternalNode 1))).1 = [false] := rfl
example : (forkExample (consInternal true (⟨[], by decide⟩ : InternalNode 1))).1 = [true] := rfl

/-- **The source root need not map to the host root.** A height-one tree embeds at the
*right child* of a height-two tree's root. Requiring root preservation would forbid this
embedding, and with it the recursive construction that produces it. -/
private def belowRootExample : InternalEmbedding 1 2 := singleton ⟨[true], by decide⟩

example : (belowRootExample ⟨[], by decide⟩).1 = [true] := rfl
example : (belowRootExample ⟨[], by decide⟩).1 ≠ (root 1).1 := by decide

/-- **Depth need not be preserved.** Here a source node at depth `1` has an image at depth `2`,
so an embedding required to preserve absolute depth could not exist. -/
private def deepExample : InternalEmbedding 2 3 :=
  fork (root 2) (comp (branchLift 2 false) (singleton ⟨[false], by decide⟩))
    (comp (branchLift 2 true) (singleton ⟨[true], by decide⟩))
    (fun _ => by exact (by decide : BranchBelow false [] [false, false]))
    (fun _ => by exact (by decide : BranchBelow true [] [true, true]))

example :
    (deepExample (consInternal false (⟨[], by decide⟩ : InternalNode 1))).1 = [false, false] := rfl
example : (consInternal false (⟨[], by decide⟩ : InternalNode 1)).1.length = 1 := rfl

-- The image is strictly deeper than the source node, which is the point.
example :
    (consInternal false (⟨[], by decide⟩ : InternalNode 1)).1.length
      < (deepExample (consInternal false (⟨[], by decide⟩ : InternalNode 1))).1.length := by decide

-- Injectivity is available as a theorem, and is not vacuous here: the two children of the
-- source root have distinct images.
example : deepExample (consInternal false (⟨[], by decide⟩ : InternalNode 1))
    ≠ deepExample (consInternal true (⟨[], by decide⟩ : InternalNode 1)) := by
  refine fun h => absurd (deepExample.injective h) ?_
  decide

end Tests

end RegularityLemmata
