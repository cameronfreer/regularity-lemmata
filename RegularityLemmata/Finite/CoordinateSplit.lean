/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Disjoint
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Splitting tuple coordinates into two groups

A `CoordinateSplit n` chooses a set of coordinates; the rest are its complement. Tuples over
a **dependent** carrier family `V : Fin n → Type*` then factor as a pair of half-tuples
(`splitEquiv`), and relations on tuples become relations between the halves (`splitRel`).

This is ordinary finite combinatorics. Nothing here mentions weights, regularity, or
stability, and nothing imports a relational model — which is what lets the weighted-box and
hypergraph layers consume it.

## Two representation decisions

**Only the chosen coordinate set is data.** The complement, the two index subtypes, and
properness are all derived. In particular `IsProper` is a **predicate, not a field**: empty
and full splits are legal neutral endpoints here, and a consumer needing a genuine two-sided
split asks for `σ.IsProper` itself. Bundling nonemptiness proofs would tax every neutral
consumer.

**Reindexing transports the carrier family too.** For `π : Equiv.Perm (Fin n)` the reindexed
tuple `fun i => x (π i)` has type `∀ i, V (π i)`, not `∀ i, V i`. Rather than insert casts,
the naturality statements are indexed by the transported family `fun i => V (π i)`, and the
correspondence between the two index subtypes is carried by an explicit `Equiv`
(`reindexLeftEquiv`, `reindexRightEquiv`). Every public statement is then cast-free and
holds by `rfl`. The membership equation

  `i ∈ (σ.reindex π).left ↔ π i ∈ σ.left`

is the canonical statement of the reindexing direction; all naturality is derived from it, so
the direction cannot drift.

The only cast in the file is inside `oneVsRest`, where reconstructing a full tuple from a
value at coordinate `i` needs `h : j = i` to move `V i` to `V j`. It is quarantined in that
definition and its evaluation lemma.
-/

namespace RegularityLemmata

/-- A split of the coordinates `Fin n` into a chosen set and its complement. Only the chosen
set is data. -/
structure CoordinateSplit (n : ℕ) where
  /-- The chosen coordinates. -/
  left : Finset (Fin n)

namespace CoordinateSplit

variable {n : ℕ} {V : Fin n → Type*}

/-! ### The two sides -/

/-- The complementary coordinates. -/
def right (σ : CoordinateSplit n) : Finset (Fin n) := Finset.univ \ σ.left

@[simp] theorem mem_right_iff {σ : CoordinateSplit n} {i : Fin n} :
    i ∈ σ.right ↔ i ∉ σ.left := by
  rw [right, Finset.mem_sdiff]
  simp

/-- The chosen index type. -/
abbrev Left (σ : CoordinateSplit n) := {i : Fin n // i ∈ σ.left}

/-- The complementary index type. -/
abbrev Right (σ : CoordinateSplit n) := {i : Fin n // i ∉ σ.left}

/-- A split is **proper** when both sides are inhabited. A predicate, deliberately not a
field: the empty and full splits are legal here. -/
def IsProper (σ : CoordinateSplit n) : Prop := σ.left.Nonempty ∧ σ.right.Nonempty

theorem isProper_iff {σ : CoordinateSplit n} :
    σ.IsProper ↔ σ.left.Nonempty ∧ ∃ i, i ∉ σ.left := by
  rw [IsProper]
  constructor
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, mem_right_iff.mp hi⟩
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, mem_right_iff.mpr hi⟩

/-! ### Restriction and gluing, for dependent carriers -/

/-- The half-tuple on the chosen coordinates. -/
def restrictLeft (σ : CoordinateSplit n) (x : ∀ i, V i) : ∀ i : σ.Left, V i.1 :=
  fun i => x i.1

/-- The half-tuple on the complementary coordinates. -/
def restrictRight (σ : CoordinateSplit n) (x : ∀ i, V i) : ∀ i : σ.Right, V i.1 :=
  fun i => x i.1

/-- Reassemble a tuple from its two halves. -/
def glue (σ : CoordinateSplit n) (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    ∀ i, V i :=
  fun i => if hi : i ∈ σ.left then xL ⟨i, hi⟩ else xR ⟨i, hi⟩

variable {σ : CoordinateSplit n}

@[simp] theorem glue_apply_left {xL : ∀ i : σ.Left, V i.1} {xR : ∀ i : σ.Right, V i.1}
    {i : Fin n} (hi : i ∈ σ.left) : σ.glue xL xR i = xL ⟨i, hi⟩ := dif_pos hi

@[simp] theorem glue_apply_right {xL : ∀ i : σ.Left, V i.1} {xR : ∀ i : σ.Right, V i.1}
    {i : Fin n} (hi : i ∉ σ.left) : σ.glue xL xR i = xR ⟨i, hi⟩ := dif_neg hi

@[simp] theorem restrictLeft_glue (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    σ.restrictLeft (σ.glue xL xR) = xL := by
  funext i
  rw [restrictLeft, glue_apply_left i.2]

@[simp] theorem restrictRight_glue (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    σ.restrictRight (σ.glue xL xR) = xR := by
  funext i
  rw [restrictRight, glue_apply_right i.2]

@[simp] theorem glue_restrict (x : ∀ i, V i) :
    σ.glue (σ.restrictLeft x) (σ.restrictRight x) = x := by
  funext i
  by_cases hi : i ∈ σ.left
  · rw [glue_apply_left hi, restrictLeft]
  · rw [glue_apply_right hi, restrictRight]

/-! ### The factorization equivalence -/

/-- **Tuples factor along a split.** Computable, with both round trips proved. -/
def splitEquiv (σ : CoordinateSplit n) (V : Fin n → Type*) :
    (∀ i, V i) ≃ ((∀ i : σ.Left, V i.1) × (∀ i : σ.Right, V i.1)) where
  toFun x := (σ.restrictLeft x, σ.restrictRight x)
  invFun p := σ.glue p.1 p.2
  left_inv x := glue_restrict x
  right_inv p := Prod.ext (restrictLeft_glue p.1 p.2) (restrictRight_glue p.1 p.2)

@[simp] theorem splitEquiv_apply (x : ∀ i, V i) :
    σ.splitEquiv V x = (σ.restrictLeft x, σ.restrictRight x) := rfl

@[simp] theorem splitEquiv_symm_apply
    (p : (∀ i : σ.Left, V i.1) × (∀ i : σ.Right, V i.1)) :
    (σ.splitEquiv V).symm p = σ.glue p.1 p.2 := rfl

/-! ### The complementary split -/

/-- Exchanging the two sides. -/
def swap (σ : CoordinateSplit n) : CoordinateSplit n := ⟨σ.right⟩

@[simp] theorem swap_left (σ : CoordinateSplit n) : σ.swap.left = σ.right := rfl

@[simp] theorem swap_swap (σ : CoordinateSplit n) : σ.swap.swap = σ := by
  refine congrArg CoordinateSplit.mk ?_
  ext i
  simp [swap, right]

/-- The complementary split's chosen indices are the original's complementary indices. -/
def swapLeftEquiv (σ : CoordinateSplit n) : σ.swap.Left ≃ σ.Right where
  toFun i := ⟨i.1, mem_right_iff.mp i.2⟩
  invFun i := ⟨i.1, mem_right_iff.mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- …and conversely. -/
def swapRightEquiv (σ : CoordinateSplit n) : σ.swap.Right ≃ σ.Left where
  toFun i := ⟨i.1, by
    by_contra h
    exact i.2 (mem_right_iff.mpr h)⟩
  invFun i := ⟨i.1, fun h => (mem_right_iff.mp h) i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem swapLeftEquiv_val (σ : CoordinateSplit n) (i : σ.swap.Left) :
    (σ.swapLeftEquiv i).1 = i.1 := rfl

@[simp] theorem swapRightEquiv_val (σ : CoordinateSplit n) (i : σ.swap.Right) :
    (σ.swapRightEquiv i).1 = i.1 := rfl

/-- **Complement coherence**: gluing over the complementary split is gluing over the
original with the two halves exchanged. This is the `Prod.swap` statement, with the index
correspondence carried by the two equivalences rather than by a cast. -/
theorem swap_glue (σ : CoordinateSplit n) (xL : ∀ i : σ.swap.Left, V i.1)
    (xR : ∀ i : σ.swap.Right, V i.1) :
    σ.swap.glue xL xR
      = σ.glue (fun i => xR ⟨i.1, fun h => (mem_right_iff.mp h) i.2⟩)
          (fun i => xL ⟨i.1, mem_right_iff.mpr i.2⟩) := by
  funext i
  by_cases hi : i ∈ σ.left
  · rw [glue_apply_left hi,
      glue_apply_right (show i ∉ σ.swap.left from fun h => (mem_right_iff.mp h) hi)]
  · rw [glue_apply_right hi,
      glue_apply_left (show i ∈ σ.swap.left from mem_right_iff.mpr hi)]

/-! ### Reindexing

The membership equation below is the canonical statement of the direction. Naturality is
stated over the **transported** carrier family `fun i => V (π i)`, which is what keeps every
public statement cast-free. -/

/-- Pull a split back along a permutation. -/
def reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) : CoordinateSplit n :=
  ⟨σ.left.image π.symm⟩

/-- **The canonical direction statement.** Everything about `reindex` follows from this. -/
@[simp] theorem mem_reindex_left {σ : CoordinateSplit n} {π : Equiv.Perm (Fin n)}
    {i : Fin n} : i ∈ (σ.reindex π).left ↔ π i ∈ σ.left := by
  rw [reindex, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rwa [Equiv.apply_symm_apply]
  · intro h
    exact ⟨π i, h, π.symm_apply_apply i⟩

/-- The index correspondence on the chosen side: `i ↦ π i`. -/
def reindexLeftEquiv (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) :
    (σ.reindex π).Left ≃ σ.Left where
  toFun i := ⟨π i.1, mem_reindex_left.mp i.2⟩
  invFun j := ⟨π.symm j.1, mem_reindex_left.mpr (by rw [Equiv.apply_symm_apply]; exact j.2)⟩
  left_inv i := Subtype.ext (π.symm_apply_apply i.1)
  right_inv j := Subtype.ext (π.apply_symm_apply j.1)

/-- The index correspondence on the complementary side. -/
def reindexRightEquiv (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) :
    (σ.reindex π).Right ≃ σ.Right where
  toFun i := ⟨π i.1, fun h => i.2 (mem_reindex_left.mpr h)⟩
  invFun j := ⟨π.symm j.1, by
    intro h
    have h' := mem_reindex_left.mp h
    rw [Equiv.apply_symm_apply] at h'
    exact j.2 h'⟩
  left_inv i := Subtype.ext (π.symm_apply_apply i.1)
  right_inv j := Subtype.ext (π.apply_symm_apply j.1)

@[simp] theorem reindexLeftEquiv_val (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (i : (σ.reindex π).Left) : (σ.reindexLeftEquiv π i).1 = π i.1 := rfl

@[simp] theorem reindexRightEquiv_val (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (i : (σ.reindex π).Right) : (σ.reindexRightEquiv π i).1 = π i.1 := rfl

/-- **Naturality of the chosen-side restriction.** Cast-free, because the reindexed tuple is
taken over the transported carrier family. -/
theorem restrictLeft_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (x : ∀ i, V i) :
    (σ.reindex π).restrictLeft (V := fun i => V (π i)) (fun i => x (π i))
      = fun i => σ.restrictLeft x (σ.reindexLeftEquiv π i) := rfl

/-- Naturality of the complementary-side restriction. -/
theorem restrictRight_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (x : ∀ i, V i) :
    (σ.reindex π).restrictRight (V := fun i => V (π i)) (fun i => x (π i))
      = fun i => σ.restrictRight x (σ.reindexRightEquiv π i) := rfl

/-- Naturality of gluing: reassembling the transported halves is the transport of the
reassembled tuple. -/
theorem glue_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    (σ.reindex π).glue (V := fun i => V (π i))
        (fun i => xL ⟨π i.1, mem_reindex_left.mp i.2⟩)
        (fun i => xR ⟨π i.1, fun h => i.2 (mem_reindex_left.mpr h)⟩)
      = fun i => σ.glue xL xR (π i) := by
  funext i
  by_cases hi : π i ∈ σ.left
  · rw [glue_apply_left (mem_reindex_left.mpr hi), glue_apply_left hi]
  · rw [glue_apply_right (fun h => hi (mem_reindex_left.mp h)), glue_apply_right hi]

/-! ### Split relations -/

/-- A relation on tuples, viewed as a relation between the two halves. -/
def splitRel (σ : CoordinateSplit n) (R : (∀ i, V i) → Prop) :
    (∀ i : σ.Left, V i.1) → (∀ i : σ.Right, V i.1) → Prop :=
  fun xL xR => R (σ.glue xL xR)

@[simp] theorem splitRel_apply (R : (∀ i, V i) → Prop) (xL : ∀ i : σ.Left, V i.1)
    (xR : ∀ i : σ.Right, V i.1) : σ.splitRel R xL xR ↔ R (σ.glue xL xR) := Iff.rfl

/-- Naturality of `splitRel` under reindexing. -/
theorem splitRel_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (R : (∀ i, V i) → Prop) (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    (σ.reindex π).splitRel (V := fun i => V (π i)) (fun y => R (fun i => σ.glue xL xR i))
        (fun i => xL (σ.reindexLeftEquiv π i)) (fun i => xR (σ.reindexRightEquiv π i))
      ↔ R (σ.glue xL xR) := Iff.rfl

/-! ### One versus rest -/

/-- The split isolating a single coordinate. -/
def singleton (i : Fin n) : CoordinateSplit n := ⟨{i}⟩

@[simp] theorem mem_singleton_left {i j : Fin n} : j ∈ (singleton i).left ↔ j = i := by
  rw [singleton, Finset.mem_singleton]

/-- A relation on tuples, viewed as a relation between the value at one coordinate and the
remaining tuple. The `h ▸ v` cast is the only one in this file, quarantined here and in the
evaluation lemma below. -/
def oneVsRest (R : (∀ i, V i) → Prop) (i : Fin n) :
    V i → (∀ j : {j : Fin n // j ≠ i}, V j.1) → Prop :=
  fun v rest => R fun j => if h : j = i then h ▸ v else rest ⟨j, h⟩

/-- The evaluation lemma, displaying the reconstructed tuple explicitly. -/
theorem oneVsRest_apply (R : (∀ i, V i) → Prop) (i : Fin n) (v : V i)
    (rest : ∀ j : {j : Fin n // j ≠ i}, V j.1) :
    oneVsRest R i v rest ↔ R (fun j => if h : j = i then h ▸ v else rest ⟨j, h⟩) := Iff.rfl

/-! ### Injectivity across a split

Only meaningful for a constant carrier, where `Function.Injective` typechecks. -/

/-- **Injectivity of a glued tuple.** The cross-range disjointness clause is load-bearing:
individually injective halves do **not** give an injective glued tuple. -/
theorem glue_injective_iff {α : Type*} (σ : CoordinateSplit n) (xL : σ.Left → α)
    (xR : σ.Right → α) :
    Function.Injective (σ.glue (V := fun _ => α) xL xR) ↔
      Function.Injective xL ∧ Function.Injective xR ∧
        Disjoint (Set.range xL) (Set.range xR) := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
    · refine Subtype.ext (h ?_)
      rw [glue_apply_left a.2, glue_apply_left b.2]
      simpa using hab
    · refine Subtype.ext (h ?_)
      rw [glue_apply_right a.2, glue_apply_right b.2]
      simpa using hab
    · rw [Set.disjoint_left]
      rintro c ⟨a, rfl⟩ ⟨b, hb⟩
      have hval : σ.glue (V := fun _ => α) xL xR a.1 = σ.glue (V := fun _ => α) xL xR b.1 := by
        rw [glue_apply_left a.2, glue_apply_right b.2]
        simpa using hb.symm
      exact b.2 (h hval ▸ a.2)
  · rintro ⟨hL, hR, hd⟩ i j hij
    by_cases hi : i ∈ σ.left <;> by_cases hj : j ∈ σ.left
    · rw [glue_apply_left hi, glue_apply_left hj] at hij
      exact congrArg Subtype.val (hL hij)
    · rw [glue_apply_left hi, glue_apply_right hj] at hij
      exact absurd (Set.disjoint_left.mp hd ⟨⟨i, hi⟩, rfl⟩ ⟨⟨j, hj⟩, hij.symm⟩) not_false
    · rw [glue_apply_right hi, glue_apply_left hj] at hij
      exact absurd (Set.disjoint_left.mp hd ⟨⟨j, hj⟩, rfl⟩ ⟨⟨i, hi⟩, hij⟩) not_false
    · rw [glue_apply_right hi, glue_apply_right hj] at hij
      exact congrArg Subtype.val (hR hij)

/-- The complementary index type as the coercion of the complementary finset. -/
def rightEquiv (σ : CoordinateSplit n) : σ.Right ≃ {i : Fin n // i ∈ σ.right} where
  toFun i := ⟨i.1, mem_right_iff.mpr i.2⟩
  invFun i := ⟨i.1, mem_right_iff.mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Box factorization -/

/-- **`piFinset` factors along a split**, in cardinality. The identity the weighted-box layer
consumes. -/
theorem card_piFinset_split [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (σ : CoordinateSplit n) (A : ∀ i, Finset (V i)) :
    (Fintype.piFinset A).card
      = (Fintype.piFinset fun i : σ.Left => A i.1).card
        * (Fintype.piFinset fun i : σ.Right => A i.1).card := by
  classical
  rw [Fintype.card_piFinset, Fintype.card_piFinset, Fintype.card_piFinset]
  have hL : (∏ i : σ.Left, (A i.1).card) = ∏ i ∈ σ.left, (A i).card :=
    Finset.prod_coe_sort σ.left (fun i => (A i).card)
  have hR : (∏ i : σ.Right, (A i.1).card) = ∏ i ∈ σ.right, (A i).card := by
    rw [← Finset.prod_coe_sort σ.right (fun i => (A i).card)]
    exact Fintype.prod_equiv σ.rightEquiv _ _ (fun _ => rfl)
  have hsplit : (∏ i, (A i).card)
      = (∏ i ∈ σ.left, (A i).card) * (∏ i ∈ σ.right, (A i).card) := by
    rw [right, ← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hsplit, hL, hR]

end CoordinateSplit

/-! ### Tests and adversarial examples -/

section Tests

open CoordinateSplit

/-- A genuinely dependent carrier family. -/
private def W : Fin 3 → Type := ![Fin 2, Fin 3, Bool]

-- **Empty and full splits are legal** — the whole point of `IsProper` being a predicate.
example : (⟨∅⟩ : CoordinateSplit 3).left = ∅ := rfl
example : ¬ (⟨∅⟩ : CoordinateSplit 3).IsProper := by
  rw [IsProper]
  simp

example : ¬ (⟨Finset.univ⟩ : CoordinateSplit 3).IsProper := by
  rw [IsProper, right]
  simp

-- A nontrivial split of `Fin 3` at `{0, 2}` is proper.
example : (⟨{0, 2}⟩ : CoordinateSplit 3).IsProper := by
  rw [IsProper]
  constructor
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

-- The factorization equivalence at the dependent family, statement level.
example (σ : CoordinateSplit 3) :
    (∀ i, W i) ≃ ((∀ i : σ.Left, W i.1) × (∀ i : σ.Right, W i.1)) :=
  σ.splitEquiv W

-- **The reindex direction**, pinned by the canonical membership equation.
example (σ : CoordinateSplit 3) (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    i ∈ (σ.reindex π).left ↔ π i ∈ σ.left := mem_reindex_left

-- A concrete direction check: swapping `0` and `1` moves the split `{0}` to `{1}`.
example : ((CoordinateSplit.singleton (0 : Fin 3)).reindex (Equiv.swap 0 1)).left = {1} := by
  ext i
  rw [mem_reindex_left, mem_singleton_left, Finset.mem_singleton]
  fin_cases i <;> decide

-- **A relation sensitive to coordinate order**, verifying `splitRel` reads the right halves.
example (σ : CoordinateSplit 3) (xL : ∀ i : σ.Left, (fun _ : Fin 3 => Fin 4) i.1)
    (xR : ∀ i : σ.Right, (fun _ : Fin 3 => Fin 4) i.1) :
    σ.splitRel (V := fun _ => Fin 4) (fun x => x 0 < x 1) xL xR
      ↔ σ.glue (V := fun _ => Fin 4) xL xR 0 < σ.glue (V := fun _ => Fin 4) xL xR 1 :=
  Iff.rfl

-- **The range-disjointness clause is necessary.** Two singleton-domain halves of the split
-- `{0}` of `Fin 2`, each vacuously injective, that collide — so the glued tuple is not
-- injective even though both halves are.
example :
    ¬ Function.Injective
        ((CoordinateSplit.singleton (0 : Fin 2)).glue (V := fun _ => Fin 4)
          (fun _ => 3) (fun _ => 3)) := by
  intro h
  have h01 : (0 : Fin 2) = 1 := by
    refine h ?_
    rw [glue_apply_left (by decide), glue_apply_right (by decide)]
  exact absurd h01 (by decide)

-- …while each half on its own is injective, since each domain is a singleton.
example :
    Function.Injective (fun _ : (CoordinateSplit.singleton (0 : Fin 2)).Left => (3 : Fin 4)) ∧
      Function.Injective
        (fun _ : (CoordinateSplit.singleton (0 : Fin 2)).Right => (3 : Fin 4)) := by
  constructor
  · intro a b _
    refine Subtype.ext ?_
    have ha := mem_singleton_left.mp a.2
    have hb := mem_singleton_left.mp b.2
    rw [ha, hb]
  · intro a b _
    refine Subtype.ext ?_
    have ha := a.2
    have hb := b.2
    rw [mem_singleton_left] at ha hb
    have ha1 : a.1 = 1 := by omega
    have hb1 : b.1 = 1 := by omega
    rw [ha1, hb1]

-- `oneVsRest` at each coordinate of `Fin 3`, at a dependent family.
example (R : (∀ i, W i) → Prop) (v : W 0) (rest : ∀ j : {j : Fin 3 // j ≠ 0}, W j.1) :
    oneVsRest R 0 v rest ↔ R (fun j => if h : j = 0 then h ▸ v else rest ⟨j, h⟩) :=
  oneVsRest_apply R 0 v rest

example (R : (∀ i, W i) → Prop) (v : W 1) (rest : ∀ j : {j : Fin 3 // j ≠ 1}, W j.1) :
    oneVsRest R 1 v rest ↔ R (fun j => if h : j = 1 then h ▸ v else rest ⟨j, h⟩) :=
  oneVsRest_apply R 1 v rest

example (R : (∀ i, W i) → Prop) (v : W 2) (rest : ∀ j : {j : Fin 3 // j ≠ 2}, W j.1) :
    oneVsRest R 2 v rest ↔ R (fun j => if h : j = 2 then h ▸ v else rest ⟨j, h⟩) :=
  oneVsRest_apply R 2 v rest

end Tests

end RegularityLemmata
