/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Language
import Mathlib.Data.Fin.VecNotation

/-!
# Computable finite relational models

Phase 8 unit 2 (design freeze in `ARCHITECTURE.md`): the data-valued model wrapper.
A `FiniteRelModel L V` interprets every relation symbol as a **Boolean** function
of ordered tuples — genuine computability, per the freeze. The carrier carries no
`Fintype` or `DecidableEq` requirement here; those enter only with enumeration and
counting.

`Holds` is the `Prop` reading (with its canonical decidability instance), and
extensionality is available at both the `rel` and `Holds` levels. The mathlib
adapter `toStructure : L.Structure V` (`Mathlib.ModelTheory.Basic`) is an
**explicit definition, never a global instance**: multiple relational models on
one carrier are routine, and a global `Language.Structure` instance would create
instance pollution and make comparisons between models painful. Consumers write
`letI := M.toStructure` when using mathlib's model-theory API; the bridge
`toStructure_relMap` identifies `RelMap` with `Holds` exactly. The gate test below
keeps two distinct models on the same carrier in a single theorem — nothing is
selected implicitly.
-/

namespace RegularityLemmata

open FirstOrder

/-- A computable finite relational model: Boolean interpretations of every
relation symbol on ordered tuples. No carrier finiteness or decidability is
required by the structure itself. -/
@[ext]
structure FiniteRelModel (L : FirstOrder.Language) [FiniteRelational L]
    (V : Type*) where
  /-- The Boolean interpretation of each relation symbol. -/
  rel : ∀ {n}, L.Relations n → (Fin n → V) → Bool

namespace FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*}

/-- The `Prop` reading of the Boolean interpretation. -/
def Holds (M : FiniteRelModel L V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → V) : Prop :=
  M.rel R x = true

instance (M : FiniteRelModel L V) {n : ℕ} (R : L.Relations n) (x : Fin n → V) :
    Decidable (M.Holds R x) :=
  inferInstanceAs (Decidable (_ = true))

/-- Extensionality at the `Holds` level. -/
theorem ext_holds {M N : FiniteRelModel L V}
    (h : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → V),
      M.Holds R x ↔ N.Holds R x) : M = N := by
  cases M with
  | mk rM =>
    cases N with
    | mk rN =>
      congr 1
      funext n R x
      exact Bool.eq_iff_iff.mpr (h R x)

/-! ### The binary adapter

A 2-ary symbol read as an ordinary binary relation `V → V → Prop` — the same-carrier
specialization of the heterogeneous pair API, which is the shape the pair-density and
homogeneity layers consume. Purely an interface: no arity bound, no regularity notion, and
nothing about ladders — transporting *ladder-freeness* along this adapter is a stability
statement and belongs to the stable development, not here. -/

/-- The binary relation named by a 2-ary symbol. -/
def binaryRel (M : FiniteRelModel L V) (R : L.Relations 2) : V → V → Prop :=
  fun a b => M.Holds R ![a, b]

@[simp] theorem binaryRel_apply (M : FiniteRelModel L V) (R : L.Relations 2) (a b : V) :
    M.binaryRel R a b ↔ M.Holds R ![a, b] := Iff.rfl

/-- Decidable, inherited from `Holds`. This is what lets `pairDensity` and the homogeneity
layer consume a model's binary relation without a classical detour. -/
instance (M : FiniteRelModel L V) (R : L.Relations 2) : DecidableRel (M.binaryRel R) :=
  fun a b => inferInstanceAs (Decidable (M.Holds R ![a, b]))

/-- The mathlib structure of a model — an **explicit definition, never a global
instance**. Consumers write `letI := M.toStructure`. -/
@[implicit_reducible]
def toStructure (M : FiniteRelModel L V) : L.Structure V where
  funMap := fun {_} f => isEmptyElim f
  RelMap := fun {_} R x => M.Holds R x

/-- The exact bridge: mathlib's `RelMap` under `toStructure` is `Holds`. -/
theorem toStructure_relMap (M : FiniteRelModel L V) {n : ℕ} (R : L.Relations n)
    (x : Fin n → V) :
    @FirstOrder.Language.Structure.RelMap L V M.toStructure n R x ↔ M.Holds R x :=
  Iff.rfl

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

-- GATE: two distinct models on the same carrier in one theorem; neither is
-- selected implicitly.
example (x : Fin 1 → Fin 2) :
    (⟨fun {_} _ _ => true⟩ : FiniteRelModel (singleRelLang 1) (Fin 2)).Holds
        (singleRelSymbol 1) x
      ∧ ¬(⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 2)).Holds
        (singleRelSymbol 1) x := by
  constructor
  · rfl
  · intro h
    exact Bool.false_ne_true h

-- The RelMap bridge, on both models simultaneously (explicit structures).
example (x : Fin 1 → Fin 2) :
    @FirstOrder.Language.Structure.RelMap _ _
        ((⟨fun {_} _ _ => true⟩ :
          FiniteRelModel (singleRelLang 1) (Fin 2)).toStructure) 1
        (singleRelSymbol 1) x
      ∧ ¬@FirstOrder.Language.Structure.RelMap _ _
        ((⟨fun {_} _ _ => false⟩ :
          FiniteRelModel (singleRelLang 1) (Fin 2)).toStructure) 1
        (singleRelSymbol 1) x := by
  constructor
  · rfl
  · intro h
    exact Bool.false_ne_true h

-- Arity zero on the EMPTY carrier: the one empty tuple satisfies the constantly
-- true nullary relation (permanent adversarial test).
example :
    (⟨fun {_} _ _ => true⟩ : FiniteRelModel (singleRelLang 0) Empty).Holds
      (singleRelSymbol 0) (fun i => i.elim0) := rfl

-- Extensionality at the Holds level, statement-level.
example (M N : FiniteRelModel (singleRelLang 2) (Fin 3))
    (h : ∀ {n : ℕ} (R : (singleRelLang 2).Relations n) (x : Fin n → Fin 3),
      M.Holds R x ↔ N.Holds R x) : M = N :=
  FiniteRelModel.ext_holds h

-- Decidability of Holds closes by decide on a concrete instance (the constant
-- diagonal model: true exactly on constant tuples).
example :
    (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 2) (Fin 2)).Holds (singleRelSymbol 2)
      (fun _ => 0) := by decide

end Tests

end RegularityLemmata
