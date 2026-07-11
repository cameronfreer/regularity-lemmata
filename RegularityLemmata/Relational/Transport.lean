/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Model

/-!
# Transport: pullback, restriction, relabeling

Phase 8 unit 3 (design freeze in `ARCHITECTURE.md`), built **before** any counting.
The primitive is `pullback` along an arbitrary map, with the frozen direction

`(pullback M f).Holds R x ↔ M.Holds R (f ∘ x)`.

`restrict` is pullback along the subtype inclusion of a `Finset` carrier — for
relational languages every subset is structurally admissible, so no mathlib
substructure machinery is imported. `relabel` is pullback along `e.symm`, with
identity and composition laws and relation-level compatibility with mathlib's
`Equiv.inducedStructure` (`Mathlib.ModelTheory.Basic`).

**Falsification note**: pullback along a noninjective map is allowed — and no
theorem here (or later) claims it preserves injective counts or induced
embeddings; the adversarial test below shows a relation surviving on injective
tuples being emptied by a constant pullback.
-/

namespace RegularityLemmata

open FirstOrder

namespace FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V W X : Type*}

/-- Pullback along an arbitrary map (the frozen direction: transported truth is
truth of the image tuple). -/
def pullback (M : FiniteRelModel L V) (f : W → V) : FiniteRelModel L W :=
  ⟨fun {_} R x => M.rel R (f ∘ x)⟩

@[simp] theorem pullback_holds (M : FiniteRelModel L V) (f : W → V) {n : ℕ}
    (R : L.Relations n) (x : Fin n → W) :
    (M.pullback f).Holds R x ↔ M.Holds R (f ∘ x) :=
  Iff.rfl

theorem pullback_id (M : FiniteRelModel L V) : M.pullback id = M :=
  ext_holds fun _ _ => Iff.rfl

theorem pullback_comp (M : FiniteRelModel L V) (f : W → V) (g : X → W) :
    (M.pullback f).pullback g = M.pullback (f ∘ g) :=
  ext_holds fun _ _ => Iff.rfl

/-- Restriction to a finite subcarrier: pullback along the subtype inclusion. -/
def restrict (M : FiniteRelModel L V) (S : Finset V) :
    FiniteRelModel L {x // x ∈ S} :=
  M.pullback Subtype.val

/-- Restriction is pullback along the inclusion, definitionally. -/
theorem restrict_eq_pullback (M : FiniteRelModel L V) (S : Finset V) :
    M.restrict S = M.pullback Subtype.val :=
  rfl

theorem restrict_holds (M : FiniteRelModel L V) (S : Finset V) {n : ℕ}
    (R : L.Relations n) (x : Fin n → {y // y ∈ S}) :
    (M.restrict S).Holds R x ↔ M.Holds R fun i => (x i : V) :=
  Iff.rfl

/-- Relabeling along an equivalence: pullback along `e.symm`. -/
def relabel (M : FiniteRelModel L V) (e : V ≃ W) : FiniteRelModel L W :=
  M.pullback e.symm

/-- Relabeling is pullback along the inverse, definitionally. -/
theorem relabel_eq_pullback (M : FiniteRelModel L V) (e : V ≃ W) :
    M.relabel e = M.pullback e.symm :=
  rfl

theorem relabel_holds (M : FiniteRelModel L V) (e : V ≃ W) {n : ℕ}
    (R : L.Relations n) (x : Fin n → W) :
    (M.relabel e).Holds R x ↔ M.Holds R fun i => e.symm (x i) :=
  Iff.rfl

theorem relabel_refl (M : FiniteRelModel L V) : M.relabel (Equiv.refl V) = M :=
  ext_holds fun _ _ => Iff.rfl

theorem relabel_trans (M : FiniteRelModel L V) (e : V ≃ W) (f : W ≃ X) :
    M.relabel (e.trans f) = (M.relabel e).relabel f :=
  ext_holds fun _ _ => Iff.rfl

/-- Relation-level compatibility with mathlib's induced structure: relabeling and
`Equiv.inducedStructure` interpret every relation identically (the function side
is empty for relational languages). -/
theorem relabel_toStructure_relMap (M : FiniteRelModel L V) (e : V ≃ W) {n : ℕ}
    (R : L.Relations n) (x : Fin n → W) :
    @FirstOrder.Language.Structure.RelMap L W (M.relabel e).toStructure n R x
      ↔ @FirstOrder.Language.Structure.RelMap L W
          (@Equiv.inducedStructure L V W M.toStructure e) n R x :=
  Iff.rfl

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- The frozen pullback direction, statement-level.
example (M : FiniteRelModel (singleRelLang 2) (Fin 3)) (f : Fin 2 → Fin 3)
    (x : Fin 2 → Fin 2) :
    (M.pullback f).Holds (singleRelSymbol 2) x
      ↔ M.Holds (singleRelSymbol 2) (f ∘ x) :=
  pullback_holds M f _ x

-- Adversarial falsification: pullback along a CONSTANT (noninjective) map empties
-- a strict inequality relation — nothing about injective structure survives.
example :
    ¬((⟨fun {_} _ x => decide (¬∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 2)).pullback
          (fun _ : Fin 2 => (0 : Fin 2))).Holds (singleRelSymbol 2)
      (fun i => i) := by decide

-- …while the original model does hold on an injective tuple.
example :
    (⟨fun {_} _ x => decide (¬∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 2) (Fin 2)).Holds (singleRelSymbol 2)
      (fun i => i) := by decide

-- Relabeling round-trips, statement-level.
example (M : FiniteRelModel (singleRelLang 1) (Fin 3)) :
    M.relabel (Equiv.refl (Fin 3)) = M :=
  relabel_refl M

-- Restriction agrees with the inclusion pullback on a concrete instance (kernel
-- decide through the subtype).
example :
    ((⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
      FiniteRelModel (singleRelLang 1) (Fin 3)).restrict {0, 1}).Holds
      (singleRelSymbol 1) (fun _ => ⟨0, by decide⟩) := by decide

end Tests

end RegularityLemmata
