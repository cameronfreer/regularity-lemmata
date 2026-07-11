/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.Counts

/-!
# Homomorphism and induced-embedding counts

Phase 8 unit 6 (design freeze in `ARCHITECTURE.md`): pattern maps and their three
**visibly distinct** counts. `Preserves` and `PreservesAndReflects` quantify
computationally over the bounded symbol type `RelSymbol`, with proved equivalences
to the unbounded mathlib formulation (via emptiness above the bound). The counts:

* `homCount` — all relation-preserving functions;
* `injectiveHomCount` — injective relation-preserving functions;
* `inducedEmbeddingCount` — injective functions preserving **and reflecting**
  every relation. Not called "copyCount": relational inducedness is
  diagonal-sensitive and includes nullary symbols.

Conversions land in mathlib's `Language.Hom` (preserves) and `Language.Embedding`
(preserves and reflects — `Mathlib.ModelTheory.Basic`), with converse
characterizations, under explicit `letI := ·.toStructure` structures.

Host monotonicity holds for the positive homomorphism counts only — the
adversarial tests show added host relations destroying induced embeddings, a
nullary mismatch zeroing every homomorphism count, and a noninjective
homomorphism existing where no injective one does.
-/

namespace RegularityLemmata

open FirstOrder

namespace FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V W V' W' : Type*}

/-- Relation preservation, quantified over the bounded symbol type. -/
def Preserves (P : FiniteRelModel L W) (M : FiniteRelModel L V) (f : W → V) :
    Prop :=
  ∀ (s : RelSymbol L) (x : Fin (s.1 : ℕ) → W),
    P.Holds s.2 x → M.Holds s.2 (f ∘ x)

/-- Relation preservation and reflection, quantified over the bounded symbol
type. -/
def PreservesAndReflects (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    (f : W → V) : Prop :=
  ∀ (s : RelSymbol L) (x : Fin (s.1 : ℕ) → W),
    P.Holds s.2 x ↔ M.Holds s.2 (f ∘ x)

/-- The bounded quantification is equivalent to the unbounded one. -/
theorem preserves_iff_forall (P : FiniteRelModel L W) (M : FiniteRelModel L V)
    (f : W → V) :
    Preserves P M f
      ↔ ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → W),
          P.Holds R x → M.Holds R (f ∘ x) := by
  constructor
  · intro h n R x
    exact h (RelSymbol.mk' R) x
  · intro h s x
    exact h s.2 x

/-- The bounded reflection is equivalent to the unbounded one. -/
theorem preservesAndReflects_iff_forall (P : FiniteRelModel L W)
    (M : FiniteRelModel L V) (f : W → V) :
    PreservesAndReflects P M f
      ↔ ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → W),
          P.Holds R x ↔ M.Holds R (f ∘ x) := by
  constructor
  · intro h n R x
    exact h (RelSymbol.mk' R) x
  · intro h s x
    exact h s.2 x

instance (P : FiniteRelModel L W) (M : FiniteRelModel L V) (f : W → V)
    [Fintype W] : Decidable (Preserves P M f) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))

instance (P : FiniteRelModel L W) (M : FiniteRelModel L V) (f : W → V)
    [Fintype W] : Decidable (PreservesAndReflects P M f) :=
  inferInstanceAs (Decidable (∀ _ _, _ ↔ _))

variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-- All relation-preserving functions. -/
def homCount (P : FiniteRelModel L W) (M : FiniteRelModel L V) : ℕ :=
  (Finset.univ.filter fun f : W → V => Preserves P M f).card

/-- Injective relation-preserving functions. -/
def injectiveHomCount (P : FiniteRelModel L W) (M : FiniteRelModel L V) : ℕ :=
  (Finset.univ.filter fun f : W → V =>
    Function.Injective f ∧ Preserves P M f).card

/-- Injective functions preserving **and reflecting** every relation
(diagonal-sensitive; includes nullary symbols). -/
def inducedEmbeddingCount (P : FiniteRelModel L W) (M : FiniteRelModel L V) : ℕ :=
  (Finset.univ.filter fun f : W → V =>
    Function.Injective f ∧ PreservesAndReflects P M f).card

theorem injectiveHomCount_le_homCount (P : FiniteRelModel L W)
    (M : FiniteRelModel L V) : injectiveHomCount P M ≤ homCount P M := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.2⟩

theorem inducedEmbeddingCount_le_injectiveHomCount (P : FiniteRelModel L W)
    (M : FiniteRelModel L V) :
    inducedEmbeddingCount P M ≤ injectiveHomCount P M := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.1, fun s x hx => (hf.2.2 s x).mp hx⟩

omit [DecidableEq V] in
/-- Empty language: every function preserves vacuously. -/
theorem homCount_empty_language (P : FiniteRelModel FirstOrder.Language.empty W)
    (M : FiniteRelModel FirstOrder.Language.empty V) :
    homCount P M = Fintype.card V ^ Fintype.card W := by
  rw [homCount, Finset.filter_true_of_mem fun f _ s => s.2.elim,
    Finset.card_univ, Fintype.card_fun]

/-- Empty language: the injective counts are the falling factorial. -/
theorem injectiveHomCount_empty_language
    (P : FiniteRelModel FirstOrder.Language.empty W)
    (M : FiniteRelModel FirstOrder.Language.empty V) :
    injectiveHomCount P M = (Fintype.card V).descFactorial (Fintype.card W) := by
  classical
  rw [injectiveHomCount]
  have hcongr : (Finset.univ.filter fun f : W → V =>
      Function.Injective f ∧ Preserves P M f)
      = Finset.univ.filter fun f : W → V => Function.Injective f := by
    refine Finset.filter_congr fun f _ => ?_
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun s => s.2.elim⟩
  rw [hcongr, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding W V),
    Fintype.card_embedding_eq]

omit [DecidableEq V] in
/-- Host monotonicity for the positive homomorphism count: more host relations,
more homomorphisms. NOT stated for induced embeddings (see the adversarial
test). -/
theorem homCount_mono_host {P : FiniteRelModel L W} {M M' : FiniteRelModel L V}
    (h : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → V),
      M.Holds R x → M'.Holds R x) :
    homCount P M ≤ homCount P M' := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, fun s x hx => h s.2 _ (hf.2 s x hx)⟩

/-! ### Mathlib conversions (explicit structures) -/

/-- A preservation proof is a mathlib homomorphism (under explicit structures). -/
def Preserves.toHom {P : FiniteRelModel L W} {M : FiniteRelModel L V} {f : W → V}
    (h : Preserves P M f) :
    letI := P.toStructure
    letI := M.toStructure
    W →[L] V := by
  letI := P.toStructure
  letI := M.toStructure
  exact
    { toFun := f
      map_fun' := fun {_} F => isEmptyElim F
      map_rel' := fun {_} R x hx => (preserves_iff_forall P M f).mp h R x hx }

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] in
/-- Conversely, a mathlib homomorphism preserves. -/
theorem preserves_of_hom {P : FiniteRelModel L W} {M : FiniteRelModel L V}
    (h : letI := P.toStructure
         letI := M.toStructure
         W →[L] V) :
    Preserves P M (@FirstOrder.Language.Hom.toFun L W V
      P.toStructure M.toStructure h) := by
  letI := P.toStructure
  letI := M.toStructure
  exact fun s x hx => h.map_rel' s.2 x hx

/-- An injective preservation-and-reflection proof is a mathlib embedding. -/
def PreservesAndReflects.toEmbedding {P : FiniteRelModel L W}
    {M : FiniteRelModel L V} {f : W → V} (hinj : Function.Injective f)
    (h : PreservesAndReflects P M f) :
    letI := P.toStructure
    letI := M.toStructure
    W ↪[L] V := by
  letI := P.toStructure
  letI := M.toStructure
  exact
    { toFun := f
      inj' := hinj
      map_fun' := fun {_} F => isEmptyElim F
      map_rel' := fun {_} R x =>
        ((preservesAndReflects_iff_forall P M f).mp h R x).symm }

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] in
/-- Conversely, a mathlib embedding preserves and reflects (and is injective). -/
theorem preservesAndReflects_of_embedding {P : FiniteRelModel L W}
    {M : FiniteRelModel L V}
    (h : letI := P.toStructure
         letI := M.toStructure
         W ↪[L] V) :
    Function.Injective ⇑(@FirstOrder.Language.Embedding.toEmbedding L W V
        P.toStructure M.toStructure h)
      ∧ PreservesAndReflects P M ⇑(@FirstOrder.Language.Embedding.toEmbedding
          L W V P.toStructure M.toStructure h) := by
  letI := P.toStructure
  letI := M.toStructure
  exact ⟨h.toEmbedding.injective, fun s x => (h.map_rel' s.2 x).symm⟩

end FiniteRelModel

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- Adding host relations increases the homomorphism count but DESTROYS induced
-- embeddings: pattern = single loose vertex pair with the relation false; a fully
-- true host admits homs but reflects nothing.
example :
    inducedEmbeddingCount
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 1))
      (⟨fun {_} _ _ => true⟩ : FiniteRelModel (singleRelLang 1) (Fin 2)) = 0 := by
  decide

example :
    0 < homCount
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 1))
      (⟨fun {_} _ _ => true⟩ : FiniteRelModel (singleRelLang 1) (Fin 2)) := by
  decide

-- A nullary mismatch zeroes every homomorphism count: the pattern asserts the
-- nullary relation, the host denies it, and no function can repair it.
example :
    homCount
      (⟨fun {_} _ _ => true⟩ : FiniteRelModel (singleRelLang 0) (Fin 1))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 0) (Fin 1)) = 0 := by
  decide

-- The diagonal relation distinguishes ordered relational embeddings from
-- hypergraph copies: a pattern whose relation holds on the constant pair demands
-- a host diagonal, which the strict-inequality host cannot reflect.
example :
    inducedEmbeddingCount
      (⟨fun {_} _ x => decide (∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 1))
      (⟨fun {_} _ x => decide (¬∀ i j, x i = x j)⟩ :
        FiniteRelModel (singleRelLang 2) (Fin 2)) = 0 := by
  decide

-- A noninjective homomorphism can exist when no injective one does: two loose
-- vertices map onto one.
example :
    0 < homCount
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 2))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 1)) := by
  decide

example :
    injectiveHomCount
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 2))
      (⟨fun {_} _ _ => false⟩ : FiniteRelModel (singleRelLang 1) (Fin 1)) = 0 := by
  decide

end Tests

end RegularityLemmata
