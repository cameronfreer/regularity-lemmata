/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.TriangleCounting

/-!
# Phase 11 unit 6: five-stratum repeated-cell counting

The placement combinatorics and injective counting bounds for triples whose boxes may
coincide (Phase 11 design freeze in `ARCHITECTURE.md`). Coarse-cell **coincidence** is
kept strictly separate from vertex **collision** throughout: the counted embeddings
are injective in every stratum; only the boxes repeat.

**Exact combinatorics first.** A triple of cells `T : Fin 3 → β` falls into exactly one
of FIVE placement classes (`PlacementClass`): all distinct, exactly `0 = 1`, exactly
`0 = 2`, exactly `1 = 2`, or all equal. The classifying map `placementClass` is total
(exhaustiveness) with disjoint fibers (a function has one value), each class is
characterized (`placementClass_eq_*_iff`), and any sum over triples decomposes
**exactly** over the five strata (`sum_placementClass_fiberwise`) — before any
inequality is stated.

**Analytic bounds second** (same file, second commit): box-restricted collision
estimates, then full-square-density lower bounds for the injective palette-realizing
count in each stratum.
-/

namespace RegularityLemmata

/-! ### The five placement classes -/

/-- The five placement classes of a triple: all coordinates distinct; exactly one of
the three coincidences `0 = 1`, `0 = 2`, `1 = 2`; or all equal. -/
inductive PlacementClass : Type
  /-- All three coordinates distinct. -/
  | allDistinct : PlacementClass
  /-- Exactly `0 = 1` (and both differ from `2`). -/
  | eq01 : PlacementClass
  /-- Exactly `0 = 2` (and both differ from `1`). -/
  | eq02 : PlacementClass
  /-- Exactly `1 = 2` (and both differ from `0`). -/
  | eq12 : PlacementClass
  /-- All three coordinates equal. -/
  | allEqual : PlacementClass
  deriving DecidableEq, Repr

instance : Fintype PlacementClass :=
  ⟨{.allDistinct, .eq01, .eq02, .eq12, .allEqual}, fun c => by cases c <;> decide⟩

variable {β : Type*} [DecidableEq β]

/-- The placement class of a triple. Totality of this map is the exhaustiveness of the
five strata; disjointness is automatic (a function takes one value). -/
def placementClass (T : Fin 3 → β) : PlacementClass :=
  if T 0 = T 1 then (if T 1 = T 2 then .allEqual else .eq01)
  else if T 0 = T 2 then .eq02
  else if T 1 = T 2 then .eq12
  else .allDistinct

/-! ### Characterizations (the disjointness content, made explicit) -/

omit [DecidableEq β] in
/-- Injectivity of a `Fin 3`-triple is the conjunction of the three disequalities
(the Graph-layer counterpart of the relational collision characterization). -/
theorem injective_fin_three_iff {T : Fin 3 → β} :
    Function.Injective T ↔ T 0 ≠ T 1 ∧ T 0 ≠ T 2 ∧ T 1 ≠ T 2 := by
  constructor
  · intro h
    exact ⟨fun e => absurd (h e) (by decide), fun e => absurd (h e) (by decide),
      fun e => absurd (h e) (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ a b hab
    fin_cases a <;> fin_cases b <;> simp_all

theorem placementClass_eq_allDistinct_iff {T : Fin 3 → β} :
    placementClass T = .allDistinct ↔ T 0 ≠ T 1 ∧ T 0 ≠ T 2 ∧ T 1 ≠ T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_allDistinct_iff_injective {T : Fin 3 → β} :
    placementClass T = .allDistinct ↔ Function.Injective T := by
  rw [placementClass_eq_allDistinct_iff, injective_fin_three_iff]

theorem placementClass_eq_allEqual_iff {T : Fin 3 → β} :
    placementClass T = .allEqual ↔ T 0 = T 1 ∧ T 1 = T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq01_iff {T : Fin 3 → β} :
    placementClass T = .eq01 ↔ T 0 = T 1 ∧ T 1 ≠ T 2 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq02_iff {T : Fin 3 → β} :
    placementClass T = .eq02 ↔ T 0 = T 2 ∧ T 0 ≠ T 1 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all

theorem placementClass_eq_eq12_iff {T : Fin 3 → β} :
    placementClass T = .eq12 ↔ T 1 = T 2 ∧ T 0 ≠ T 1 := by
  rw [placementClass]
  split_ifs with h01 h12 h02 h12' <;> simp_all
  exact fun h => h01 h.symm

/-- In the two one-coincidence strata that omit it, the third pair is automatically
distinct: `eq01` forces `T 0 ≠ T 2`, … -/
theorem ne_of_placementClass_eq_eq01 {T : Fin 3 → β}
    (h : placementClass T = .eq01) : T 0 ≠ T 2 := by
  rw [placementClass_eq_eq01_iff] at h
  exact fun h02 => h.2 (h.1.symm.trans h02)

/-- … and `eq12` forces `T 0 ≠ T 2`. -/
theorem ne_of_placementClass_eq_eq12 {T : Fin 3 → β}
    (h : placementClass T = .eq12) : T 0 ≠ T 2 := by
  rw [placementClass_eq_eq12_iff] at h
  exact fun h02 => h.2 (h02.trans h.1.symm)

/-! ### The exact five-stratum decomposition -/

/-- **The exact decomposition.** Any sum over a finite set of triples splits exactly
over the five placement strata — disjointness and exhaustiveness in one identity,
before any inequality. -/
theorem sum_placementClass_fiberwise {M : Type*} [AddCommMonoid M]
    (S : Finset (Fin 3 → β)) (f : (Fin 3 → β) → M) :
    ∑ c : PlacementClass, ∑ T ∈ S.filter (fun T => placementClass T = c), f T
      = ∑ T ∈ S, f T :=
  Finset.sum_fiberwise S placementClass f

/-! ### Tests and adversarial examples -/

section Tests

-- The classifier is exhaustive and computes on the nose.
example : placementClass (![0, 1, 2] : Fin 3 → Fin 3) = .allDistinct := by decide
example : placementClass (![0, 0, 2] : Fin 3 → Fin 3) = .eq01 := by decide
example : placementClass (![0, 1, 0] : Fin 3 → Fin 3) = .eq02 := by decide
example : placementClass (![0, 1, 1] : Fin 3 → Fin 3) = .eq12 := by decide
example : placementClass (![1, 1, 1] : Fin 3 → Fin 3) = .allEqual := by decide

-- Disjointness, concretely: no triple lies in two strata (the classifier is a
-- function), and each characterization excludes the others.
example (T : Fin 3 → Fin 5) : ¬(placementClass T = .eq01 ∧ placementClass T = .eq02) :=
  fun ⟨h1, h2⟩ => by rw [h1] at h2; exact absurd h2 (by decide)

-- The exact decomposition on a concrete sum: counting all 27 triples of `Fin 3` by
-- stratum gives 6 + 6 + 6 + 6 + 3 = 27.
example :
    (((Finset.univ : Finset (Fin 3 → Fin 3))).filter
        (fun T => placementClass T = .allDistinct)).card = 6 ∧
      ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
        (fun T => placementClass T = .eq01)).card = 6 ∧
      ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
        (fun T => placementClass T = .allEqual)).card = 3 := by decide

example :
    ∑ c : PlacementClass, ((Finset.univ : Finset (Fin 3 → Fin 3)).filter
      (fun T => placementClass T = c)).card = 27 := by decide

end Tests

end RegularityLemmata
