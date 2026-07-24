/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Graph.Atomise
import RegularityLemmata.Graph.FamilyRegularity

/-!
# Equitable-supplier ladder, step 3 (construction)

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence step 3,
**construction half**: the equitabilised one-step refinement of an equipartition, with
its exact combinatorics — part counts and part sizes — established before any density or
energy estimate is attempted. The approximation half (how much of a witness side the
chunks recover) is a separate unit.

The construction follows mathlib's `SzemerediRegularity.chunk` architecture
(`Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk`), adapted in three ways: the host
is an arbitrary `s : Finset α` rather than `univ`; the relation is an arbitrary DIRECTED
`R` (via `witnessCuts` from `Graph/Atomise.lean`), so no symmetry is used; and the number
of chunks per parent is the ladder's own `familyChunksPerPart #P.parts` rather than
mathlib's `4 ^ #P.parts`.

* `chunkSize P` (mathlib's `m`) and `chunkRem P` (mathlib's `a`) are the numerical data of
  one step: `chunkSize P * familyChunksPerPart #P.parts + chunkRem P = #s / #P.parts`
  (`chunkSize_mul_add_chunkRem`), with `chunkRem P < familyChunksPerPart #P.parts`. Because
  `P` is an equipartition, every parent cell has size `chunkSize P * familyChunksPerPart
  #P.parts + chunkRem P` or one more, which is exactly the shape `Finpartition.equitabilise`
  consumes (`chunk_card_aux₁` / `chunk_card_aux₂`).
* `equitableChunk R ε hP hC : Finpartition C` — the local chunking of the parent cell `C`:
  equitabilise the cell's own witness atomisation `Finpartition.atomise C (witnessCuts R ε P C)`
  into **exactly** `familyChunksPerPart #P.parts` chunks (`card_equitableChunk_parts`), each of
  the common global size `chunkSize P` or `chunkSize P + 1` (`card_equitableChunk_part`).
* `equitableIncrement R ε hP : Finpartition s` — the global bind of the local chunkings. It
  refines `P` (`equitableIncrement_le`, immediate since each chunk sits inside its parent),
  has **exactly** `familyStepBound #P.parts` parts (`card_equitableIncrement_parts`), and is an
  equipartition (`equitableIncrement_isEquipartition`).
* Host-size and positivity: `familyStepBound #P.parts ≤ #s` is the single hypothesis that
  makes the step nondegenerate. It gives `0 < chunkSize P` (`chunkSize_pos`) and, per parent
  cell, `familyChunksPerPart #P.parts ≤ #C` (`familyChunksPerPart_le_card_part`) — the room
  needed to create the prescribed number of nonempty chunks in every cell.

**Two layers, deliberately kept separate.** Equitabilisation is *applied to* the atom
partition, but it does **not refine** it: a chunk may straddle an atom boundary, and no
`equitableIncrement R ε hP ≤ witnessRefinement R ε P` is claimed here — it is false in
general (the phenomenon is exhibited concretely in the tests below, on a hand-built
equitable partition rather than on the choice-produced one, which is opaque). The atom
partition's job is to certify that every chosen witness side is a union of atoms
(`witnessRefinement_resolves`); the separate approximation unit then upgrades that to "every
witness side is, up to a bounded remainder, a union of chunks", via mathlib's
`Finpartition.card_parts_equitabilise_subset_le`. Keeping the certifying layer (atoms) and
the produced layer (chunks) distinct is what makes the step-4 energy accounting readable.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

/-! ### The numerical data of one step -/

/-- The common chunk size `m`: the host size divided by the exact number of chunks
`familyStepBound #P.parts` that one step produces. -/
def chunkSize (P : Finpartition s) : ℕ :=
  s.card / familyStepBound P.parts.card

/-- The per-parent remainder `a`: the number of chunks in a parent cell that must be one
element larger than the common size. -/
def chunkRem (P : Finpartition s) : ℕ :=
  s.card / P.parts.card % familyChunksPerPart P.parts.card

variable {P : Finpartition s}

theorem chunkRem_lt : chunkRem P < familyChunksPerPart P.parts.card :=
  Nat.mod_lt _ (familyChunksPerPart_pos _)

/-- The parent cell size decomposition: the average cell size splits into
`familyChunksPerPart #P.parts` chunks of size `chunkSize P`, plus the remainder. -/
theorem chunkSize_mul_add_chunkRem :
    chunkSize P * familyChunksPerPart P.parts.card + chunkRem P = s.card / P.parts.card := by
  rw [chunkSize, chunkRem, familyStepBound, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

/-- The arithmetic shape `Finpartition.equitabilise` consumes: a set of size `m * q + a`
splits into `q - a` parts of size `m` and `a` parts of size `m + 1`. -/
private theorem equitabilise_card_aux {q a m N : ℕ} (ha : a ≤ q) (h : N = m * q + a) :
    (q - a) * m + a * (m + 1) = N := by
  subst h
  rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel ha,
    Nat.mul_comm]

/-- A parent cell of average size is chunked as `q - a` chunks of size `m` and `a` of size
`m + 1` (mathlib's `card_aux₁`). -/
theorem chunk_card_aux₁ {C : Finset α}
    (hC : C.card = chunkSize P * familyChunksPerPart P.parts.card + chunkRem P) :
    (familyChunksPerPart P.parts.card - chunkRem P) * chunkSize P
      + chunkRem P * (chunkSize P + 1) = C.card :=
  equitabilise_card_aux chunkRem_lt.le hC

/-- A parent cell one larger than average is chunked as `q - (a + 1)` chunks of size `m` and
`a + 1` of size `m + 1` (mathlib's `card_aux₂`). The equipartition hypothesis is what rules
out every other cell size. -/
theorem chunk_card_aux₂ (hP : P.IsEquipartition) {C : Finset α} (hC : C ∈ P.parts)
    (hCcard : C.card ≠ chunkSize P * familyChunksPerPart P.parts.card + chunkRem P) :
    (familyChunksPerPart P.parts.card - (chunkRem P + 1)) * chunkSize P
      + (chunkRem P + 1) * (chunkSize P + 1) = C.card := by
  refine equitabilise_card_aux chunkRem_lt ?_
  rcases hP.card_parts_eq_average hC with h | h
  · exact absurd (h.trans chunkSize_mul_add_chunkRem.symm) hCcard
  · rw [h, ← chunkSize_mul_add_chunkRem, Nat.add_assoc]

/-! ### Positivity and host-size room -/

theorem familyStepBound_pos_of_mem {C : Finset α} (hC : C ∈ P.parts) :
    0 < familyStepBound P.parts.card :=
  familyStepBound_pos (Finset.card_pos.mpr ⟨C, hC⟩)

/-- **The step is nondegenerate exactly when the host is large enough**: if the host admits
the step's part count, the common chunk size is positive. This is what lets
`Finpartition.card_parts_equitabilise` count parts. -/
theorem chunkSize_pos {C : Finset α} (hC : C ∈ P.parts)
    (hs : familyStepBound P.parts.card ≤ s.card) : 0 < chunkSize P :=
  Nat.div_pos hs (familyStepBound_pos_of_mem hC)

/-- **Room for the prescribed chunks**: if the host admits the step's part count, then EVERY
cell of the equipartition is at least as large as the number of chunks it must be cut into.
This is the positivity needed to create `familyChunksPerPart #P.parts` nonempty local
chunks. -/
theorem familyChunksPerPart_le_card_part (hP : P.IsEquipartition)
    (hs : familyStepBound P.parts.card ≤ s.card) {C : Finset α} (hC : C ∈ P.parts) :
    familyChunksPerPart P.parts.card ≤ C.card := by
  have hm : 1 ≤ chunkSize P := chunkSize_pos hC hs
  calc familyChunksPerPart P.parts.card
      = 1 * familyChunksPerPart P.parts.card := (Nat.one_mul _).symm
    _ ≤ chunkSize P * familyChunksPerPart P.parts.card :=
        Nat.mul_le_mul_right _ hm
    _ ≤ chunkSize P * familyChunksPerPart P.parts.card + chunkRem P := Nat.le_add_right _ _
    _ = s.card / P.parts.card := chunkSize_mul_add_chunkRem
    _ ≤ C.card := hP.average_le_card_part hC

/-! ### The local chunking of a parent cell -/

/-- **The local chunk**: equitabilise the parent cell's own witness atomisation into exactly
`familyChunksPerPart #P.parts` chunks of the common global size `chunkSize P` or
`chunkSize P + 1`. The case split is on whether `C` has average size or one more; the
equipartition hypothesis `hP` is what makes the second branch's arithmetic available.

This is a `Finpartition C`, so every chunk is a subset of its parent by construction — the
source of `equitableIncrement_le`. It is NOT a refinement of the atomisation it is built
from; see the module docstring. -/
noncomputable def equitableChunk (hP : P.IsEquipartition) {C : Finset α} (hC : C ∈ P.parts) :
    Finpartition C :=
  if hCcard : C.card = chunkSize P * familyChunksPerPart P.parts.card + chunkRem P then
    (Finpartition.atomise C (witnessCuts R ε P C)).equitabilise (chunk_card_aux₁ hCcard)
  else
    (Finpartition.atomise C (witnessCuts R ε P C)).equitabilise (chunk_card_aux₂ hP hC hCcard)

/-- **Every chunk has the common global size** `chunkSize P` or `chunkSize P + 1` — the same
`chunkSize P` in every parent cell, which is what makes the global result an equipartition. -/
theorem card_equitableChunk_part (hP : P.IsEquipartition) {C : Finset α} (hC : C ∈ P.parts)
    {t : Finset α} (ht : t ∈ (equitableChunk R ε hP hC).parts) :
    t.card = chunkSize P ∨ t.card = chunkSize P + 1 := by
  rw [equitableChunk] at ht
  split_ifs at ht <;> exact Finpartition.card_eq_of_mem_parts_equitabilise ht

/-- **Exactly `familyChunksPerPart #P.parts` chunks in every parent cell** — the same count
in each, which is what makes the global part count exact. -/
theorem card_equitableChunk_parts (hP : P.IsEquipartition)
    (hs : familyStepBound P.parts.card ≤ s.card) {C : Finset α} (hC : C ∈ P.parts) :
    (equitableChunk R ε hP hC).parts.card = familyChunksPerPart P.parts.card := by
  have hm : chunkSize P ≠ 0 := (chunkSize_pos hC hs).ne'
  rw [equitableChunk]
  split_ifs with hCcard
  · rw [Finpartition.card_parts_equitabilise _ _ hm]
    exact Nat.sub_add_cancel chunkRem_lt.le
  · rw [Finpartition.card_parts_equitabilise _ _ hm]
    exact Nat.sub_add_cancel chunkRem_lt

/-! ### The global equitabilised increment -/

/-- **The equitabilised increment**: the bind of the per-parent chunkings. Every cell of the
equipartition `P` is cut into the same number of chunks of the same global size. -/
noncomputable def equitableIncrement (hP : P.IsEquipartition) : Finpartition s :=
  P.bind fun _ hC => equitableChunk R ε hP hC

theorem mem_equitableIncrement {hP : P.IsEquipartition} {b : Finset α} :
    b ∈ (equitableIncrement R ε hP).parts ↔
      ∃ C, ∃ hC : C ∈ P.parts, b ∈ (equitableChunk R ε hP hC).parts :=
  Finpartition.mem_bind

/-- **The increment refines the parent partition.** Immediate: each chunk is a part of a
`Finpartition C` for a cell `C` of `P`. No claim about the atomisation is made. -/
theorem equitableIncrement_le (hP : P.IsEquipartition) : equitableIncrement R ε hP ≤ P := by
  intro b hb
  obtain ⟨C, hC, hb⟩ := (mem_equitableIncrement R ε).mp hb
  exact ⟨C, hC, (equitableChunk R ε hP hC).le hb⟩

/-- Every part of the increment has the common size `chunkSize P` or `chunkSize P + 1`. -/
theorem card_equitableIncrement_part (hP : P.IsEquipartition) {b : Finset α}
    (hb : b ∈ (equitableIncrement R ε hP).parts) :
    b.card = chunkSize P ∨ b.card = chunkSize P + 1 := by
  obtain ⟨C, hC, hb⟩ := (mem_equitableIncrement R ε).mp hb
  exact card_equitableChunk_part R ε hP hC hb

/-- **The increment is an equipartition** — with the same `chunkSize P` across all parents. -/
theorem equitableIncrement_isEquipartition (hP : P.IsEquipartition) :
    (equitableIncrement R ε hP).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2
    ⟨chunkSize P, fun _ hb => card_equitableIncrement_part R ε hP hb⟩

/-- **The exact global part count**: `#P.parts` parents, each cut into
`familyChunksPerPart #P.parts` chunks, is exactly the step bound
`familyStepBound #P.parts` the numerical schedule iterates. -/
theorem card_equitableIncrement_parts (hP : P.IsEquipartition)
    (hs : familyStepBound P.parts.card ≤ s.card) :
    (equitableIncrement R ε hP).parts.card = familyStepBound P.parts.card := by
  rw [equitableIncrement, Finpartition.card_bind]
  rw [Finset.sum_congr rfl fun C _ => card_equitableChunk_parts R ε hP hs C.2]
  rw [Finset.sum_const, Finset.card_attach, smul_eq_mul, familyStepBound]

/-! ### Tests and adversarial examples -/

section Tests

-- The degenerate regime the host-size hypothesis excludes: on a one-element host the
-- discrete partition has one cell but the step demands `familyStepBound 1 = 1024` chunks,
-- so the common chunk size collapses to `0` and no part count can be exact.
example : chunkSize (⊥ : Finpartition (Finset.univ : Finset (Fin 1))) = 0 := by
  have h : familyStepBound (⊥ : Finpartition (Finset.univ : Finset (Fin 1))).parts.card
      = 1024 := by decide
  rw [chunkSize, h]
  decide

-- The remainder is always a genuine remainder: strictly below the per-parent chunk count.
example (P : Finpartition (Finset.univ : Finset (Fin 5))) :
    chunkRem P < familyChunksPerPart P.parts.card := chunkRem_lt

-- The cell-size decomposition, as consumed by `equitabilise`.
example (P : Finpartition (Finset.univ : Finset (Fin 5))) :
    chunkSize P * familyChunksPerPart P.parts.card + chunkRem P
      = (Finset.univ : Finset (Fin 5)).card / P.parts.card := chunkSize_mul_add_chunkRem

-- **The chunk-crossing phenomenon.** The host `{0,1,2,3}` atomised by the single cut
-- `{0}` has the two atoms `{0}` and `{1,2,3}`, of unequal sizes 1 and 3: the atom layer is
-- never equitable, which is exactly why a separate chunk layer is needed.
example :
    (Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}}).parts = {{0}, {1, 2, 3}} := by
  decide

-- ... and a genuinely equitable partition of that host — all parts of the common size 2 —
-- CROSSES an atom boundary: `{0,1}` lies inside neither atom. The witness is hand-built
-- (`twoPartition` into `{0,1}` and `{2,3}`) because the production chunking comes from
-- `Finpartition.equitabilise`, which is defined by choice and computes nothing. So an
-- equitabilisation of an atom partition need NOT refine it: no
-- `equitableIncrement ≤ witnessRefinement` is claimed anywhere above, and the separate
-- approximation unit must instead work with the guaranteed bounded remainder.
example :
    (twoPartition ({0, 1, 2, 3} : Finset (Fin 4)) {0, 1} (by decide) (by decide)
      (by decide)).IsEquipartition := by
  refine Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨2, fun t ht => ?_⟩
  rw [Finset.mem_coe, twoPartition_parts] at ht
  revert ht
  revert t
  decide

example :
    ¬ twoPartition ({0, 1, 2, 3} : Finset (Fin 4)) {0, 1} (by decide) (by decide) (by decide)
      ≤ Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}} := by
  intro hle
  obtain ⟨D, hD, hsub⟩ :=
    hle (show ({0, 1} : Finset (Fin 4)) ∈ _ by rw [twoPartition_parts]; decide)
  have hno : ∀ D : Finset (Fin 4),
      D ∈ (Finpartition.atomise ({0, 1, 2, 3} : Finset (Fin 4)) {{0}}).parts →
        ¬ ({0, 1} : Finset (Fin 4)) ⊆ D := by decide
  exact hno D hD hsub

end Tests

end RegularityLemmata
