/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Relational.BinaryPalette
import RegularityLemmata.Partition.Grouping

/-!
# Route (b) ladder step 2: the proxy-pair event index

`ARCHITECTURE.md` route (b) ladder step 2 (grouping frozen 2026-07-28). Representative
selection is to be rebuilt over ordered distinct PROXY pairs. This file supplies the new
event index and derives its size — the step the frozen record requires **before** any
tolerance is chosen — and nothing else.

## What changes

The role-indexed selection of `Relational/RepresentativeSelection.lean` indexes events by

    (large coarse cell × large coarse cell) × (ordered distinct role pair × palette)

carrying a `6·K` multiplicity: six ordered role pairs times the `K` palette colors, with
equal coarse cells admitted. Under grouping the index becomes

    (ordered DISTINCT proxy pair) × palette

and the role factor disappears entirely — one representative per proxy serves every pattern
role, which is what removes G10 structurally. Distinctness is now required at PROXY level,
so **sibling pairs — two proxies of one owner — are events**, while a proxy paired with
itself is not.

## The size

`proxyPairEvents Q = Q.parts.offDiag` is the ordered distinct proxy pairs, of cardinality
`p² − p` for `p` proxies (`card_proxyPairEvents`). With `p = 3n` proxies from `n` owners
that is `3n(3n − 1)`, under the frozen **`9n²` envelope**
(`card_proxyPairEvents_le_of_triple`), and with palettes a factor `K`
(`card_proxyPaletteEvents_le`).

## Not done here

The selection summit itself is not rebuilt. `BinaryPaletteStrongDiagWitness.exists_representatives`
and its deviant-mass input remain role-indexed, and the generic weighted-choice machinery
(`Finite/WeightedChoice.lean`) is untouched by design — it is already indexed by an abstract
event type with two distinct coordinates, which is exactly what the new index supplies.
Rounding, cleaning, and `Recolor.lean` stay closed; profile homogenization remains the later
rounding obligation.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### The index -/

/-- **The proxy-pair event index**: ordered pairs of DISTINCT proxy cells. Sibling pairs —
two proxies of one owner — are included; a proxy against itself is not. -/
def proxyPairEvents (Q : Finpartition s) : Finset (Finset V × Finset V) :=
  Q.parts.offDiag

theorem mem_proxyPairEvents {Q : Finpartition s} {p : Finset V × Finset V} :
    p ∈ proxyPairEvents Q ↔ p.1 ∈ Q.parts ∧ p.2 ∈ Q.parts ∧ p.1 ≠ p.2 :=
  Finset.mem_offDiag

/-- **Sibling pairs are events, and they live in one owner.** Two distinct proxies carrying
the same owner label are an ordered distinct proxy pair — so the union bound must cover them
— while both sit inside that owner. This is the clause the coarse-level `C ≠ D` exclusion
does NOT provide. -/
theorem mem_proxyPairEvents_of_sibling {Q : Finpartition s} {g : Finset V → ℕ} {j : ℕ}
    {A B : Finset V} (hA : A ∈ Q.parts) (hB : B ∈ Q.parts) (hgA : g A = j) (hgB : g B = j)
    (hAB : A ≠ B) : (A, B) ∈ proxyPairEvents Q ∧
      A ⊆ groupUnion Q g j ∧ B ⊆ groupUnion Q g j :=
  ⟨mem_proxyPairEvents.mpr ⟨hA, hB, hAB⟩, subset_groupUnion hA hgA,
    subset_groupUnion hB hgB⟩

/-- A proxy is never paired with itself. -/
theorem notMem_proxyPairEvents_self {Q : Finpartition s} {A : Finset V} :
    (A, A) ∉ proxyPairEvents Q := by
  rw [mem_proxyPairEvents]
  rintro ⟨-, -, h⟩
  exact h rfl

/-! ### The size, derived before any tolerance -/

theorem card_proxyPairEvents (Q : Finpartition s) :
    (proxyPairEvents Q).card = Q.parts.card * Q.parts.card - Q.parts.card :=
  Finset.offDiag_card Q.parts

/-- **The `9n²` envelope.** With `3n` proxies from `n` owners the ordered distinct proxy
pairs number `3n(3n − 1)`, which sits under `9n²`. This is an envelope on the proxy count,
NOT a ninefold factor over the coarse `n(n − 1)`. -/
theorem card_proxyPairEvents_le_of_triple (Q : Finpartition s) {n : ℕ}
    (hn : Q.parts.card = 3 * n) : (proxyPairEvents Q).card ≤ 9 * (n * n) := by
  rw [card_proxyPairEvents, hn]
  cases n with
  | zero => simp
  | succ m => nlinarith [Nat.sub_le (3 * (m + 1) * (3 * (m + 1))) (3 * (m + 1))]

/-- With palette colors the index carries a factor `K`, and the whole event count is under
`9n²·K`. The tolerance is chosen against this, and only after it. -/
theorem card_proxyPaletteEvents_le {L : FirstOrder.Language} [FiniteRelational L]
    (Q : Finpartition s) {n : ℕ} (hn : Q.parts.card = 3 * n) :
    (proxyPairEvents Q ×ˢ (Finset.univ : Finset (BinaryPairPalette L))).card
      ≤ 9 * (n * n) * Fintype.card (BinaryPairPalette L) := by
  rw [Finset.card_product, Finset.card_univ]
  exact Nat.mul_le_mul_right _ (card_proxyPairEvents_le_of_triple Q hn)

/-! ### Tests -/

section Tests

-- With two proxies there are exactly two ordered distinct pairs, and neither is a self-pair.
example : (proxyPairEvents (twoPartition ({0, 1, 2, 3} : Finset (Fin 4)) {0, 1}
    (by decide) (by decide) (by decide))).card = 2 := by
  rw [card_proxyPairEvents, twoPartition_card]

-- The self-pair is excluded.
example (Q : Finpartition (Finset.univ : Finset (Fin 4))) (A : Finset (Fin 4)) :
    (A, A) ∉ proxyPairEvents Q := notMem_proxyPairEvents_self

-- The envelope at three owners: nine proxies, 72 ordered distinct pairs, under 81.
example (Q : Finpartition (Finset.univ : Finset (Fin 9))) (h : Q.parts.card = 3 * 3) :
    (proxyPairEvents Q).card ≤ 9 * (3 * 3) := card_proxyPairEvents_le_of_triple Q h

example : 3 * 3 * (3 * 3) - 3 * 3 = 72 := by decide

-- Sibling pairs really are in the index: two distinct proxies sharing an owner label.
example (Q : Finpartition (Finset.univ : Finset (Fin 4))) (A B : Finset (Fin 4))
    (hA : A ∈ Q.parts) (hB : B ∈ Q.parts) (hAB : A ≠ B) :
    (A, B) ∈ proxyPairEvents Q ∧ A ⊆ groupUnion Q (fun _ => 0) 0
      ∧ B ⊆ groupUnion Q (fun _ => 0) 0 :=
  mem_proxyPairEvents_of_sibling (g := fun _ => 0) (j := 0) hA hB rfl rfl hAB

end Tests

end RegularityLemmata
