# Retaining completion: specification of completing a family of exact-size blocks to a partition

**Status: specification for review. No theorem signature is frozen until this document is
approved; no Lean implementation accompanies it.** Companion to issue #183 (audit 5c, item ii).
The supply-constrained completion (audit 5c, item i) is **not** specified here and stays open.
Everything below uses this repository's definitions and the audit findings; open choices are
presented as choices.

## 0. Setting and existing declarations (unchanged)

- The enlarging completions `exists_equipartition_absorb_leftover` and
  `exists_equipartition_absorb_chunks` (`Partition/AbsorbLeftover.lean`): pairwise disjoint
  blocks of exact size `s` covering `S ⊆ univ` become an equipartition of `univ` with the
  **same** part count, each part containing one block; sizes `{s, s+1}` (under
  `|univ \ S| ≤ #blocks`) or `{s+q, s+q+1}`. The blocks are grown. Unchanged by this document.
- The slicing certificate `SliceCert A F m s t` (`Partition/PrefixBlockSampling.lean`):
  `block : Fin m → Finset α`, `block_card : ∀ j, |block j| = s`, `block_subset`,
  `block_disjoint`, `trace_upper`; `covered := univ.biUnion block`, `leftover := A \ covered`,
  `card_covered : |covered| = m·s`, `card_leftover : |leftover| = |A| − m·s`, and at the
  maximal count `m = |A| / s`: `card_leftover_eq_mod : |leftover| = |A| % s`,
  `card_leftover_lt : |leftover| < s`.
- `exists_balanced_slicing`, `exists_balanced_slicing_of_threshold(_self)`: certificates at the
  maximal count with parent-density control on every block.
- Mathlib: `Finpartition.IsEquipartition` (all part sizes within one of each other),
  `Finpartition.exists_equipartition_card_eq s hn hs` (an equipartition of `s` into `n ≠ 0`
  parts for `n ≤ |s|`), and the constructors for a partition from pairwise disjoint nonempty
  parts covering a set (`Finpartition.ofErase`, or `Finpartition.mk` with the disjointness and
  cover fields).

## 1. What "retaining" means, and the two readings of "balanced"

**Input.** A finite set `A`, a family `B : Fin m → Finset α` of pairwise disjoint blocks with
`B j ⊆ A` and `|B j| = s > 0` (the `SliceCert` fields, or any such family), and the remainder
`R := A \ ⋃_j B j`, so `|R| = |A| − m·s`. For arbitrary blocks this is the only leftover identity;
`|R| = |A| % s` holds **only** at the maximal count `m = |A| / s` (`card_leftover_eq_mod`), and
the specification does not assume it.

**Retaining.** The output is a `Finpartition A` whose parts include every `B j` **verbatim** (as
members of `parts`, not merely as subsets of parts) together with a partition of `R`. Nothing is
enlarged. This is the distinction from `AbsorbLeftover`, where the conclusion is `∃ b ∈ blocks, b ⊆ p`.

**Balanced.** Two readings; they differ in feasibility and must not be conflated.

- **(I) Balanced remainder.** The remainder is partitioned into `p'` parts whose sizes are within
  one of each other (an equipartition of `R`); the blocks are retained at size `s`. Feasible
  for every `1 ≤ p' ≤ |R|`, and for `R = ∅` with `p' = 0`. The whole partition is in general
  **not** an equipartition.
- **(II) Balanced whole.** The whole partition is an equipartition of `A` with the blocks
  retained. When there is at least one block (`m > 0`), the blocks have size `s`, so every
  part must have size in `{s−1, s}` or in `{s, s+1}`, and the remainder must split into parts
  of those sizes. When `m = 0` there is no size-`s` part and the condition is simply that the
  remainder partition is itself an equipartition. **No numerical threshold characterizes
  feasibility**: `|R| ≥ s − 1` or `|R| ≥ s` is not sufficient. Counterexample: one block of
  size `5` and a remainder of size `7`; `7` is not a sum of parts in `{4, 5}` nor in `{5, 6}`,
  so no retaining completion of this input is an equipartition, although `7 ≥ 5`. Also
  infeasible: one block of size `3` in a four-element carrier, whose remainder is a singleton
  (`{3, 1}` is not equitable). At the maximal count `|R| = |A| % s < s`, reading (II) is
  feasible only for `|R| = 0` (`s ∣ |A|`) or `|R| = s − 1` (a single remainder part); in
  general the numerical existence question (which `|R|` are sums of parts from `{s−1, s}` or
  `{s, s+1}`) is **deferred** and not stated as a theorem here.

**Scope, by ruling:** the theorem is reading (I) with a free feasible remainder-part count; the
balanced-whole reading is kept only as a characterization lemma with its correct hypotheses
(the `m > 0` and `m = 0` clauses), and its numerical existence characterization is deferred
rather than replaced by a threshold shortcut.

## 2. Proposed statements

**Input shape, by ruling.** The construction takes an **abstract indexed block family**
`B : Fin m → Finset α` with `∀ j, B j ⊆ A`, `∀ j, |B j| = s`, pairwise disjointness for `i ≠ j`,
and `0 < s`; the `SliceCert` adapter (feeding `cert.block` with `cert.block_subset`,
`cert.block_card`, `cert.block_disjoint`) is derived from it, so the slicing theorems compose
without a second construction.

**Construction.** Given the blocks and any partition `P_R : Finpartition R`, the retained
partition `retain B P_R : Finpartition A` has `parts = (univ.image B) ∪ P_R.parts` (disjoint
union of the block family and the remainder's parts; both families consist of nonempty
pairwise disjoint sets, the blocks are nonempty because `s > 0`, and the union covers `A`).

Laws:
- `mem_retain_block : ∀ j, B j ∈ (retain B P_R).parts` (retained verbatim);
- `mem_retain_iff : p ∈ (retain B P_R).parts ↔ (∃ j, p = B j) ∨ p ∈ P_R.parts`;
- `card_parts_retain : #(retain B P_R).parts = m + #P_R.parts` (the blocks are distinct as sets,
  being disjoint and nonempty);
- `retain_le_of_le`: refinement relations inherited from `P_R` (optional).

**Reading (I), existence.** For `0 < s`, blocks as above, and `p'` with `p' ≤ |R|` and
(`p' ≠ 0` or `R = ∅`): there is `P_R` an equipartition of `R` with `#P_R.parts = p'`
(Mathlib's `exists_equipartition_card_eq` on `R`), hence a `Finpartition A` retaining every
block with `m + p'` parts, remainder part sizes in `{|R| / p', |R| / p' + 1}`, and no part of
the remainder larger than `|R| / p' + 1`. Corollary at the maximal count with `p' = 1` (when
`R ≠ ∅`): one remainder part of size `|A| % s < s`.

**Reading (II), characterization (with its correct hypotheses).** For the retained partition
with remainder parts `P_R`:
- if `m > 0`: `(retain B P_R).IsEquipartition ↔ (∀ p ∈ P_R.parts, |p| ∈ {s−1, s}) ∨ (∀ p ∈ P_R.parts, |p| ∈ {s, s+1})`
  (the empty remainder satisfies both sides);
- if `m = 0`: `(retain B P_R).IsEquipartition ↔ P_R.IsEquipartition` (there is no size-`s` part).

No existence lemma for such a `P_R` is proposed; the numerical characterization of the
representable remainder sizes is deferred (§1).

**Density transport.** Composing with `exists_balanced_slicing` (or the threshold wrapper): the
retained blocks are the certificate's blocks as sets, so every density guarantee
`|(T ∩ B j)/s − (A ∩ T)/|A|| ≤ β` holds verbatim on the retained parts that are blocks; the
remainder's parts carry **no** density guarantee, and the specification does not claim one.

## 3. Endpoints and preserved API

- `R = ∅` (`s ∣ |A|` at the maximal count): `P_R` is the empty partition; the retained
  partition is the block family itself, which is an equipartition (all parts of size `s`);
  readings (I) and (II) coincide.
- `m = 0` (no blocks): the retained partition is `P_R` itself; reading (I) is Mathlib's
  equipartition existence; reading (II) is vacuous about `s`.
- `0 < |R| < s−1` at the maximal count: reading (I) gives one part of size `|R|` (or `p'`
  parts); reading (II) is infeasible, and the enlarging completion `exists_equipartition_absorb_leftover`
  is the alternative when an equipartition is required (at the cost of growing the blocks).
- `AbsorbLeftover`, `SliceCert`, and every slicing theorem are preserved unchanged.

## 4. Proposed compiled consumers and tests

1. **The review's first example** (`α = Fin 4`, one block `{0,1,2}`, `s = 3`): reading (I)
   with `p' = 1` gives the partition `{{0,1,2}, {3}}`, the block retained, `2` parts; the
   characterization shows it is **not** an equipartition (`|{3}| = 1 ∉ {2, 3}`), by `decide`.
1b. **The size-5, remainder-7 counterexample** (`α = Fin 12`, one block `{0,…,4}`, `s = 5`,
   remainder of size `7`): for **every** partition `P_R` of the remainder, the retained
   partition is not an equipartition. Proof route: by the characterization the remainder parts
   would all have sizes in `{4, 5}` or all in `{5, 6}`, and their sizes sum to `7`, which is
   impossible in either set (a small arithmetic lemma, `omega` after summing). This pins that no
   threshold on `|R|` can replace the deferred existence question.
1c. **The zero-block case** (`m = 0`, `A = R`): `retain B P_R = P_R` up to `parts`, and the
   retained partition is an equipartition iff `P_R` is; with `P_R` from Mathlib's
   `exists_equipartition_card_eq`, it is.
2. **A feasible balanced whole** (`α = Fin 6`, blocks `{0,1}, {2,3}`, `s = 2`, remainder
   `{4,5}` as one part): the retained partition `{{0,1},{2,3},{4,5}}` is an equipartition, by
   `decide`.
3. **Density transport**: statement-level, from `exists_balanced_slicing_of_threshold_self`,
   obtain the certificate, retain its blocks with `p' = 1` on the leftover (when nonempty), and
   read off the parent-density guarantee on every retained block from the certificate's
   conclusion, the leftover part being the only part without one.
4. **`R = ∅`**: `α = Fin 4`, blocks `{0,1}, {2,3}`: the retained partition equals the block
   family and is an equipartition.

## 5. Choices, as ruled, and what stays open

1. The theorem is reading (I), balanced remainder, with a free feasible remainder-part count
   `p'`; reading (II) is a characterization lemma only, with the `m > 0` / `m = 0` clauses, and
   its numerical existence characterization is deferred.
2. The input is an abstract indexed block family `B : Fin m → Finset α`; the `SliceCert`
   adapter is derived.
3. Still open for the next specification review: the exact form of the characterization's
   statement (two disjuncts on sizes, or the single condition "all remainder parts within one
   of `s`" phrased with `Nat` subtraction), and whether the construction should also be offered
   for a `Finset (Finset α)` family to match `AbsorbLeftover`'s interface.

This document needs another specification review before any signature is frozen.

The per-type supply completion of #183 (item i) is not touched by any of this; its condition
remains unwritten and it stays open.
