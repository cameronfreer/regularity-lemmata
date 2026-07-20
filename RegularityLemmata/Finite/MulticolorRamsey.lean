/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic

/-!
# Route (b) step 1 substrate: finite multicolor Ramsey by greedy pigeonhole

`ARCHITECTURE.md` route (b) ladder, step 1 (design freeze 2026-07-20): mathlib has no
finite Ramsey machinery, so the self-regular-subset lemma's extraction — a
subcollection of pieces whose pairwise discretized density vectors all lie in one
class — needs a self-contained bound. This file proves it with the classical greedy
argument, ordered-pair form:

* `exists_forward_monochromatic_chain` — from `(r+1)^t` vertices, a chain
  `v : Fin t → V` where each `v i` sees a SINGLE recorded color `c i` toward every
  later chain vertex. Each greedy step spends one vertex and keeps the largest of
  the `r` color classes (pigeonhole), shrinking `(r+1)^(t+1)` to at least `(r+1)^t`.
* `exists_monochromatic_subchain` — the summit: from `multicolorRamseyBound r s =
  (r+1)^(r·s+1)` vertices, `s` vertices in chain order with ALL forward colors equal
  to one `c` (pigeonhole on the recorded colors of a chain of length `r·s + 1`).

The coloring is a function on ORDERED pairs and no symmetry is assumed: the
conclusion controls `χ (v i) (v j)` for `i < j` only. The intended instantiation
colors an ordered pair of pieces by the discretized pair of BOTH directed palette
density vectors, so forward-monochromaticity already pins both directions of every
extracted pair. The bound is deliberately generous (single-exponential in `r·s`);
only its finiteness enters the route (b) constants.
-/

namespace RegularityLemmata

variable {V : Type*} [DecidableEq V] {r : ℕ}

open Finset

/-- **The greedy chain.** From `(r+1)^t` vertices, a length-`t` injective chain in
which every vertex sees one recorded color toward all later chain vertices. -/
theorem exists_forward_monochromatic_chain (χ : V → V → Fin r) :
    ∀ (t : ℕ) (S : Finset V), (r + 1) ^ t ≤ S.card →
    ∃ (v : Fin t → V) (c : Fin t → Fin r),
      (∀ i, v i ∈ S) ∧ Function.Injective v ∧
      ∀ i j : Fin t, i < j → χ (v i) (v j) = c i := by
  intro t
  induction t with
  | zero =>
    intro S _
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ t ih =>
    intro S hS
    have hpos : 0 < S.card :=
      lt_of_lt_of_le (Nat.one_le_pow _ _ (Nat.succ_pos r)) hS
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      exact (χ x x).elim0
    -- The largest color class of `χ x ·` on `S.erase x` still has `(r+1)^t` vertices.
    have hclass : (univ : Finset (Fin r)).card * (r + 1) ^ t ≤ (S.erase x).card := by
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem hx]
      have h2 : r * (r + 1) ^ t + 1 ≤ (r + 1) ^ (t + 1) := by
        have h3 := Nat.one_le_pow t (r + 1) (Nat.succ_pos r)
        have h5 : (r + 1) ^ (t + 1) = r * (r + 1) ^ t + (r + 1) ^ t := by ring
        omega
      have h4 : r * (r + 1) ^ t + 1 ≤ S.card := le_trans h2 hS
      omega
    obtain ⟨c₀, -, hc₀⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (f := χ x) (fun a _ => mem_univ _)
        (univ_nonempty_iff.mpr ⟨⟨0, hrpos⟩⟩) hclass
    obtain ⟨v', c', hv'mem, hv'inj, hv'chain⟩ :=
      ih ((S.erase x).filter (fun y => χ x y = c₀)) hc₀
    -- Prepend `x` with recorded color `c₀`.
    refine ⟨Fin.cons x v', Fin.cons c₀ c', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using hx
      · rw [Fin.cons_succ]
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hv'mem i'))
    · intro a b hab
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · rfl
      · rw [Fin.cons_zero, Fin.cons_succ] at hab
        exact absurd hab.symm (Finset.ne_of_mem_erase
          (Finset.mem_of_mem_filter _ (hv'mem b')))
      · rw [Fin.cons_succ, Fin.cons_zero] at hab
        exact absurd hab (Finset.ne_of_mem_erase
          (Finset.mem_of_mem_filter _ (hv'mem a')))
      · rw [Fin.cons_succ, Fin.cons_succ] at hab
        rw [hv'inj hab]
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact absurd hij (lt_irrefl _)
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact (Finset.mem_filter.mp (hv'mem j')).2
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact absurd hij (Fin.not_lt_zero _)
        · simp only [Fin.cons_succ]
          exact hv'chain i' j' (Fin.succ_lt_succ_iff.mp hij)

/-- The single-exponential multicolor Ramsey bound of this substrate: a vertex set of
this size guarantees `s` vertices in chain order with one common forward color. Only
finiteness of the bound enters the route (b) constants. -/
def multicolorRamseyBound (r s : ℕ) : ℕ := (r + 1) ^ (r * s + 1)

/-- **The extraction summit.** From `multicolorRamseyBound r s` vertices, `s`
vertices in chain order whose forward colors all equal one `c`. -/
theorem exists_monochromatic_subchain (χ : V → V → Fin r) {s : ℕ} (S : Finset V)
    (hS : multicolorRamseyBound r s ≤ S.card) :
    ∃ (v : Fin s → V) (c : Fin r), (∀ i, v i ∈ S) ∧ Function.Injective v ∧
      ∀ i j : Fin s, i < j → χ (v i) (v j) = c := by
  classical
  obtain ⟨w, cw, hwS, hwinj, hwchain⟩ :=
    exists_forward_monochromatic_chain χ (r * s + 1) S hS
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    exact (χ (w ⟨0, Nat.succ_pos _⟩) (w ⟨0, Nat.succ_pos _⟩)).elim0
  -- Pigeonhole on the recorded colors: some color repeats at least `s` times.
  have hcnt : (univ : Finset (Fin r)).card * s
      < (univ : Finset (Fin (r * s + 1))).card := by
    rw [Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨c₀, -, hc₀⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := cw) (fun a _ => mem_univ _) hcnt
  set T := (univ : Finset (Fin (r * s + 1))).filter (fun a => cw a = c₀) with hT
  have hTcard : s ≤ T.card := le_of_lt hc₀
  -- Enumerate the fiber in increasing order and take its first `s` indices.
  refine ⟨fun i => w ((T.orderIsoOfFin rfl ⟨i.1, lt_of_lt_of_le i.2 hTcard⟩ : T) : _),
    c₀, fun i => hwS _, ?_, ?_⟩
  · intro a b hab
    have h1 := hwinj hab
    have h2 := (T.orderIsoOfFin rfl).injective (Subtype.ext h1)
    have h3 := congrArg Fin.val h2
    exact Fin.ext h3
  · intro i j hij
    have hmono : (T.orderIsoOfFin rfl ⟨i.1, lt_of_lt_of_le i.2 hTcard⟩ : T)
        < T.orderIsoOfFin rfl ⟨j.1, lt_of_lt_of_le j.2 hTcard⟩ :=
      (T.orderIsoOfFin rfl).strictMono (by exact_mod_cast hij)
    have hfib : cw ((T.orderIsoOfFin rfl ⟨i.1, lt_of_lt_of_le i.2 hTcard⟩ : T) : _)
        = c₀ :=
      (Finset.mem_filter.mp
        (T.orderIsoOfFin rfl ⟨i.1, lt_of_lt_of_le i.2 hTcard⟩).2).2
    rw [← hfib]
    exact hwchain _ _ hmono

/-! ### Tests -/

section Tests

-- The bound, concretely: one color, target `1` → `2² = 4`; two colors, target `2`
-- → `3⁵ = 243`.
example : multicolorRamseyBound 1 1 = 4 := by decide

example : multicolorRamseyBound 2 2 = 243 := by decide

-- One color: the summit specializes to plain extraction — any coloring into `Fin 1`
-- is globally monochromatic, and the guarantee is nonvacuous once `|S| ≥ 4`.
example (χ : ℕ → ℕ → Fin 1) (S : Finset ℕ) (hS : 4 ≤ S.card) :
    ∃ (v : Fin 1 → ℕ) (c : Fin 1), (∀ i, v i ∈ S) ∧ Function.Injective v ∧
      ∀ i j : Fin 1, i < j → χ (v i) (v j) = c :=
  exists_monochromatic_subchain χ S (by simpa [multicolorRamseyBound] using hS)

end Tests

end RegularityLemmata
