/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Hypergraph.Colored

/-!
# Copy, induced-copy, and homomorphism counts

Counts of a pattern hypergraph `P` (on a finite vertex type `W`) inside a host `H`
(on `V`): `homCount` (edge-preserving maps — note that landing an `r`-edge on an
`r`-edge already forces injectivity on that edge), `copyCount` (injective
edge-preserving maps), and `inducedCopyCount` (injective maps under which `r`-sets are
edges exactly when their images are). For **total colored** hypergraphs the copy and
induced notions coincide, so `ColoredHypergraph.copyCount` asks the colors of all
`r`-sets to transport.

All counts are computable filters over the full function box, so small instances are
checked by `decide`. Extremal identities: every injective map is a copy into the
complete host (`copyCount_complete`, a falling factorial), and the empty pattern is
mapped by everything (`homCount_empty`, a full power) — the vacuous/degenerate
conventions exercised by the test battery.
-/

namespace RegularityLemmata

namespace UniformHypergraph

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {r : ℕ}

/-- Edge-preserving maps from the pattern to the host. -/
def homCount (P : UniformHypergraph r W) (H : UniformHypergraph r V) : ℕ :=
  (Finset.univ.filter fun f : W → V => ∀ e ∈ P.edges, e.image f ∈ H.edges).card

/-- Injective edge-preserving maps. -/
def copyCount (P : UniformHypergraph r W) (H : UniformHypergraph r V) : ℕ :=
  (Finset.univ.filter fun f : W → V =>
    Function.Injective f ∧ ∀ e ∈ P.edges, e.image f ∈ H.edges).card

/-- Injective maps under which `r`-sets are pattern edges exactly when their images
are host edges. -/
def inducedCopyCount (P : UniformHypergraph r W) (H : UniformHypergraph r V) : ℕ :=
  (Finset.univ.filter fun f : W → V => Function.Injective f ∧
    ∀ e ∈ Finset.univ.powersetCard r, (e ∈ P.edges ↔ e.image f ∈ H.edges)).card

theorem copyCount_le_homCount (P : UniformHypergraph r W) (H : UniformHypergraph r V) :
    copyCount P H ≤ homCount P H := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.2⟩

theorem inducedCopyCount_le_copyCount (P : UniformHypergraph r W)
    (H : UniformHypergraph r V) : inducedCopyCount P H ≤ copyCount P H := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨hf.1, hf.2.1, fun e he => ?_⟩
  exact (hf.2.2 e (P.edges_subset_powersetCard he)).mp he

/-- Every injective map is a copy into the complete host: the count is the falling
factorial `(|V|)_{|W|}`. -/
theorem copyCount_complete (P : UniformHypergraph r W) :
    copyCount P (complete r V) = (Fintype.card V).descFactorial (Fintype.card W) := by
  classical
  rw [copyCount]
  have hcongr : (Finset.univ.filter fun f : W → V =>
      Function.Injective f ∧ ∀ e ∈ P.edges, e.image f ∈ (complete r V).edges)
      = Finset.univ.filter fun f : W → V => Function.Injective f := by
    refine Finset.filter_congr fun f _ => ?_
    constructor
    · exact fun h => h.1
    · intro hinj
      refine ⟨hinj, fun e he => ?_⟩
      rw [complete, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_image_of_injective e hinj]
      exact P.card_eq e he
  rw [hcongr, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding W V),
    Fintype.card_embedding_eq]

/-- The empty pattern is mapped by every function: a full power. -/
theorem homCount_empty (H : UniformHypergraph r V) :
    homCount (empty r W) H = (Fintype.card V) ^ (Fintype.card W) := by
  rw [homCount]
  have hcongr : (Finset.univ.filter fun f : W → V =>
      ∀ e ∈ (empty r W).edges, e.image f ∈ H.edges) = Finset.univ := by
    refine Finset.filter_true_of_mem fun f _ e he => ?_
    exact absurd he (Finset.notMem_empty e)
  rw [hcongr, Finset.card_univ]
  simp

end UniformHypergraph

namespace ColoredHypergraph

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {r K : ℕ}

/-- Color-respecting injective copies. For total colorings this is simultaneously the
copy and the induced-copy notion: every `r`-set's color must transport. -/
def copyCount (P : ColoredHypergraph r K W) (H : ColoredHypergraph r K V) : ℕ :=
  (Finset.univ.filter fun f : W → V => Function.Injective f ∧
    ∀ e ∈ Finset.univ.powersetCard r, H.coloring (e.image f) = P.coloring e).card

/-- Colored copies of the uncolored reduct: forgetting colors can only gain copies. -/
theorem copyCount_le_card_injective (P : ColoredHypergraph r K W)
    (H : ColoredHypergraph r K V) :
    copyCount P H ≤ (Finset.univ.filter
      (Function.Injective : (W → V) → Prop)).card := by
  refine Finset.card_le_card fun f hf => ?_
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, hf.2.1⟩

end ColoredHypergraph

/-! ### Tests and adversarial examples -/

open UniformHypergraph ColoredHypergraph

-- The single-edge 2-pattern on Fin 2 has 6 copies in the complete 2-graph on Fin 3
-- (all injective maps), matching the falling factorial (3)_2 = 6.
example :
    copyCount (complete 2 (Fin 2)) (complete 2 (Fin 3)) = 6 := by decide

example :
    copyCount (complete 2 (Fin 2)) (complete 2 (Fin 3))
      = (Fintype.card (Fin 3)).descFactorial (Fintype.card (Fin 2)) :=
  copyCount_complete _

-- No copies into the empty host (the pattern has an edge; images have nowhere to go).
example : copyCount (complete 2 (Fin 2)) (empty 2 (Fin 3)) = 0 := by decide

-- The empty pattern is mapped by all 3² functions.
example : homCount (empty 2 (Fin 2)) (empty 2 (Fin 3)) = 9 := homCount_empty _

-- Induced vs plain copies differ: the single-edge pattern on a 3-vertex ground set
-- (edges {{0,1}}) has plain copies into the complete host, but NO induced copies
-- (the complete host would force the other pairs to be pattern edges too).
example :
    inducedCopyCount
      (⟨{{0, 1}}, by decide⟩ : UniformHypergraph 2 (Fin 3)) (complete 2 (Fin 3)) = 0 := by
  decide

example :
    0 < copyCount
      (⟨{{0, 1}}, by decide⟩ : UniformHypergraph 2 (Fin 3)) (complete 2 (Fin 3)) := by
  decide

-- Colored copies on a tiny instance: 2-colorings of pairs over Fin 2 → Fin 3 hosts.
example :
    ColoredHypergraph.copyCount
      (⟨fun _ => 0⟩ : ColoredHypergraph 2 2 (Fin 2))
      (⟨fun _ => 0⟩ : ColoredHypergraph 2 2 (Fin 3)) = 6 := by decide

example :
    ColoredHypergraph.copyCount
      (⟨fun _ => 0⟩ : ColoredHypergraph 2 2 (Fin 2))
      (⟨fun _ => 1⟩ : ColoredHypergraph 2 2 (Fin 3)) = 0 := by decide

end RegularityLemmata
