/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.Inequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card

/-!
# The finite multiplicative-weights (Hedge) forecaster and its regret bound

Self-contained real analysis over `Finset` sums — no measure theory and no probability library —
in the library's raw-weight idiom: `hedgeWeight` is an honest definition, `hedgeProb` its
normalization as a raw function with nonnegativity and sum-one *theorems* (no bundled
probability type), and the forecaster is online by construction, which the causal-congruence
lemmas state directly.

**Primitive: an arbitrary finite expert type `ι`.** Normalization needs `[Nonempty ι]`; the
`Fin m` specializations carry `[NeZero m]` instead and read `log m`. The empty-expert endpoint is
stated explicitly: with no experts the potential is `0`, `hedgeProb` is identically `0` under the
guard-free `x / 0 = 0` convention, and nothing sums to one.

**The bound.** For losses in `[0, 1]` and **any** `η > 0`, against every fixed expert `i₀`,

`∑_{t<T} ⟨p_t, ℓ_t⟩ ≤ ∑_{t<T} ℓ t i₀ + log |ι| / η + η T / 2`.

The proof is the potential argument on `Φ t = ∑ i, hedgeWeight η ℓ t i`. The update and
potential identities (`hedgeWeight_succ`, `hedgePotential_succ`) are algebraic; the single
analytic ingredient is `exp (−x) ≤ 1 − x + x²/2` (`exp_neg_le_one_sub_add_sq_half`,
`Finite/Inequalities.lean`), which gives the per-round estimate
`Φ (t+1) ≤ Φ t · (1 − η⟨p_t, ℓ_t⟩ + η²/2)`. **To keep `η` unconstrained**, the logarithm of that
factor is relaxed to the increment `−η⟨p_t, ℓ_t⟩ + η²/2` via `log (1 + y) ≤ y` and *that*
increment is telescoped; dividing a `(η − η²/2)`-form through instead would impose `η < 2` on
the public statement.

Antecedents: N. Littlestone and M. K. Warmuth, *The weighted majority algorithm*, Inf. Comput.
108 (1994); Y. Freund and R. E. Schapire, *A decision-theoretic generalization of on-line
learning and an application to boosting*, J. Comput. Syst. Sci. 55 (1997) — the Hedge form.

**Exposure.** Root import only. A one-module `Online/` facade would be premature; revisit when a
second online-learning module exists.
-/

namespace RegularityLemmata

open Finset

variable {ι κ : Type*} [Fintype ι]

/-! ### Weights, potential, probabilities -/

/-- The exponential weight of expert `i` after `t` rounds: `exp (−η ∑_{s<t} ℓ s i)`. -/
noncomputable def hedgeWeight (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  Real.exp (-η * ∑ s ∈ range t, ℓ s i)

/-- The potential: the total weight after `t` rounds. -/
noncomputable def hedgePotential (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, hedgeWeight η ℓ t i

/-- The distribution played at round `t`: the normalized weights (raw function; guard-free
`x / 0 = 0`, so identically `0` with no experts). -/
noncomputable def hedgeProb (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  hedgeWeight η ℓ t i / hedgePotential η ℓ t

/-- The forecaster's expected loss at round `t`: `⟨p_t, ℓ_t⟩`. -/
noncomputable def hedgeExpectedLoss (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, hedgeProb η ℓ t i * ℓ t i

variable {η : ℝ} {ℓ ℓ' : ℕ → ι → ℝ} {t : ℕ} {i : ι}

omit [Fintype ι] in
/-- The closed form, definitionally. -/
theorem hedgeWeight_eq_exp : hedgeWeight η ℓ t i = Real.exp (-η * ∑ s ∈ range t, ℓ s i) := rfl

omit [Fintype ι] in
@[simp] theorem hedgeWeight_zero : hedgeWeight η ℓ 0 i = 1 := by
  simp [hedgeWeight]

omit [Fintype ι] in
/-- **The multiplicative update.** -/
theorem hedgeWeight_succ :
    hedgeWeight η ℓ (t + 1) i = hedgeWeight η ℓ t i * Real.exp (-η * ℓ t i) := by
  rw [hedgeWeight, hedgeWeight, sum_range_succ, ← Real.exp_add]
  congr 1
  ring

omit [Fintype ι] in
theorem hedgeWeight_pos : 0 < hedgeWeight η ℓ t i := Real.exp_pos _

theorem hedgePotential_nonneg : 0 ≤ hedgePotential η ℓ t :=
  sum_nonneg fun _ _ => hedgeWeight_pos.le

/-- With at least one expert the potential is positive. -/
theorem hedgePotential_pos [Nonempty ι] : 0 < hedgePotential η ℓ t :=
  sum_pos (fun _ _ => hedgeWeight_pos) univ_nonempty

@[simp] theorem hedgePotential_zero : hedgePotential η ℓ 0 = Fintype.card ι := by
  simp [hedgePotential]

/-- **The potential is the weight of every expert's own cumulative loss**: each weight is at
most the total. -/
theorem hedgeWeight_le_hedgePotential : hedgeWeight η ℓ t i ≤ hedgePotential η ℓ t :=
  single_le_sum (f := fun j => hedgeWeight η ℓ t j) (fun _ _ => hedgeWeight_pos.le) (mem_univ i)

theorem hedgeProb_nonneg : 0 ≤ hedgeProb η ℓ t i :=
  div_nonneg hedgeWeight_pos.le hedgePotential_nonneg

/-- It really is a distribution — given an expert. -/
theorem hedgeProb_sum_one [Nonempty ι] : ∑ i, hedgeProb η ℓ t i = 1 := by
  simp only [hedgeProb, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hedgePotential_pos.ne'

theorem hedgeProb_le_one : hedgeProb η ℓ t i ≤ 1 := by
  rw [hedgeProb]
  rcases eq_or_ne (hedgePotential η ℓ t) 0 with h0 | h0
  · rw [h0, div_zero]; exact zero_le_one
  · exact (div_le_one (lt_of_le_of_ne hedgePotential_nonneg h0.symm)).mpr
      hedgeWeight_le_hedgePotential

/-- Uniform at round `0`. -/
theorem hedgeProb_zero : hedgeProb η ℓ 0 i = 1 / Fintype.card ι := by
  simp [hedgeProb]

/-! ### The empty-expert endpoint -/

section Empty

variable [IsEmpty ι]

/-- With no experts the potential is `0`. -/
theorem hedgePotential_of_isEmpty : hedgePotential η ℓ t = 0 := by
  simp [hedgePotential]

/-- With no experts nothing sums to one: the probabilities sum to `0`. -/
theorem sum_hedgeProb_of_isEmpty : ∑ i, hedgeProb η ℓ t i = 0 := by
  simp

theorem hedgeExpectedLoss_of_isEmpty : hedgeExpectedLoss η ℓ t = 0 := by
  simp [hedgeExpectedLoss]

end Empty

/-! ### Causal congruence: round `t` reads only rounds `< t` -/

omit [Fintype ι] in
theorem hedgeWeight_congr (h : ∀ s < t, ℓ s = ℓ' s) : hedgeWeight η ℓ t = hedgeWeight η ℓ' t := by
  funext i
  rw [hedgeWeight, hedgeWeight]
  congr 2
  exact sum_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]

theorem hedgePotential_congr (h : ∀ s < t, ℓ s = ℓ' s) :
    hedgePotential η ℓ t = hedgePotential η ℓ' t := by
  rw [hedgePotential, hedgePotential, hedgeWeight_congr h]

theorem hedgeProb_congr (h : ∀ s < t, ℓ s = ℓ' s) : hedgeProb η ℓ t = hedgeProb η ℓ' t := by
  funext i
  rw [hedgeProb, hedgeProb, hedgeWeight_congr h, hedgePotential_congr h]

/-! ### Relabeling by an equivalence of expert types -/

section Relabel

variable [Fintype κ] (e : κ ≃ ι)

omit [Fintype ι] [Fintype κ] in
/-- Weights transport along a relabeling of the experts, pointwise. -/
theorem hedgeWeight_comp_equiv :
    hedgeWeight η (fun s j => ℓ s (e j)) t = fun j => hedgeWeight η ℓ t (e j) := rfl

/-- The potential is invariant under relabeling. -/
theorem hedgePotential_comp_equiv :
    hedgePotential η (fun s j => ℓ s (e j)) t = hedgePotential η ℓ t := by
  rw [hedgePotential, hedgePotential, hedgeWeight_comp_equiv]
  exact e.sum_comp fun i => hedgeWeight η ℓ t i

/-- Probabilities transport along a relabeling, pointwise. -/
theorem hedgeProb_comp_equiv :
    hedgeProb η (fun s j => ℓ s (e j)) t = fun j => hedgeProb η ℓ t (e j) := by
  funext j
  rw [hedgeProb, hedgeProb, hedgeWeight_comp_equiv, hedgePotential_comp_equiv]

/-- The expected loss is invariant under relabeling. -/
theorem hedgeExpectedLoss_comp_equiv :
    hedgeExpectedLoss η (fun s j => ℓ s (e j)) t = hedgeExpectedLoss η ℓ t := by
  rw [hedgeExpectedLoss, hedgeExpectedLoss, hedgeProb_comp_equiv]
  exact e.sum_comp fun i => hedgeProb η ℓ t i * ℓ t i

end Relabel

/-! ### The potential estimate -/

/-- **The potential update, algebraic**: the next potential is the current one times the
forecaster's expected value of `exp (−η ℓ_t)`. Needs an expert, to divide by the potential. -/
theorem hedgePotential_succ [Nonempty ι] :
    hedgePotential η ℓ (t + 1)
      = hedgePotential η ℓ t * ∑ i, hedgeProb η ℓ t i * Real.exp (-η * ℓ t i) := by
  rw [hedgePotential, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hedgeWeight_succ, hedgeProb]
  field_simp
  rw [mul_div_cancel_right₀ _ hedgePotential_pos.ne']

/-- **The per-round estimate**, the single analytic step: for `η ≥ 0` and losses in `[0, 1]`,
`Φ (t+1) ≤ Φ t · (1 − η⟨p_t, ℓ_t⟩ + η²/2)`, from `exp (−x) ≤ 1 − x + x²/2` at `x = η ℓ_t i`
and `ℓ_t i² ≤ 1`. -/
theorem hedgePotential_succ_le [Nonempty ι] (hη : 0 ≤ η)
    (hℓ : ∀ i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1) :
    hedgePotential η ℓ (t + 1)
      ≤ hedgePotential η ℓ t * (1 - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2) := by
  rw [hedgePotential_succ]
  refine mul_le_mul_of_nonneg_left ?_ hedgePotential_nonneg
  have hpt : ∀ i, Real.exp (-η * ℓ t i) ≤ 1 - η * ℓ t i + η ^ 2 / 2 := by
    intro i
    obtain ⟨h0, h1⟩ := hℓ i
    have hx : 0 ≤ η * ℓ t i := mul_nonneg hη h0
    rw [neg_mul]
    refine (exp_neg_le_one_sub_add_sq_half hx).trans ?_
    have hsq : (η * ℓ t i) ^ 2 ≤ η ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg η) (pow_le_one₀ h0 h1)
    linarith
  calc ∑ i, hedgeProb η ℓ t i * Real.exp (-η * ℓ t i)
      ≤ ∑ i, hedgeProb η ℓ t i * (1 - η * ℓ t i + η ^ 2 / 2) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) hedgeProb_nonneg
    _ = (∑ i, hedgeProb η ℓ t i) - η * ∑ i, hedgeProb η ℓ t i * ℓ t i
          + η ^ 2 / 2 * ∑ i, hedgeProb η ℓ t i := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ = 1 - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2 := by
        rw [hedgeProb_sum_one, hedgeExpectedLoss]
        ring

/-- **The relaxed logarithmic increment.** `log Φ (t+1) ≤ log Φ t − η⟨p_t, ℓ_t⟩ + η²/2`: the
factor `1 − η⟨p,ℓ⟩ + η²/2` is positive for every `η ≥ 0` (it is at least `(1 − η)²/2 + 1/2`,
since `⟨p, ℓ⟩ ≤ 1`), and `log (1 + y) ≤ y`. This is the step that keeps `η` unconstrained. -/
theorem log_hedgePotential_succ_le [Nonempty ι] (hη : 0 ≤ η)
    (hℓ : ∀ i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1) :
    Real.log (hedgePotential η ℓ (t + 1))
      ≤ Real.log (hedgePotential η ℓ t) - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2 := by
  have hL0 : 0 ≤ hedgeExpectedLoss η ℓ t :=
    sum_nonneg fun i _ => mul_nonneg hedgeProb_nonneg (hℓ i).1
  have hL1 : hedgeExpectedLoss η ℓ t ≤ 1 := by
    calc hedgeExpectedLoss η ℓ t ≤ ∑ i, hedgeProb η ℓ t i * 1 :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hℓ i).2 hedgeProb_nonneg
      _ = 1 := by simp [hedgeProb_sum_one]
  have hfac : 0 < 1 - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2 := by
    nlinarith [sq_nonneg (1 - η), mul_le_mul_of_nonneg_left hL1 hη]
  calc Real.log (hedgePotential η ℓ (t + 1))
      ≤ Real.log (hedgePotential η ℓ t * (1 - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2)) :=
        Real.log_le_log hedgePotential_pos (hedgePotential_succ_le hη hℓ)
    _ = Real.log (hedgePotential η ℓ t) + Real.log (1 - η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2) :=
        Real.log_mul hedgePotential_pos.ne' hfac.ne'
    _ ≤ Real.log (hedgePotential η ℓ t) + (-η * hedgeExpectedLoss η ℓ t + η ^ 2 / 2) := by
        have := Real.log_le_sub_one_of_pos hfac
        linarith
    _ = _ := by ring

/-! ### The regret bound -/

/-- **Telescoped**: `log Φ T ≤ log |ι| − η ∑_{t<T} ⟨p_t, ℓ_t⟩ + η² T / 2`. -/
theorem log_hedgePotential_le [Nonempty ι] (hη : 0 ≤ η) {T : ℕ}
    (hℓ : ∀ t < T, ∀ i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1) :
    Real.log (hedgePotential η ℓ T)
      ≤ Real.log (Fintype.card ι) - η * ∑ t ∈ range T, hedgeExpectedLoss η ℓ t
        + η ^ 2 * T / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have := log_hedgePotential_succ_le (η := η) (ℓ := ℓ) (t := T) hη (hℓ T (Nat.lt_succ_self T))
    have ih' := ih fun t ht => hℓ t (ht.trans (Nat.lt_succ_self T))
    rw [sum_range_succ]
    push_cast
    linarith

/-- **The Hedge regret bound.** For losses in `[0, 1]` over the horizon `t < T` and any
`η > 0`, against every fixed expert `i₀`:

`∑_{t<T} ⟨p_t, ℓ_t⟩ ≤ ∑_{t<T} ℓ t i₀ + log |ι| / η + η T / 2`,

with no upper hypothesis on `η` and no hypothesis on rounds `≥ T`. From the telescoped
potential bound and `Φ T ≥ hedgeWeight η ℓ T i₀ = exp (−η ∑_{t<T} ℓ t i₀)`. The expert `i₀`
itself witnesses `Nonempty ι`, so no instance is assumed. -/
theorem hedge_regret (hη : 0 < η) {T : ℕ} (hℓ : ∀ t < T, ∀ i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1)
    (i₀ : ι) :
    ∑ t ∈ range T, hedgeExpectedLoss η ℓ t
      ≤ ∑ t ∈ range T, ℓ t i₀ + Real.log (Fintype.card ι) / η + η * T / 2 := by
  have : Nonempty ι := ⟨i₀⟩
  have hup := log_hedgePotential_le hη.le hℓ
  have hlow : -η * ∑ t ∈ range T, ℓ t i₀ ≤ Real.log (hedgePotential η ℓ T) := by
    rw [← Real.log_exp (-η * ∑ t ∈ range T, ℓ t i₀)]
    exact Real.log_le_log (Real.exp_pos _) hedgeWeight_le_hedgePotential
  have hkey : η * ∑ t ∈ range T, hedgeExpectedLoss η ℓ t
      ≤ η * ∑ t ∈ range T, ℓ t i₀ + Real.log (Fintype.card ι) + η ^ 2 * T / 2 := by
    linarith
  have := div_le_div_of_nonneg_right hkey hη.le
  rw [mul_div_cancel_left₀ _ hη.ne'] at this
  refine this.trans (le_of_eq ?_)
  field_simp

/-! ### `Fin m` specializations -/

section Fin

variable {m : ℕ} {ℓm : ℕ → Fin m → ℝ}

/-- The potential over `m` experts is positive when `m ≠ 0`. -/
theorem sum_hedgeWeight_pos [NeZero m] : 0 < ∑ i, hedgeWeight η ℓm t i :=
  hedgePotential_pos

theorem hedgeProb_sum_one_fin [NeZero m] : ∑ i, hedgeProb η ℓm t i = 1 :=
  hedgeProb_sum_one

/-- The regret bound over `m` experts, reading `log m`; `i₀ : Fin m` already forces `m ≠ 0`. -/
theorem hedge_regret_fin (hη : 0 < η) {T : ℕ} (hℓ : ∀ t < T, ∀ i, 0 ≤ ℓm t i ∧ ℓm t i ≤ 1)
    (i₀ : Fin m) :
    ∑ t ∈ range T, hedgeExpectedLoss η ℓm t
      ≤ ∑ t ∈ range T, ℓm t i₀ + Real.log m / η + η * T / 2 := by
  have := hedge_regret hη hℓ i₀
  rwa [Fintype.card_fin] at this

end Fin

/-! ### Tests and adversarial examples: concrete symbolic pins

`Real.exp` is not computable, so these are **concrete symbolic pins**, not executable ones:
closed forms on a concrete loss sequence, kernel-checked by `simp`/`norm_num`, plus the
endpoints. -/

section Tests

/-- Two experts; expert `0` loses at round `0`, expert `1` does not; nothing afterwards. -/
private def twoLoss : ℕ → Fin 2 → ℝ
  | 0, i => if i = 0 then 1 else 0
  | _ + 1, _ => 0

private theorem twoLoss_mem (t : ℕ) (i : Fin 2) : 0 ≤ twoLoss t i ∧ twoLoss t i ≤ 1 := by
  cases t with
  | zero => simp only [twoLoss]; split_ifs <;> norm_num
  | succ t => simp [twoLoss]

-- **Round `0` is uniform**: `1/2` each.
example (η : ℝ) : hedgeProb η twoLoss 0 0 = 1 / 2 := by
  rw [hedgeProb_zero]; norm_num

-- **The update, computed**: after round `0` the losing expert's weight is `exp (−η)`, the other's
-- stays `1`, so the played distribution is `(exp (−η) / (exp (−η) + 1), 1 / (exp (−η) + 1))`.
example (η : ℝ) : hedgeWeight η twoLoss 1 0 = Real.exp (-η) := by
  simp [hedgeWeight, twoLoss]
example (η : ℝ) : hedgeWeight η twoLoss 1 1 = 1 := by
  simp [hedgeWeight, twoLoss]
example (η : ℝ) : hedgePotential η twoLoss 1 = Real.exp (-η) + 1 := by
  simp [hedgePotential, hedgeWeight, twoLoss, Fin.sum_univ_two]
example (η : ℝ) : hedgeProb η twoLoss 1 1 = 1 / (Real.exp (-η) + 1) := by
  simp [hedgeProb, hedgePotential, hedgeWeight, twoLoss, Fin.sum_univ_two]

-- **The forecaster moves mass to the better expert** for every `η > 0`.
example {η : ℝ} (hη : 0 < η) : hedgeProb η twoLoss 1 0 < hedgeProb η twoLoss 1 1 := by
  have h1 : Real.exp (-η) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < Real.exp (-η) + 1 := by positivity
  have e0 : hedgeProb η twoLoss 1 0 = Real.exp (-η) / (Real.exp (-η) + 1) := by
    simp [hedgeProb, hedgePotential, hedgeWeight, twoLoss, Fin.sum_univ_two]
  have e1 : hedgeProb η twoLoss 1 1 = 1 / (Real.exp (-η) + 1) := by
    simp [hedgeProb, hedgePotential, hedgeWeight, twoLoss, Fin.sum_univ_two]
  rw [e0, e1]
  exact div_lt_div_of_pos_right h1 hpos

-- **Rounds `≥ 1` are stationary** on this sequence: nothing is lost afterwards, so the weights
-- and the distribution at round `2` equal those at round `1`.
example (η : ℝ) : hedgeWeight η twoLoss 2 = hedgeWeight η twoLoss 1 := by
  funext i
  rw [hedgeWeight_succ]
  simp [twoLoss]

-- **Zero loss keeps the distribution uniform at every round.**
example (η : ℝ) (t : ℕ) (i : Fin 3) : hedgeProb η (fun _ _ => (0 : ℝ)) t i = 1 / 3 := by
  simp [hedgeProb, hedgePotential, hedgeWeight]

-- **The regret bound, instantiated** at `m = 2`, `η = 1`, against expert `1` on `twoLoss`;
-- `T = 0` reads `0 ≤ 0 + log 2 + 0`.
example (T : ℕ) :
    ∑ t ∈ range T, hedgeExpectedLoss 1 twoLoss t
      ≤ ∑ t ∈ range T, twoLoss t 1 + Real.log 2 / 1 + 1 * T / 2 := by
  have := hedge_regret_fin (ℓm := twoLoss) one_pos (T := T) (fun t _ => twoLoss_mem t) 1
  simpa using this
example : ∑ t ∈ range 0, hedgeExpectedLoss 1 twoLoss t
    ≤ ∑ t ∈ range 0, twoLoss t 1 + Real.log 2 / 1 + 1 * (0 : ℕ) / 2 :=
  hedge_regret_fin (ℓm := twoLoss) one_pos (T := 0) (fun t _ => twoLoss_mem t) 1

-- **Arbitrary `η`**: the bound is stated at `η = 5`, beyond the `η < 2` an unrelaxed
-- telescoping would have imposed.
example (T : ℕ) :
    ∑ t ∈ range T, hedgeExpectedLoss 5 twoLoss t
      ≤ ∑ t ∈ range T, twoLoss t 0 + Real.log 2 / 5 + 5 * T / 2 := by
  have := hedge_regret_fin (ℓm := twoLoss) (by norm_num : (0 : ℝ) < 5) (T := T)
    (fun t _ => twoLoss_mem t) 0
  simpa using this

-- **Finite horizon**: the bound at `T = 1` is unaffected by an out-of-range loss at round `1`.
private def wildLater : ℕ → Fin 2 → ℝ
  | 0, i => if i = 0 then 1 else 0
  | _ + 1, _ => 7
example : ∑ t ∈ range 1, hedgeExpectedLoss 1 wildLater t
    ≤ ∑ t ∈ range 1, wildLater t 1 + Real.log 2 / 1 + 1 * (1 : ℕ) / 2 :=
  hedge_regret_fin (ℓm := wildLater) one_pos (T := 1)
    (fun t ht i => by
      obtain rfl : t = 0 := by omega
      simp only [wildLater]; split_ifs <;> norm_num) 1

-- **The empty-expert endpoint**: no distribution, potential `0`, expected loss `0`.
example (η : ℝ) (ℓ : ℕ → Fin 0 → ℝ) (t : ℕ) : hedgePotential η ℓ t = 0 :=
  hedgePotential_of_isEmpty
example (η : ℝ) (ℓ : ℕ → Fin 0 → ℝ) (t : ℕ) : ∑ i, hedgeProb η ℓ t i = 0 :=
  sum_hedgeProb_of_isEmpty
example (η : ℝ) (ℓ : ℕ → Fin 0 → ℝ) (t : ℕ) : hedgeExpectedLoss η ℓ t = 0 :=
  hedgeExpectedLoss_of_isEmpty

-- **Relabeling**: swapping the two experts swaps the probabilities.
example (η : ℝ) (t : ℕ) :
    hedgeProb η (fun s j => twoLoss s (Equiv.swap (0 : Fin 2) 1 j)) t 0
      = hedgeProb η twoLoss t 1 := by
  rw [hedgeProb_comp_equiv]
  simp

-- **Causal congruence**: changing the loss at round `3` does not change round `2`.
example (η : ℝ) (ℓ ℓ' : ℕ → Fin 2 → ℝ) (h : ∀ s < 2, ℓ s = ℓ' s) :
    hedgeProb η ℓ 2 = hedgeProb η ℓ' 2 :=
  hedgeProb_congr h

end Tests

end RegularityLemmata
