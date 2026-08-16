/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import RegularityLemmata.Partition.SimultaneousSampling
import RegularityLemmata.Partition.ProportionalTraceForm
import RegularityLemmata.Partition.PolyGeometricThreshold
import RegularityLemmata.Partition.HypergeometricGeometric

/-!
# The coupled active-trace sampling schedule

The coupled tail keeps the trace-dependent numerator until the threshold-dependent denominator
is combined with it, producing the usable schedule condition

`m * |F_active| * (2*s - t)^r < (2*s)^r`   (with `r = t/8`)

— a genuine geometric factor at slack `t`, unlike the fully uniform numerator route (documented
as too coarse for the regime where the slack `t` is a small fraction of `s`).  Inactive traces
(test sets whose proportional window is already at `s`) are discharged exactly.
`exists_forall_event_mul_pow_lt_of_fixed_ratio` bridges `polyGeometricThreshold`-style
asymptotics to this division-free form for the eventual existential host threshold.
-/

open Finset

set_option maxHeartbeats 1600000

namespace RegularityLemmata

/-- Activity of the proportional window bounds the raw incidence numerator. -/
theorem mul_lt_mul_sub_of_proportional_active {a n s t : ℕ} (hn : 0 < n)
    (hactive : a * s / n + t < s) :
    a * s < n * (s - t) := by
  have hdiv : a * s < n * (a * s / n + 1) := Nat.lt_mul_div_succ _ hn
  have hquot : a * s / n + 1 ≤ s - t := by omega
  exact lt_of_lt_of_le hdiv (Nat.mul_le_mul_left n hquot)

/-- The falling-factorial corrections preserve a base bounded away from one.

The intended reading is
`a*s / ((a*s/n+t+2-r)*(n+1-r)) <= (2*s-t)/(2*s)`.
The hypotheses `8*r <= t` and `s <= n` absorb both `r`-shifts. -/
theorem coupled_proportional_base {a n s t r : ℕ} (hs : 0 < s) (hsn : s ≤ n)
    (ht : t < s) (hr : 8 * r ≤ t) (hactive : a * s / n + t < s) :
    2 * s * (a * s) ≤
      (2 * s - t) * (a * s / n + t + 2 - r) * (n + 1 - r) := by
  have hn : 0 < n := lt_of_lt_of_le hs hsn
  have has := (mul_lt_mul_sub_of_proportional_active hn hactive).le
  let x := a * s / n + 1
  let d := t + 1 - r
  let ss := s + 1 - r
  let nn := n + 1 - r
  have hrle : r ≤ t := by omega
  have htle : t ≤ s := ht.le
  have hx : x ≤ s - t := by
    dsimp [x]
    omega
  have hd : d + r = t + 1 := by
    dsimp [d]
    omega
  have hss : ss = (s - t) + d := by
    have hsplit : s + 1 - r = (s - t) + (t + 1 - r) := by omega
    simpa [ss, d] using hsplit
  have hden : a * s / n + t + 2 - r = x + d := by
    have hsplit (q : ℕ) : q + t + 2 - r = (q + 1) + (t + 1 - r) := by omega
    simpa [x, d] using hsplit (a * s / n)
  have hnn : nn + r = n + 1 := by
    dsimp [nn]
    omega
  have hsspos : 0 < ss := by
    dsimp [ss]
    omega
  have hcross : x * ss ≤ (s - t) * (x + d) := by
    rw [hss]
    calc
      x * ((s - t) + d) = x * (s - t) + x * d := by ring
      _ ≤ x * (s - t) + (s - t) * d := by gcongr
      _ = (s - t) * (x + d) := by ring
  have hasx : a * s ≤ n * x := by
    dsimp [x]
    exact (Nat.lt_mul_div_succ (a * s) hn).le
  have hA : (a * s) * ss ≤ n * (s - t) * (x + d) := by
    calc
      (a * s) * ss ≤ (n * x) * ss := Nat.mul_le_mul_right ss hasx
      _ = n * (x * ss) := by ring
      _ ≤ n * ((s - t) * (x + d)) := Nat.mul_le_mul_left n hcross
      _ = n * (s - t) * (x + d) := by ring
  have hC : 2 * s * n * (s - t) ≤ (2 * s - t) * ss * nn := by
    let u := 8 * s - t
    let b := 2 * s - t
    have htu : t ≤ 8 * s := by omega
    have hu : u + t = 8 * s := by
      dsimp [u]
      omega
    have hb : b + t = 2 * s := by
      dsimp [b]
      omega
    have hu_pos : 0 < u := by
      dsimp [u]
      omega
    have hb_pos : 0 < b := by
      dsimp [b]
      omega
    have hf1base : u ≤ 8 * ss := by
      dsimp [u, ss]
      omega
    have hf1 : s * u ≤ (8 * s) * ss := by
      calc
        s * u ≤ s * (8 * ss) := Nat.mul_le_mul_left s hf1base
        _ = (8 * s) * ss := by ring
    have hrt_scaled : 8 * s * r ≤ n * t := by
      calc
        8 * s * r = s * (8 * r) := by ring
        _ ≤ s * t := Nat.mul_le_mul_left s hr
        _ ≤ n * t := Nat.mul_le_mul_right t hsn
    have hf2 : n * u ≤ (8 * s) * nn := by
      nlinarith [hrt_scaled]
    have hprod : s * n * u ^ 2 ≤ (8 * s) ^ 2 * ss * nn := by
      have hp := Nat.mul_le_mul hf1 hf2
      nlinarith [hp]
    have ht_sq : t * t ≤ s * s := Nat.mul_le_mul ht.le ht.le
    have hbracket : t * t ≤ 32 * s * s + 18 * s * t := by nlinarith
    have hcubic := Nat.mul_le_mul_left t hbracket
    have hcore : 128 * s ^ 2 * (s - t) ≤ b * u ^ 2 := by
      show 128 * s ^ 2 * (s - t) ≤ (2 * s - t) * (8 * s - t) ^ 2
      have hcubicz : (t : ℤ) * (t * t) ≤ t * (32 * s * s + 18 * s * t) := by
        exact_mod_cast hcubic
      have ht2 : t ≤ 2 * s := by omega
      zify [htle, htu, ht2]
      nlinarith [hcubicz]
    have hcore_scaled := Nat.mul_le_mul_left (s * n) hcore
    have hprod_scaled := Nat.mul_le_mul_left b hprod
    have hlarge : 64 * s ^ 2 * (2 * s * n * (s - t)) ≤
        64 * s ^ 2 * (b * ss * nn) := by
      calc
        64 * s ^ 2 * (2 * s * n * (s - t)) =
            s * n * (128 * s ^ 2 * (s - t)) := by ring
        _ ≤ s * n * (b * u ^ 2) := hcore_scaled
        _ = b * (s * n * u ^ 2) := by ring
        _ ≤ b * ((8 * s) ^ 2 * ss * nn) := hprod_scaled
        _ = 64 * s ^ 2 * (b * ss * nn) := by ring
    have hscale : 0 < 64 * s ^ 2 := by positivity
    exact Nat.le_of_mul_le_mul_left hlarge hscale
  have hscaledA := Nat.mul_le_mul_left (2 * s) hA
  have hscaledC := Nat.mul_le_mul_right (x + d) hC
  have hwith : 2 * s * (a * s) * ss ≤
      (2 * s - t) * (x + d) * nn * ss := by
    calc
      2 * s * (a * s) * ss ≤ 2 * s * (n * (s - t) * (x + d)) := by
        simpa [Nat.mul_assoc] using hscaledA
      _ = (2 * s * n * (s - t)) * (x + d) := by ring
      _ ≤ ((2 * s - t) * ss * nn) * (x + d) := hscaledC
      _ = (2 * s - t) * (x + d) * nn * ss := by ring
  have hfin := Nat.le_of_mul_le_mul_right hwith hsspos
  rw [hden]
  exact hfin

/-- Power form of `coupled_proportional_base`, matching the exact moment numerator and
denominator in `card_upperViolations_geometric`. -/
theorem coupled_proportional_pow {a n s t r : ℕ} (hs : 0 < s) (hsn : s ≤ n)
    (ht : t < s) (hr : 8 * r ≤ t) (hactive : a * s / n + t < s) :
    (2 * s) ^ r * (a ^ r * s ^ r) ≤
      (2 * s - t) ^ r *
        ((a * s / n + t + 2 - r) ^ r * (n + 1 - r) ^ r) := by
  have hbase := coupled_proportional_base hs hsn ht hr hactive
  have hpow := Nat.pow_le_pow_left hbase r
  calc
    (2 * s) ^ r * (a ^ r * s ^ r) = (2 * s * (a * s)) ^ r := by
      ring
    _ ≤ ((2 * s - t) * (a * s / n + t + 2 - r) * (n + 1 - r)) ^ r := hpow
    _ = (2 * s - t) ^ r *
        ((a * s / n + t + 2 - r) ^ r * (n + 1 - r) ^ r) := by
      ring

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An active proportional upper-tail event has a uniform geometric ratio, while its exact
trace-dependent numerator is retained until after the threshold-dependent denominator is
combined with it. -/
theorem card_upperViolations_mul_pow_le (A : Finset α) {n s t r : ℕ}
    (hn : Fintype.card α = n) (hs : 0 < s) (hsn : s ≤ n) (ht : t < s)
    (hr : 8 * r ≤ t) (hactive : A.card * s / n + t < s) :
    (upperViolations A s (A.card * s / n + t)).card * (2 * s) ^ r ≤
      n.choose s * (2 * s - t) ^ r := by
  have hrs : r ≤ s := by omega
  have hgeom := card_upperViolations_geometric A (hrs := hrs)
    (hi := A.card * s / n + t)
  rw [hn] at hgeom
  have hratio := coupled_proportional_pow (a := A.card) hs hsn ht hr hactive
  let G := (A.card * s / n + t + 2 - r) ^ r * (n + 1 - r) ^ r
  have hG : 0 < G := by
    have h1 : 0 < A.card * s / n + t + 2 - r := by
      have h0 : 0 < t + 2 - r := by omega
      exact lt_of_lt_of_le h0 (Nat.sub_le_sub_right (Nat.le_add_left (t + 2) _) r)
    have h2 : 0 < n + 1 - r := by omega
    exact Nat.mul_pos (pow_pos h1 r) (pow_pos h2 r)
  have hgeom' : (upperViolations A s (A.card * s / n + t)).card * G
      ≤ n.choose s * (A.card ^ r * s ^ r) := by
    dsimp only [G]
    calc
      (upperViolations A s (A.card * s / n + t)).card *
          ((A.card * s / n + t + 2 - r) ^ r * (n + 1 - r) ^ r)
          = (upperViolations A s (A.card * s / n + t)).card *
              (A.card * s / n + t + 2 - r) ^ r * (n + 1 - r) ^ r := by ring
      _ ≤ n.choose s * A.card ^ r * s ^ r := hgeom
      _ = n.choose s * (A.card ^ r * s ^ r) := by ring
  have hratio' : (2 * s) ^ r * (A.card ^ r * s ^ r) ≤ (2 * s - t) ^ r * G := by
    dsimp only [G]
    exact hratio
  have hwithG :
      ((upperViolations A s (A.card * s / n + t)).card * (2 * s) ^ r) * G ≤
        (n.choose s * (2 * s - t) ^ r) * G := by
    calc
      ((upperViolations A s (A.card * s / n + t)).card * (2 * s) ^ r) * G =
          (2 * s) ^ r *
            ((upperViolations A s (A.card * s / n + t)).card * G) := by ring
      _ ≤ (2 * s) ^ r * (n.choose s * (A.card ^ r * s ^ r)) :=
        Nat.mul_le_mul_left _ hgeom'
      _ = n.choose s * ((2 * s) ^ r * (A.card ^ r * s ^ r)) := by ring
      _ ≤ n.choose s * ((2 * s - t) ^ r * G) := Nat.mul_le_mul_left _ hratio'
      _ = (n.choose s * (2 * s - t) ^ r) * G := by ring
  exact Nat.le_of_mul_le_mul_right hwithG hG

/-- Schedule-ready active-trace sampler with a genuine geometric factor.

Taking `r = t / 8` makes the event ratio approximately
`m * |active| * (1 - t/(2*s))^(t/8)`.  Inactive traces are discharged exactly. -/
theorem exists_equiv_forall_blocks_proportional_of_active_ratio
    {n s m t r : ℕ} (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hs : 0 < s) (ht : t < s) (hr : 8 * r ≤ t)
    (hchoose : 0 < n.choose s)
    (hratio : m * (F.filter fun A ↦ A.card * s / n + t < s).card *
        (2 * s - t) ^ r < (2 * s) ^ r) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ A.card * s / n + t := by
  let active := F.filter fun A ↦ A.card * s / n + t < s
  have hsn : s ≤ n := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs_pos
    · omega
    · rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
      · subst hm0
        rw [Nat.zero_mul] at hnm
        subst hnm
        rw [Nat.choose_eq_zero_of_lt (by omega)] at hchoose
        omega
      · calc s = 1 * s := (one_mul s).symm
          _ ≤ m * s := Nat.mul_le_mul_right s hm_pos
          _ = n := hnm.symm
  have htail : ∀ A ∈ active,
      (upperViolations A s (A.card * s / n + t)).card * (2 * s) ^ r ≤
        n.choose s * (2 * s - t) ^ r := by
    intro A hA
    exact card_upperViolations_mul_pow_le A hn hs hsn ht hr (Finset.mem_filter.mp hA).2
  have hD : 0 < (2 * s) ^ r := pow_pos (by omega) r
  have hsum : m * ∑ A ∈ active,
      (upperViolations A s (A.card * s / n + t)).card < n.choose s :=
    sum_bad_lt_of_mul_le_and_event_ratio active
      (fun A ↦ (upperViolations A s (A.card * s / n + t)).card)
      hchoose hD htail (by simpa [active] using hratio)
  obtain ⟨e, he⟩ := exists_equiv_forall_blocks_upper hn hnm active
    (fun A ↦ A.card * s / n + t) hsum
  refine ⟨e, fun A hA j hj ↦ ?_⟩
  by_cases hactive : A.card * s / n + t < s
  · exact he A (Finset.mem_filter.mpr ⟨hA, hactive⟩) j hj
  · have hjs : (j + 1) * s ≤ n := by
      calc
        (j + 1) * s ≤ m * s := Nat.mul_le_mul_right s hj
        _ = n := hnm.symm
    calc
      (A ∩ sampleBlock e s j).card ≤ (sampleBlock e s j).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = s := card_sampleBlock e hjs
      _ ≤ A.card * s / n + t := by omega

/-- The concrete eighth-slack moment satisfies the correction budget. -/
theorem eighth_moment_le_slack (t : ℕ) : 8 * (t / 8) ≤ t := Nat.mul_div_le t 8

/-- Once the slack is at least eight, the eighth-slack moment is still linear in the slack. -/
theorem slack_le_sixteen_mul_eighth_moment {t : ℕ} (ht : 8 ≤ t) :
    t ≤ 16 * (t / 8) := by
  omega

/-- The concrete moment exposes a genuinely contracting power ratio. -/
theorem eighth_moment_ratio_lt {s t : ℕ} (ht8 : 8 ≤ t) (hts : t < s) :
    (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8) := by
  apply Nat.pow_lt_pow_left
  · omega
  · omega

/-- A fixed real contraction and a polynomial event count imply the exact natural-number
power inequality required by the active sampler.  This is the bridge from the
polynomial-versus-geometric threshold to the division-free schedule. -/
theorem exists_forall_event_mul_pow_lt_of_fixed_ratio
    (K d : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ E b B : ℕ,
      E ≤ K * r ^ d → 0 < B → (b : ℝ) / B ≤ q → E * b ^ r < B ^ r := by
  obtain ⟨R, hR⟩ := exists_forall_nat_mul_pow_mul_geometric_lt_one K d q hq0 hq1
  refine ⟨R, fun r hr E b B hE hB hbq ↦ ?_⟩
  have hEreal : (E : ℝ) ≤ K * (r : ℝ) ^ d := by exact_mod_cast hE
  have hratio0 : 0 ≤ (b : ℝ) / B := by positivity
  have hratio_pow : ((b : ℝ) / B) ^ r ≤ q ^ r := by gcongr
  have hsmall : (E : ℝ) * ((b : ℝ) / B) ^ r < 1 := by
    calc
      (E : ℝ) * ((b : ℝ) / B) ^ r ≤
          (K * (r : ℝ) ^ d) * q ^ r := by gcongr
      _ < 1 := by simpa [mul_assoc] using hR r hr
  have hBreal : 0 < (B : ℝ) ^ r := pow_pos (by exact_mod_cast hB) r
  have hscaled : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) < (B : ℝ) ^ r * 1 :=
    mul_lt_mul_of_pos_left hsmall hBreal
  have hBne : ((B : ℝ)) ≠ 0 := by positivity
  have heq : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) =
      (E : ℝ) * (b : ℝ) ^ r := by
    rw [div_pow]
    field_simp
  have hreal : (E : ℝ) * (b : ℝ) ^ r < (B : ℝ) ^ r := by
    rw [heq, mul_one] at hscaled
    exact hscaled
  exact_mod_cast hreal

/-- Concrete `r = floor(t/8)` specialization of the active-trace sampler. -/
theorem exists_equiv_forall_blocks_proportional_eighth_moment
    {n s m t : ℕ} (hn : Fintype.card α = n) (hnm : n = m * s)
    (F : Finset (Finset α)) (hs : 0 < s) (ht : t < s)
    (hchoose : 0 < n.choose s)
    (hratio : m * (F.filter fun A ↦ A.card * s / n + t < s).card *
        (2 * s - t) ^ (t / 8) < (2 * s) ^ (t / 8)) :
    ∃ e : Fin n ≃ α, ∀ A ∈ F, ∀ j, j < m →
      (A ∩ sampleBlock e s j).card ≤ A.card * s / n + t := by
  exact exists_equiv_forall_blocks_proportional_of_active_ratio hn hnm F hs ht
    (eighth_moment_le_slack t) hchoose hratio

end RegularityLemmata
