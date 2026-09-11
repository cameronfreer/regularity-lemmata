/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Partition.BalancedSlicing
import RegularityLemmata.Partition.ExplicitPolyGeometricThreshold

/-!
# Slicing block sizes, slacks, and the geometric races

Named parameters for consuming `exists_balanced_slicing` at proportional block sizes, and
the geometric races that discharge its ratio hypothesis beyond named host-size thresholds:

* `sliceBlockSize μ n = ⌊μ n⌋` — a block size at host fraction `μ`;
* `sliceSlack μ ν n = ⌊ν · sliceBlockSize μ n⌋` — the per-block density slack (`β = ν`);
* `sliceRaceCoeff q μ ν` / `sliceThreshold q μ ν` — the **constant-count race**: at most
  `⌈2/μ⌉` blocks per piece against `2 q ⌈1/ν⌉` trace sets, a degree-`0` event count
  against `polyGeometricThreshold` (`slice_sampling_race`);
* `sliceRaceCoeffLinear μ ν` / `sliceThresholdLinear μ ν` — the **linear-count race**: the
  trace family may be as large as the host itself, and the exponent grows linearly with
  the host too, so the race runs at degree `1` (`slice_sampling_race_linear`).

The joint monotonicity lemmas (`sliceThreshold_le_sliceThreshold`,
`sliceThresholdLinear_le_sliceThresholdLinear`) let consumers state bound suites over
their own parameters.
-/

namespace RegularityLemmata

/-- A common block size: fraction `μ` of the host, floored. -/
noncomputable def sliceBlockSize (μ : ℝ) (n : ℕ) : ℕ := ⌊μ * n⌋₊

/-- The per-block slack (the `t` of the slicing certificate): fraction `ν` of the block,
floored — so the slicing runs at density error `β = ν`. -/
noncomputable def sliceSlack (μ ν : ℝ) (n : ℕ) : ℕ := ⌊ν * sliceBlockSize μ n⌋₊

/-- The constant event-count coefficient of the race: at most `⌈2/μ⌉` blocks per piece,
each against `2 q ⌈1/ν⌉` trace sets. -/
noncomputable def sliceRaceCoeff (q : ℕ) (μ ν : ℝ) : ℕ := ⌈2 / μ⌉₊ * (2 * (q * ⌈1 / ν⌉₊))

/-- The host-size threshold beyond which the constant-count race closes. -/
noncomputable def sliceThreshold (q : ℕ) (μ ν : ℝ) : ℕ :=
  ⌈2 / (ν * μ) * (8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) + 8)⌉₊

section Facts

variable {q c n : ℕ} {μ ν : ℝ}

/-- The key mass fact at the threshold: `16 P + 16 ≤ ν μ n`. -/
theorem sliceThreshold_key (hμ : 0 < μ) (hν : 0 < ν)
    (hn : sliceThreshold q μ ν ≤ n) :
    16 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) + 16 ≤ ν * μ * n := by
  have hνμ : 0 < ν * μ := mul_pos hν hμ
  have h1 : (2 / (ν * μ)) * (8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ)
      + 8) ≤ (n : ℝ) := by
    calc (2 / (ν * μ)) * (8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) + 8)
        ≤ ((sliceThreshold q μ ν : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn

  rw [div_mul_eq_mul_div, div_le_iff₀ hνμ] at h1
  nlinarith
theorem sliceBlockSize_le (hμ : 0 ≤ μ) : (sliceBlockSize μ n : ℝ) ≤ μ * n :=
  Nat.floor_le (by positivity)

/-- Under the threshold hypotheses, the block size clears `16`; in particular it is
positive. -/
theorem sixteen_le_sliceBlockSize (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) : 16 ≤ sliceBlockSize μ n := by
  have hkey := sliceThreshold_key (q := q) hμ hν hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have h16 : (16 : ℝ) ≤ μ * n := by nlinarith
  exact Nat.le_floor (by exact_mod_cast h16)

/-- Half the real mass survives the floor once the block is large. -/
theorem sliceBlockSize_ge_half (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) : μ * n / 2 ≤ (sliceBlockSize μ n : ℝ) := by
  have h16 : (16 : ℕ) ≤ sliceBlockSize μ n := sixteen_le_sliceBlockSize hμ hν hν2 hn
  have hfloor : μ * n < (sliceBlockSize μ n : ℝ) + 1 := Nat.lt_floor_add_one _
  have h16R : (16 : ℝ) ≤ (sliceBlockSize μ n : ℝ) := by exact_mod_cast h16
  linarith

/-- The slack mass fact: `8 P + 8 ≤ ν · sliceBlockSize`. -/
theorem sliceSlack_mass (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) :
    8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) + 8
      ≤ ν * sliceBlockSize μ n := by
  have hkey := sliceThreshold_key (q := q) hμ hν hn
  have hhalf := sliceBlockSize_ge_half (q := q) hμ hν hν2 hn
  nlinarith

/-- In particular `8 ≤ ν · sliceBlockSize` — the largeness the chunk absorption consumes. -/
theorem eight_le_nu_mul_sliceBlockSize (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) : (8 : ℝ) ≤ ν * sliceBlockSize μ n := by
  have h := sliceSlack_mass (q := q) hμ hν hν2 hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  linarith

theorem sliceSlack_le (hν : 0 ≤ ν) : (sliceSlack μ ν n : ℝ) ≤ ν * sliceBlockSize μ n :=
  Nat.floor_le (by positivity)

theorem sliceSlack_lt_sliceBlockSize (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) : sliceSlack μ ν n < sliceBlockSize μ n := by
  have h16 := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
  have hle := sliceSlack_le (μ := μ) (n := n) hν.le
  have h1 : (sliceSlack μ ν n : ℝ) ≤ (1 / 2) * sliceBlockSize μ n := by
    have := mul_le_mul_of_nonneg_right hν2 (Nat.cast_nonneg (α := ℝ) (sliceBlockSize μ n))
    linarith
  have h2 : (sliceSlack μ ν n : ℝ) < (sliceBlockSize μ n : ℝ) := by
    have h16R : (16 : ℝ) ≤ (sliceBlockSize μ n : ℝ) := by exact_mod_cast h16
    linarith
  exact_mod_cast h2

/-- Piece-to-block count is bounded by the constant `⌈2/μ⌉`. -/
theorem sliceCount_le_ceil (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) (hc : c ≤ n) :
    c / sliceBlockSize μ n ≤ ⌈2 / μ⌉₊ := by
  have hhalf := sliceBlockSize_ge_half (q := q) hμ hν hν2 hn
  have h16 := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
  have hs0 : 0 < sliceBlockSize μ n := by omega
  have hs0R : (0 : ℝ) < (sliceBlockSize μ n : ℝ) := by exact_mod_cast hs0
  have h1 : ((c / sliceBlockSize μ n : ℕ) : ℝ) ≤ (c : ℝ) / (sliceBlockSize μ n : ℝ) :=
    Nat.cast_div_le
  have hn0 : (0 : ℝ) < μ * n := by
    have h16R : (16 : ℝ) ≤ (sliceBlockSize μ n : ℝ) := by exact_mod_cast h16
    have := sliceBlockSize_le (μ := μ) (n := n) hμ.le
    linarith
  have h2 : (c : ℝ) / (sliceBlockSize μ n : ℝ) ≤ 2 / μ := by
    rw [div_le_div_iff₀ hs0R hμ]
    have hcR : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
    nlinarith
  have h3 : ((c / sliceBlockSize μ n : ℕ) : ℝ) ≤ ((⌈2 / μ⌉₊ : ℕ) : ℝ) :=
    h1.trans (h2.trans (Nat.le_ceil _))
  exact_mod_cast h3

/-- The threshold is monotone in the family size, so one largeness hypothesis serves every
smaller family. -/
theorem sliceThreshold_mono_q {q q' : ℕ} {μ ν : ℝ} (hq : q ≤ q')
    (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2) :
    sliceThreshold q μ ν ≤ sliceThreshold q' μ ν := by
  unfold sliceThreshold
  refine Nat.ceil_le_ceil ?_
  have hK : sliceRaceCoeff q μ ν ≤ sliceRaceCoeff q' μ ν := by
    unfold sliceRaceCoeff
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq))
  have hP : polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4)
      ≤ polyGeometricThreshold (sliceRaceCoeff q' μ ν) 0 (ν / 4) :=
    polyGeometricThreshold_le_polyGeometricThreshold hK le_rfl (by positivity) le_rfl
      (by linarith)
  have hPR : (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ)
      ≤ (polyGeometricThreshold (sliceRaceCoeff q' μ ν) 0 (ν / 4) : ℝ) := by exact_mod_cast hP
  have hcoeff : (0 : ℝ) ≤ 2 / (ν * μ) := by positivity
  nlinarith

/-- The threshold is positive, so a host beyond it is nonempty. -/
theorem sliceThreshold_pos {q : ℕ} {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    0 < sliceThreshold q μ ν := by
  refine Nat.ceil_pos.mpr ?_
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have h1 : (0 : ℝ) < 2 / (ν * μ) := by positivity
  nlinarith

/-- Division-free race endpoint at degree `0`: a constant event count against geometric
decay. -/
private theorem event_mul_pow_lt_const (K E b B r : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hE : (E : ℝ) ≤ (K : ℝ)) (hB : 0 < B)
    (hratio : (b : ℝ) / B ≤ 1 - x) (hr : polyGeometricThreshold K 0 x ≤ r) :
    E * b ^ r < B ^ r := by
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hratio0 : (0 : ℝ) ≤ (b : ℝ) / B := by positivity
  have hsmall : (E : ℝ) * ((b : ℝ) / B) ^ r < 1 := by
    have hspec := polyGeometricThreshold_spec K 0 x hx hx1 r hr
    rw [pow_zero, mul_one] at hspec
    calc (E : ℝ) * ((b : ℝ) / B) ^ r
        ≤ (K : ℝ) * (1 - x) ^ r :=
          mul_le_mul hE (pow_le_pow_left₀ hratio0 hratio r) (by positivity)
            (Nat.cast_nonneg _)
      _ < 1 := hspec
  have hscaled : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) < (B : ℝ) ^ r * 1 :=
    mul_lt_mul_of_pos_left hsmall (pow_pos hBR r)
  have heq : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) = (E : ℝ) * (b : ℝ) ^ r := by
    rw [div_pow]
    field_simp
  rw [heq, mul_one] at hscaled
  exact_mod_cast hscaled

/-- **The constant-count race**: beyond `sliceThreshold`, any piece of the host satisfies
the ratio hypothesis of `exists_average_slicing` at block size `sliceBlockSize`, slack
`sliceSlack`, and `q` functions. The event count is constant (`sliceRaceCoeff`), so the
polynomial degree in the geometric threshold is `0`. -/
theorem slice_sampling_race (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) (hc : c ≤ n) :
    (c / sliceBlockSize μ n) * (2 * (q * ⌈1 / ν⌉₊))
        * (2 * sliceBlockSize μ n - sliceSlack μ ν n) ^ (sliceSlack μ ν n / 8)
      < (2 * sliceBlockSize μ n) ^ (sliceSlack μ ν n / 8) := by
  set m := sliceBlockSize μ n with hm
  set t := sliceSlack μ ν n with ht
  have h16 := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
  have htm := sliceSlack_lt_sliceBlockSize (q := q) hμ hν hν2 hn
  have hmass := sliceSlack_mass (q := q) hμ hν hν2 hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h16
    linarith
  -- The slack keeps at least half its real mass, so the contraction is at least `ν / 4`.
  have htfloor : ν * (m : ℝ) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
  have htge : ν * (m : ℝ) / 2 ≤ (t : ℝ) := by
    have h8 : (8 : ℝ) ≤ ν * m := by linarith
    linarith
  have hcontr : ((2 * m - t : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) ≤ 1 - ν / 4 := by
    have hcast : ((2 * m - t : ℕ) : ℝ) = 2 * (m : ℝ) - (t : ℝ) := by
      have : t ≤ 2 * m := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  -- The exponent clears the geometric threshold.
  have htP : 8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4)) + 7 ≤ t := by
    have h1 : (8 * (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) + 7)
        ≤ (t : ℝ) := by linarith
    exact_mod_cast h1
  have hr : polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) ≤ t / 8 := by omega
  -- The event count is at most the constant coefficient.
  have hE : ((c / m * (2 * (q * ⌈1 / ν⌉₊)) : ℕ) : ℝ) ≤ (sliceRaceCoeff q μ ν : ℝ) := by
    have h1 : c / m ≤ ⌈2 / μ⌉₊ := sliceCount_le_ceil (q := q) hμ hν hν2 hn hc
    have h2 : c / m * (2 * (q * ⌈1 / ν⌉₊)) ≤ ⌈2 / μ⌉₊ * (2 * (q * ⌈1 / ν⌉₊)) :=
      Nat.mul_le_mul_right _ h1
    rw [sliceRaceCoeff]
    exact_mod_cast h2
  have hrace := event_mul_pow_lt_const (sliceRaceCoeff q μ ν)
    (c / m * (2 * (q * ⌈1 / ν⌉₊))) (2 * m - t) (2 * m) (t / 8)
    (x := ν / 4) (by positivity) (by linarith) hE (by omega) hcontr hr
  exact hrace

end Facts


/-! ### The linear race: host-sized trace families

When the trace family is as large as the host itself, the event count grows **linearly**
in the host size. The geometric decay still wins — the race runs at polynomial degree
`1`. -/

/-- The event-count coefficient of the linear race. -/
noncomputable def sliceRaceCoeffLinear (μ ν : ℝ) : ℕ :=
  ⌈2 / μ⌉₊ * (2 * ⌈1 / ν⌉₊) * ⌈64 / (ν * μ)⌉₊

/-- The host-size threshold of the linear race. -/
noncomputable def sliceThresholdLinear (μ ν : ℝ) : ℕ :=
  ⌈2 / (ν * μ) * (8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) + 8)⌉₊

section SymFacts

variable {q c n : ℕ} {μ ν : ℝ}

theorem sliceThresholdLinear_key (hμ : 0 < μ) (hν : 0 < ν)
    (hn : sliceThresholdLinear μ ν ≤ n) :
    16 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) + 16 ≤ ν * μ * n := by
  have hνμ : 0 < ν * μ := mul_pos hν hμ
  have h1 : (2 / (ν * μ)) * (8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ)
      + 8) ≤ (n : ℝ) := by
    calc (2 / (ν * μ))
          * (8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) + 8)
        ≤ ((sliceThresholdLinear μ ν : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, div_le_iff₀ hνμ] at h1
  nlinarith

theorem sliceThresholdLinear_pos (hμ : 0 < μ) (hν : 0 < ν) :
    0 < sliceThresholdLinear μ ν := by
  refine Nat.ceil_pos.mpr ?_
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have h1 : (0 : ℝ) < 2 / (ν * μ) := by positivity
  nlinarith

theorem sixteen_le_sliceBlockSize_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) : 16 ≤ sliceBlockSize μ n := by
  have hkey := sliceThresholdLinear_key hμ hν hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have h16 : (16 : ℝ) ≤ μ * n := by nlinarith
  exact Nat.le_floor (by exact_mod_cast h16)

theorem sliceBlockSize_ge_half_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) : μ * n / 2 ≤ (sliceBlockSize μ n : ℝ) := by
  have h16 : (16 : ℕ) ≤ sliceBlockSize μ n := sixteen_le_sliceBlockSize_linear hμ hν hν2 hn
  have hfloor : μ * n < (sliceBlockSize μ n : ℝ) + 1 := Nat.lt_floor_add_one _
  have h16R : (16 : ℝ) ≤ (sliceBlockSize μ n : ℝ) := by exact_mod_cast h16
  linarith

theorem sliceSlack_mass_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) :
    8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) + 8
      ≤ ν * sliceBlockSize μ n := by
  have hkey := sliceThresholdLinear_key hμ hν hn
  have hhalf := sliceBlockSize_ge_half_linear hμ hν hν2 hn
  nlinarith

theorem eight_le_nu_mul_sliceBlockSize_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) : (8 : ℝ) ≤ ν * sliceBlockSize μ n := by
  have h := sliceSlack_mass_linear hμ hν hν2 hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  linarith

theorem sliceCount_le_ceil_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) (hc : c ≤ n) :
    c / sliceBlockSize μ n ≤ ⌈2 / μ⌉₊ := by
  have hhalf := sliceBlockSize_ge_half_linear hμ hν hν2 hn
  have h16 := sixteen_le_sliceBlockSize_linear hμ hν hν2 hn
  have hs0 : 0 < sliceBlockSize μ n := by omega
  have hs0R : (0 : ℝ) < (sliceBlockSize μ n : ℝ) := by exact_mod_cast hs0
  have h1 : ((c / sliceBlockSize μ n : ℕ) : ℝ) ≤ (c : ℝ) / (sliceBlockSize μ n : ℝ) :=
    Nat.cast_div_le
  have hn0 : (0 : ℝ) < μ * n := by
    have h16R : (16 : ℝ) ≤ (sliceBlockSize μ n : ℝ) := by exact_mod_cast h16
    have := sliceBlockSize_le (μ := μ) (n := n) hμ.le
    linarith
  have h2 : (c : ℝ) / (sliceBlockSize μ n : ℝ) ≤ 2 / μ := by
    rw [div_le_div_iff₀ hs0R hμ]
    have hcR : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
    nlinarith
  have h3 : ((c / sliceBlockSize μ n : ℕ) : ℝ) ≤ ((⌈2 / μ⌉₊ : ℕ) : ℝ) :=
    h1.trans (h2.trans (Nat.le_ceil _))
  exact_mod_cast h3

/-- Division-free race endpoint at degree `1`: a linear event count against geometric
decay. -/
private theorem event_mul_pow_lt_linear (K E b B r : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hE : (E : ℝ) ≤ (K : ℝ) * (r : ℝ)) (hB : 0 < B)
    (hratio : (b : ℝ) / B ≤ 1 - x) (hr : polyGeometricThreshold K 1 x ≤ r) :
    E * b ^ r < B ^ r := by
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hratio0 : (0 : ℝ) ≤ (b : ℝ) / B := by positivity
  have hsmall : (E : ℝ) * ((b : ℝ) / B) ^ r < 1 := by
    have hspec := polyGeometricThreshold_spec K 1 x hx hx1 r hr
    rw [pow_one] at hspec
    calc (E : ℝ) * ((b : ℝ) / B) ^ r
        ≤ (K : ℝ) * (r : ℝ) * (1 - x) ^ r :=
          mul_le_mul hE (pow_le_pow_left₀ hratio0 hratio r) (by positivity)
            (by positivity)
      _ < 1 := hspec
  have hscaled : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) < (B : ℝ) ^ r * 1 :=
    mul_lt_mul_of_pos_left hsmall (pow_pos hBR r)
  have heq : (B : ℝ) ^ r * ((E : ℝ) * ((b : ℝ) / B) ^ r) = (E : ℝ) * (b : ℝ) ^ r := by
    rw [div_pow]
    field_simp
  rw [heq, mul_one] at hscaled
  exact_mod_cast hscaled

/-- **The linear-count race**: with the family size bounded by the host itself, the ratio
hypothesis of `exists_average_slicing` still holds beyond `sliceThresholdLinear`, because
the exponent grows linearly in the host while the event count is linear too — a degree-`1`
geometric race. -/
theorem slice_sampling_race_linear (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThresholdLinear μ ν ≤ n) (hc : c ≤ n) (hq : q ≤ n) :
    (c / sliceBlockSize μ n) * (2 * (q * ⌈1 / ν⌉₊))
        * (2 * sliceBlockSize μ n - sliceSlack μ ν n) ^ (sliceSlack μ ν n / 8)
      < (2 * sliceBlockSize μ n) ^ (sliceSlack μ ν n / 8) := by
  set m := sliceBlockSize μ n with hm
  set t := sliceSlack μ ν n with ht
  have h16 := sixteen_le_sliceBlockSize_linear (n := n) hμ hν hν2 hn
  have hmass := sliceSlack_mass_linear (n := n) hμ hν hν2 hn
  have hP : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h16
    linarith
  have htle : (t : ℝ) ≤ ν * m := sliceSlack_le hν.le
  have htm : t < m := by
    have h1 : (t : ℝ) ≤ (1 / 2) * m := by nlinarith
    have h16R : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h16
    have h2 : (t : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast h2
  have htfloor : ν * (m : ℝ) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
  have htge : ν * (m : ℝ) / 2 ≤ (t : ℝ) := by
    have h8 : (8 : ℝ) ≤ ν * m := by linarith
    linarith
  have hcontr : ((2 * m - t : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) ≤ 1 - ν / 4 := by
    have hcast : ((2 * m - t : ℕ) : ℝ) = 2 * (m : ℝ) - (t : ℝ) := by
      have : t ≤ 2 * m := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have htP : 8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4)) + 7 ≤ t := by
    have h1 : (8 * (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) + 7)
        ≤ (t : ℝ) := by linarith
    exact_mod_cast h1
  have hr : polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) ≤ t / 8 := by omega
  -- Event count: linear in the exponent.
  have hE : ((c / m * (2 * (q * ⌈1 / ν⌉₊)) : ℕ) : ℝ)
      ≤ (sliceRaceCoeffLinear μ ν : ℝ) * ((t / 8 : ℕ) : ℝ) := by
    have h1 : c / m ≤ ⌈2 / μ⌉₊ := sliceCount_le_ceil_linear hμ hν hν2 hn hc
    -- `n ≤ 64 (t/8) / (νμ)`: the slack keeps a `νμ/4` fraction of the host, and
    -- `t < 8 (t/8) + 8 ≤ 16 (t/8)` once `t ≥ 8`.
    have hP1 : 1 ≤ polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) := by
      rw [polyGeometricThreshold]
      omega
    have hr8 : (1 : ℕ) ≤ t / 8 := by omega
    have ht16 : (t : ℝ) ≤ 16 * ((t / 8 : ℕ) : ℝ) := by
      have h2 : t < 8 * (t / 8) + 8 := by omega
      have h3 : (t : ℝ) < 8 * ((t / 8 : ℕ) : ℝ) + 8 := by exact_mod_cast h2
      have h4 : (8 : ℝ) ≤ 8 * ((t / 8 : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((t / 8 : ℕ) : ℝ) := by exact_mod_cast hr8
        linarith
      linarith
    have hνμn : ν * μ * (n : ℝ) / 4 ≤ (t : ℝ) := by
      have hhalf := sliceBlockSize_ge_half_linear (n := n) hμ hν hν2 hn
      nlinarith
    have hn64 : (n : ℝ) ≤ 64 * ((t / 8 : ℕ) : ℝ) / (ν * μ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hq64 : (q : ℝ) ≤ ⌈64 / (ν * μ)⌉₊ * ((t / 8 : ℕ) : ℝ) := by
      have hqn : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
      have hceil : 64 / (ν * μ) ≤ (⌈64 / (ν * μ)⌉₊ : ℝ) := Nat.le_ceil _
      have hr8R : (0 : ℝ) ≤ ((t / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h64 : 64 * ((t / 8 : ℕ) : ℝ) / (ν * μ)
          = 64 / (ν * μ) * ((t / 8 : ℕ) : ℝ) := by ring
      rw [h64] at hn64
      calc (q : ℝ) ≤ 64 / (ν * μ) * ((t / 8 : ℕ) : ℝ) := hqn.trans hn64
        _ ≤ (⌈64 / (ν * μ)⌉₊ : ℝ) * ((t / 8 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hceil hr8R
    have h1R : ((c / m : ℕ) : ℝ) ≤ (⌈2 / μ⌉₊ : ℝ) := by exact_mod_cast h1
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have hcm0 : (0 : ℝ) ≤ ((c / m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hν0 : (0 : ℝ) ≤ (⌈1 / ν⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [sliceRaceCoeffLinear]
    push_cast
    nlinarith [mul_le_mul h1R (mul_le_mul_of_nonneg_left hq64 (by positivity : (0:ℝ) ≤ 2 * (⌈1 / ν⌉₊ : ℝ))) (by positivity) (Nat.cast_nonneg _)]
  exact event_mul_pow_lt_linear (sliceRaceCoeffLinear μ ν)
    (c / m * (2 * (q * ⌈1 / ν⌉₊))) (2 * m - t) (2 * m) (t / 8)
    (x := ν / 4) (by positivity) (by linarith) hE (by omega) hcontr hr

end SymFacts



/-- **Joint monotonicity of the constant-count threshold**: a larger family, smaller block
fraction, or smaller slack all raise it. Stated jointly, over the positive domain with
`ν ≤ 1/2`, so consumers compose one lemma. -/
theorem sliceThreshold_le_sliceThreshold {q q' : ℕ} {μ μ' ν ν' : ℝ} (hq : q ≤ q')
    (hμ' : 0 < μ') (hμle : μ' ≤ μ) (hν' : 0 < ν') (hνle : ν' ≤ ν) (hν2 : ν ≤ 1 / 2) :
    sliceThreshold q μ ν ≤ sliceThreshold q' μ' ν' := by
  have hμ : 0 < μ := lt_of_lt_of_le hμ' hμle
  have hν : 0 < ν := lt_of_lt_of_le hν' hνle
  unfold sliceThreshold
  refine Nat.ceil_le_ceil ?_
  have hK : sliceRaceCoeff q μ ν ≤ sliceRaceCoeff q' μ' ν' := by
    unfold sliceRaceCoeff
    have h1 : ⌈2 / μ⌉₊ ≤ ⌈2 / μ'⌉₊ :=
      Nat.ceil_le_ceil (div_le_div_of_nonneg_left (by norm_num) hμ' hμle)
    have h2 : ⌈1 / ν⌉₊ ≤ ⌈1 / ν'⌉₊ :=
      Nat.ceil_le_ceil (div_le_div_of_nonneg_left (by norm_num) hν' hνle)
    exact Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul hq h2))
  have hP : polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4)
      ≤ polyGeometricThreshold (sliceRaceCoeff q' μ' ν') 0 (ν' / 4) :=
    polyGeometricThreshold_le_polyGeometricThreshold hK le_rfl (by positivity)
      (by linarith) (by linarith)
  have hPR : (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ)
      ≤ (polyGeometricThreshold (sliceRaceCoeff q' μ' ν') 0 (ν' / 4) : ℝ) := by
    exact_mod_cast hP
  have hcoeff : 2 / (ν * μ) ≤ 2 / (ν' * μ') := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul hνle hμle hμ'.le hν.le
  have hc' : (0 : ℝ) ≤ 2 / (ν' * μ') := by positivity
  have hc : (0 : ℝ) ≤ 2 / (ν * μ) := by positivity
  have hP0 : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeff q μ ν) 0 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  nlinarith

/-- **Joint monotonicity of the linear-count threshold**: a smaller block fraction or
smaller slack raises it. -/
theorem sliceThresholdLinear_le_sliceThresholdLinear {μ μ' ν ν' : ℝ}
    (hμ' : 0 < μ') (hμle : μ' ≤ μ) (hν' : 0 < ν') (hνle : ν' ≤ ν) (hν2 : ν ≤ 1 / 2) :
    sliceThresholdLinear μ ν ≤ sliceThresholdLinear μ' ν' := by
  have hμ : 0 < μ := lt_of_lt_of_le hμ' hμle
  have hν : 0 < ν := lt_of_lt_of_le hν' hνle
  unfold sliceThresholdLinear
  refine Nat.ceil_le_ceil ?_
  have hK : sliceRaceCoeffLinear μ ν ≤ sliceRaceCoeffLinear μ' ν' := by
    unfold sliceRaceCoeffLinear
    have h1 : ⌈2 / μ⌉₊ ≤ ⌈2 / μ'⌉₊ :=
      Nat.ceil_le_ceil (div_le_div_of_nonneg_left (by norm_num) hμ' hμle)
    have h2 : ⌈1 / ν⌉₊ ≤ ⌈1 / ν'⌉₊ :=
      Nat.ceil_le_ceil (div_le_div_of_nonneg_left (by norm_num) hν' hνle)
    have h3 : ⌈64 / (ν * μ)⌉₊ ≤ ⌈64 / (ν' * μ')⌉₊ := by
      refine Nat.ceil_le_ceil ?_
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul hνle hμle hμ'.le hν.le
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ h2)) h3
  have hP : polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4)
      ≤ polyGeometricThreshold (sliceRaceCoeffLinear μ' ν') 1 (ν' / 4) :=
    polyGeometricThreshold_le_polyGeometricThreshold hK le_rfl (by positivity)
      (by linarith) (by linarith)
  have hPR : (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ)
      ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ' ν') 1 (ν' / 4) : ℝ) := by
    exact_mod_cast hP
  have hcoeff : 2 / (ν * μ) ≤ 2 / (ν' * μ') := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul hνle hμle hμ'.le hν.le
  have hc' : (0 : ℝ) ≤ 2 / (ν' * μ') := by positivity
  have hP0 : (0 : ℝ) ≤ (polyGeometricThreshold (sliceRaceCoeffLinear μ ν) 1 (ν / 4) : ℝ) :=
    Nat.cast_nonneg _
  nlinarith



/-! ### Balanced slicing at the named parameters

The sampling corollary: a consumer supplies the carrier, a finite family of test sets, the
block fraction `μ`, the tolerance `ν`, a family-size ceiling `q`, and a host size beyond
`sliceThreshold q μ ν`; every side condition of `exists_balanced_slicing` is discharged here
from those inputs (block size and slack from `sliceBlockSize` and `sliceSlack`, positivity and
`t < s` from `sixteen_le_sliceBlockSize` and `sliceSlack_lt_sliceBlockSize`, `t ≤ ν·s` from
`sliceSlack_le`, and the ratio from the constant-count race with the family term `2 · |F|`
bounded by the race's `2 · q · ⌈1/ν⌉₊`). The normalization is the parent-density one of
`exists_balanced_slicing` and is not changed. -/

/-- **Balanced slicing beyond the named threshold.** For `n ≥ sliceThreshold q μ ν`, a carrier
`A` of size at most `n` and a family `F` of at most `q` test sets: `A.card / sliceBlockSize μ n`
disjoint blocks of exact size `sliceBlockSize μ n` inside `A`, on each of which every member of
`F` has density within `ν` of its density on `A`. The leftover is `A.card % sliceBlockSize μ n`
(`SliceCert.card_leftover_eq_mod`). Hypotheses: `0 < μ`, `0 < ν ≤ 1/2`, the threshold,
`A.card ≤ n`, `A.Nonempty` (for the parent density), `F.card ≤ q`. Nothing is chosen here:
`s`, `t`, and the ratio are computed from `(μ, ν, n)` in that order.

**The zero-block case is part of the contract.** `A.card ≤ n` does not make the block size fit
inside `A`: `sliceBlockSize μ n = ⌊μ·n⌋₊` can exceed `A.card` (for a small carrier inside a large
host, or for `μ > 1`), and then `A.card / sliceBlockSize μ n = 0`, the certificate has no blocks,
its leftover is all of `A`, and the density conclusion is vacuous. The specialization
`exists_balanced_slicing_of_threshold_self` at `n = A.card` and `μ ≤ 1` returns at least one
block. -/
theorem exists_balanced_slicing_of_threshold [DecidableEq α] (A : Finset α)
    (F : Finset (Finset α)) {q n : ℕ} {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ n) (hAn : A.card ≤ n) (hA : A.Nonempty) (hF : F.card ≤ q) :
    ∃ cert : SliceCert A (traceComplementClosure A F) (A.card / sliceBlockSize μ n)
        (sliceBlockSize μ n) (sliceSlack μ ν n),
      ∀ T ∈ F, ∀ j, |((T ∩ cert.block j).card : ℝ) / sliceBlockSize μ n
          - ((A ∩ T).card : ℝ) / A.card| ≤ ν := by
  have hs : 0 < sliceBlockSize μ n := by
    have := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
    omega
  have ht : sliceSlack μ ν n < sliceBlockSize μ n :=
    sliceSlack_lt_sliceBlockSize (q := q) hμ hν hν2 hn
  have htβ : (sliceSlack μ ν n : ℝ) ≤ ν * sliceBlockSize μ n := sliceSlack_le hν.le
  have hrace := slice_sampling_race (q := q) (c := A.card) hμ hν hν2 hn hAn
  have hfam : 2 * F.card ≤ 2 * (q * ⌈1 / ν⌉₊) := by
    have hc : 1 ≤ ⌈1 / ν⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    calc 2 * F.card ≤ 2 * q := Nat.mul_le_mul_left 2 hF
      _ = 2 * (q * 1) := by rw [mul_one]
      _ ≤ 2 * (q * ⌈1 / ν⌉₊) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left q hc)
  have hratio : (A.card / sliceBlockSize μ n) * (2 * F.card)
      * (2 * sliceBlockSize μ n - sliceSlack μ ν n) ^ (sliceSlack μ ν n / 8)
      < (2 * sliceBlockSize μ n) ^ (sliceSlack μ ν n / 8) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfam)) hrace
  exact exists_balanced_slicing A F hA hs ht htβ hratio

/-- **The intended sampling use, nonvacuous.** At `n = A.card` and `μ ≤ 1` the block size
`⌊μ·|A|⌋₊` fits inside `A`, so at least one block is returned: the block count
`A.card / sliceBlockSize μ A.card` is positive. Same conclusion as
`exists_balanced_slicing_of_threshold` otherwise; the threshold is now a condition on `A.card`. -/
theorem exists_balanced_slicing_of_threshold_self [DecidableEq α] (A : Finset α)
    (F : Finset (Finset α)) {q : ℕ} {μ ν : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hν : 0 < ν)
    (hν2 : ν ≤ 1 / 2) (hn : sliceThreshold q μ ν ≤ A.card) (hF : F.card ≤ q) :
    ∃ cert : SliceCert A (traceComplementClosure A F) (A.card / sliceBlockSize μ A.card)
        (sliceBlockSize μ A.card) (sliceSlack μ ν A.card),
      0 < A.card / sliceBlockSize μ A.card ∧
      ∀ T ∈ F, ∀ j, |((T ∩ cert.block j).card : ℝ) / sliceBlockSize μ A.card
          - ((A ∩ T).card : ℝ) / A.card| ≤ ν := by
  have hs : 0 < sliceBlockSize μ A.card := by
    have := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
    omega
  have hA : A.Nonempty := by
    rw [← Finset.card_pos]
    have hs' := sixteen_le_sliceBlockSize (q := q) hμ hν hν2 hn
    have : (sliceBlockSize μ A.card : ℝ) ≤ μ * A.card := sliceBlockSize_le hμ.le
    have h0 : (0 : ℝ) < A.card := by
      by_contra h
      push Not at h
      have : (sliceBlockSize μ A.card : ℝ) ≤ 0 := this.trans (by nlinarith)
      have : (16 : ℝ) ≤ sliceBlockSize μ A.card := by exact_mod_cast hs'
      linarith
    exact_mod_cast h0
  obtain ⟨cert, h⟩ :=
    exists_balanced_slicing_of_threshold A F hμ hν hν2 hn le_rfl hA hF
  refine ⟨cert, ?_, h⟩
  apply Nat.div_pos _ hs
  have h1 : (sliceBlockSize μ A.card : ℝ) ≤ A.card :=
    calc (sliceBlockSize μ A.card : ℝ) ≤ μ * A.card := sliceBlockSize_le hμ.le
      _ ≤ 1 * A.card := by gcongr
      _ = A.card := one_mul _
  exact_mod_cast h1

/-! ### Tests and adversarial examples -/

section Tests

-- **The named-parameter wrapper is a compiled consumer of the race**: a consumer supplies
-- `(A, F, μ, ν, q, n)` and receives exact-size blocks with parent-density control at tolerance
-- `ν`, together with the leftover `A.card % sliceBlockSize μ n`; no side condition of
-- `exists_balanced_slicing` is left to the consumer.
example [DecidableEq α] (A : Finset α) (F : Finset (Finset α)) {q n : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2) (hn : sliceThreshold q μ ν ≤ n)
    (hAn : A.card ≤ n) (hA : A.Nonempty) (hF : F.card ≤ q) :
    ∃ cert : SliceCert A (traceComplementClosure A F) (A.card / sliceBlockSize μ n)
        (sliceBlockSize μ n) (sliceSlack μ ν n),
      cert.leftover.card = A.card % sliceBlockSize μ n ∧
      ∀ T ∈ F, ∀ j, |((T ∩ cert.block j).card : ℝ) / sliceBlockSize μ n
          - ((A ∩ T).card : ℝ) / A.card| ≤ ν := by
  obtain ⟨cert, h⟩ := exists_balanced_slicing_of_threshold A F hμ hν hν2 hn hAn hA hF
  exact ⟨cert, cert.card_leftover_eq_mod, h⟩

-- **The zero-block endpoint of the wrapper**: when the block size exceeds the carrier, the block
-- count is `0`, the certificate returned by `exists_balanced_slicing_of_threshold` has no blocks,
-- its leftover is all of `A`, and the density conclusion is vacuous. Pinned at the level of the
-- block count and the leftover, since the wrapper's hypotheses cannot be met on a small concrete
-- host (the thresholds are large).
example [DecidableEq α] (A : Finset α) {n : ℕ} {μ : ℝ} (hlt : A.card < sliceBlockSize μ n) :
    A.card / sliceBlockSize μ n = 0 :=
  Nat.div_eq_of_lt hlt
example [DecidableEq α] (A : Finset α) (F : Finset (Finset α)) {n t : ℕ} {μ : ℝ}
    (cert : SliceCert A F (A.card / sliceBlockSize μ n) (sliceBlockSize μ n) t)
    (hlt : A.card < sliceBlockSize μ n) : cert.leftover = A := by
  have h0 : A.card / sliceBlockSize μ n = 0 := Nat.div_eq_of_lt hlt
  simp only [SliceCert.leftover, SliceCert.covered]
  have : (Finset.univ : Finset (Fin (A.card / sliceBlockSize μ n))) = ∅ := by
    rw [Finset.univ_eq_empty_iff]; rw [h0]; exact Fin.isEmpty'
  rw [this, Finset.biUnion_empty, Finset.sdiff_empty]
-- The block size can exceed the carrier even with `A.card ≤ n`: `μ` has no upper bound.
example : (2 : ℕ) < sliceBlockSize (3 : ℝ) 2 := by
  rw [sliceBlockSize]
  have : (⌊(3 : ℝ) * (2 : ℕ)⌋₊) = 6 := by norm_num
  omega

-- **The nonvacuous specialization**: at `n = A.card` and `μ ≤ 1` at least one block is
-- returned (statement-level; the threshold hypothesis is on `A.card`).
example [DecidableEq α] (A : Finset α) (F : Finset (Finset α)) {q : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hν : 0 < ν) (hν2 : ν ≤ 1 / 2)
    (hn : sliceThreshold q μ ν ≤ A.card) (hF : F.card ≤ q) :
    ∃ cert : SliceCert A (traceComplementClosure A F) (A.card / sliceBlockSize μ A.card)
        (sliceBlockSize μ A.card) (sliceSlack μ ν A.card),
      0 < A.card / sliceBlockSize μ A.card ∧
      ∀ T ∈ F, ∀ j, |((T ∩ cert.block j).card : ℝ) / sliceBlockSize μ A.card
          - ((A ∩ T).card : ℝ) / A.card| ≤ ν :=
  exists_balanced_slicing_of_threshold_self A F hμ hμ1 hν hν2 hn hF

-- Block sizes floor to zero below one block's worth of mass.
example : sliceBlockSize (1/4 : ℝ) 2 = 0 := by
  rw [sliceBlockSize, Nat.floor_eq_zero]
  norm_num

-- A concrete block size and its slack: `⌊(1/2)·9⌋ = 4` and `⌊(1/2)·4⌋ = 2`.
example : sliceBlockSize (1/2 : ℝ) 9 = 4 := by
  rw [sliceBlockSize, Nat.floor_eq_iff (by norm_num)]
  push_cast
  norm_num

example : sliceSlack (1/2 : ℝ) (1/2 : ℝ) 9 = 2 := by
  have h4 : sliceBlockSize (1/2 : ℝ) 9 = 4 := by
    rw [sliceBlockSize, Nat.floor_eq_iff (by norm_num)]
    push_cast
    norm_num
  rw [sliceSlack, h4, Nat.floor_eq_iff (by norm_num)]
  push_cast
  norm_num

end Tests


end RegularityLemmata
