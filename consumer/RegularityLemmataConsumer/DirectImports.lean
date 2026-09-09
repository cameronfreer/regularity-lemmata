import RegularityLemmata.Finite.Hedge
import RegularityLemmata.Finite.DensityBuckets

/-!
# Consumer check: direct module imports

Advertised entry points need not be facades: `Finite.Hedge` and `Finite.DensityBuckets` are
imported directly.
-/

open RegularityLemmata

namespace Consumer

/-- Bucket closeness, consumed as stated. -/
example {α x y : ℝ} (hα : 0 < α) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : densityBucket α x = densityBucket α y) : |x - y| < α :=
  abs_sub_lt_of_densityBucket_eq hα hx hy h

/-- The Hedge regret bound, consumed as stated. -/
example {ι : Type*} [Fintype ι] {η : ℝ} (hη : 0 < η) {T : ℕ} (ℓ : ℕ → ι → ℝ)
    (hℓ : ∀ t < T, ∀ i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1) (i₀ : ι) :
    ∑ t ∈ Finset.range T, hedgeExpectedLoss η ℓ t
      ≤ ∑ t ∈ Finset.range T, ℓ t i₀ + Real.log (Fintype.card ι) / η + η * T / 2 :=
  hedge_regret hη hℓ i₀

end Consumer
