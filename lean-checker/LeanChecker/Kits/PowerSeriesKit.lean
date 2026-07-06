import Mathlib

/-!
# Power-series coefficient uniqueness kit (issue #72)

Reusable analysis infrastructure for Putnam-style generating-function and
Taylor-series problems: extracting COEFFICIENT facts from the knowledge that a
power series agrees with a function near `0`.

Motivation: `putnam_1970_a1` gives an arbitrary coefficient sequence
`p : ℕ → ℝ` with only `∀ x ∈ ball 0 c, ∑' n, p n * x ^ n = f x` — reasoning
about the zeros of `p` first needs `p` pinned to THE power-series coefficients
of `f`. Mathlib has the one-dimensional uniqueness principle
(`HasFPowerSeriesAt.eq_formalMultilinearSeries`) and the scalar-series bridge
(`FormalMultilinearSeries.ofScalars`); this kit packages them in the
benchmark-shaped `∑' n, p n * x ^ n` form.

## Route to `putnam_1970_a1` (remaining gaps, deliberately out of scope here)

1. From the raw ball hypothesis, produce `HasFPowerSeriesAt f (ofScalars ℝ p) 0`
   — needs summability/radius extraction from pointwise convergence on a ball
   (the sum converges at every `x` in the ball, which bounds the radius below).
2. The coefficient formula for `Real.exp (a*x) * Real.cos (b*x)`
   (via the complex exponential: `p n = re ((a+bI)^n) / n!`).
3. The zero-set dichotomy from rationality/periodicity of `arctan (b/a) / π`.
-/

namespace LeanChecker.PowerSeriesKit

open FormalMultilinearSeries

/-- **Local coefficient uniqueness** at a point: two scalar power series
representing the same function have identical coefficient sequences. This is
the kit's core bridge from Mathlib's `FormalMultilinearSeries` uniqueness to
plain `ℕ → ℝ` coefficient talk. -/
theorem coeff_eq_of_hasFPowerSeriesAt {f : ℝ → ℝ} {p q : ℕ → ℝ} {x : ℝ}
    (hp : HasFPowerSeriesAt f (ofScalars ℝ p) x)
    (hq : HasFPowerSeriesAt f (ofScalars ℝ q) x) : p = q :=
  ofScalars_series_injective ℝ ℝ (hp.eq_formalMultilinearSeries hq)

/-- The benchmark-shaped sum: over `ℝ`, `ofScalarsSum p` is exactly
`fun x => ∑' n, p n * x ^ n`. -/
theorem ofScalarsSum_eq_tsum_mul (p : ℕ → ℝ) (x : ℝ) :
    ofScalarsSum p x = ∑' n : ℕ, p n * x ^ n := by
  rw [ofScalarsSum_eq_tsum]
  simp [smul_eq_mul]

/-- **Local coefficient uniqueness from locally equal sums**: two scalar power
series with positive radius of convergence whose sums agree on a neighborhood
of `0` have equal coefficients. -/
theorem coeff_eq_of_locally_eq_sum {p q : ℕ → ℝ}
    (hp : 0 < (ofScalars ℝ p).radius)
    (hq : 0 < (ofScalars ℝ q).radius)
    (heq : ∀ᶠ x in nhds (0 : ℝ), ofScalarsSum p x = ofScalarsSum q x) :
    p = q := by
  have Hp : HasFPowerSeriesAt (ofScalarsSum p) (ofScalars ℝ p) 0 :=
    ((ofScalars ℝ p).hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have Hq : HasFPowerSeriesAt (ofScalarsSum q) (ofScalars ℝ q) 0 :=
    ((ofScalars ℝ q).hasFPowerSeriesOnBall hq).hasFPowerSeriesAt
  exact ofScalars_series_injective ℝ ℝ (Hp.eq_formalMultilinearSeries_of_eventually Hq heq)

/-- Fixture: two locally equal power series, in the benchmark's own
`∑' n, p n * x ^ n` phrasing, have equal coefficients. -/
example {p q : ℕ → ℝ}
    (hp : 0 < (ofScalars ℝ p).radius)
    (hq : 0 < (ofScalars ℝ q).radius)
    (heq : ∀ᶠ x in nhds (0 : ℝ), ∑' n : ℕ, p n * x ^ n = ∑' n : ℕ, q n * x ^ n) :
    p = q := by
  refine coeff_eq_of_locally_eq_sum hp hq ?_
  filter_upwards [heq] with x hx
  rw [ofScalarsSum_eq_tsum_mul, ofScalarsSum_eq_tsum_mul, hx]

end LeanChecker.PowerSeriesKit
