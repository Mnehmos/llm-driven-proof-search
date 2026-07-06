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

/-! ## v2 (issue #86): from the raw ball hypothesis to Mathlib's shape

The benchmark hypothesis is rawer than v1's inputs: only
`∀ x ∈ ball 0 c, ∑' n, p n * x ^ n = f x`, with NO summability given. The v2
bridges close that distance:

- `summable_of_tsum_ne_zero` — Mathlib's `tsum` of a non-summable family is
  the junk value `0`, so wherever `f x ≠ 0` the benchmark equation itself
  forces summability. For `putnam_1970_a1`'s `f = exp(ax)·cos(bx)` this holds
  near `0` since `f 0 = 1`.
- `le_radius_ofScalars_of_summable_at` — PLAIN summability at one point `x`
  bounds the `ofScalars` radius below by `‖x‖₊` (terms → 0 → `=O(1)`; no
  absolute summability needed).
- `hasFPowerSeriesAt_of_eqOn_ball` — with the radius bound, the ball equation
  upgrades to `HasFPowerSeriesAt f (ofScalars ℝ p) 0`, which is exactly what
  v1's `coeff_eq_of_hasFPowerSeriesAt` consumes.

Route to `putnam_1970_a1` from here (remaining steps):
1. From continuity of `exp(ax)·cos(bx)` and `f 0 = 1`, pick a smaller ball
   where `f ≠ 0`; apply the three bridges to pin `p` to THE coefficients.
2. The coefficient formula `p n = Complex.re ((a + b*I) ^ n) / n!` for
   `exp(ax)·cos(bx)` (through `Complex.exp` and `Complex.ofReal_cos`).
3. The zero-set dichotomy from the argument of `a + b*I`: `p n = 0` iff
   `cos (n·θ) = 0` for `θ = arctan (b/a)`, whose solution set is empty or
   infinite by periodicity/rationality analysis. -/

section V2

open Filter

/-- **Junk-value bridge**: a `tsum` that is provably nonzero forces
summability, because Mathlib's `tsum` of a non-summable family is `0`. This
is how the benchmark's raw `∑' n, p n * x ^ n = f x` hypothesis yields
summability wherever `f x ≠ 0`. -/
theorem summable_of_tsum_ne_zero {g : ℕ → ℝ} (h : ∑' n, g n ≠ 0) : Summable g := by
  by_contra hs
  exact h (tsum_eq_zero_of_not_summable hs)

/-- **Radius from plain summability at a point**: if `∑ p n * x ^ n` is
summable (NOT necessarily absolutely), the `ofScalars` radius is at least
`‖x‖₊` — terms tend to `0`, hence are `=O(1)`. -/
theorem le_radius_ofScalars_of_summable_at {p : ℕ → ℝ} {x : ℝ}
    (h : Summable fun n => p n * x ^ n) :
    (‖x‖₊ : ENNReal) ≤ (ofScalars ℝ p).radius := by
  apply FormalMultilinearSeries.le_radius_of_isBigO
  have hO : (fun n => p n * x ^ n) =O[atTop] (fun _ => (1 : ℝ)) :=
    h.tendsto_atTop_zero.isBigO_one ℝ
  have heq : (fun n => ‖(ofScalars ℝ p) n‖ * (‖x‖₊ : ℝ) ^ n)
      = fun n => ‖p n * x ^ n‖ := by
    funext n
    rw [ofScalars_norm, coe_nnnorm, ← norm_pow, ← norm_mul]
  rw [heq]
  exact hO.norm_left

/-- **Ball-to-series bridge** (issue #86): a radius bound plus the raw ball
equation upgrade `f` to `HasFPowerSeriesAt f (ofScalars ℝ p) 0` — the exact
input shape of v1's `coeff_eq_of_hasFPowerSeriesAt`. -/
theorem hasFPowerSeriesAt_of_eqOn_ball {p : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hrad : ENNReal.ofReal c ≤ (ofScalars ℝ p).radius)
    (heq : ∀ x ∈ Metric.ball (0 : ℝ) c, ∑' n : ℕ, p n * x ^ n = f x) :
    HasFPowerSeriesAt f (ofScalars ℝ p) 0 := by
  have h0 : 0 < (ofScalars ℝ p).radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hrad
  have H := ((ofScalars ℝ p).hasFPowerSeriesOnBall h0).hasFPowerSeriesAt
  apply H.congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with x hx
  show ofScalarsSum p x = f x
  rw [ofScalarsSum_eq_tsum_mul, heq x hx]

/-- Fixture (issue #86 acceptance): **raw ball hypotheses to coefficient
equality** — two coefficient sequences representing the same `f` on a ball,
with radius bounds, are equal. Combined with
`le_radius_ofScalars_of_summable_at` + `summable_of_tsum_ne_zero`, the radius
hypotheses themselves come from the ball equation wherever `f ≠ 0`. -/
example {p q : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hp : ENNReal.ofReal c ≤ (ofScalars ℝ p).radius)
    (hq : ENNReal.ofReal c ≤ (ofScalars ℝ q).radius)
    (heqp : ∀ x ∈ Metric.ball (0 : ℝ) c, ∑' n : ℕ, p n * x ^ n = f x)
    (heqq : ∀ x ∈ Metric.ball (0 : ℝ) c, ∑' n : ℕ, q n * x ^ n = f x) :
    p = q :=
  coeff_eq_of_hasFPowerSeriesAt (hasFPowerSeriesAt_of_eqOn_ball hc hp heqp)
    (hasFPowerSeriesAt_of_eqOn_ball hc hq heqq)

/-- Fixture (issue #86 acceptance): **a standard coefficient formula in the
benchmark's own shape** — the exponential's series with coefficients
`(n!)⁻¹`, phrased as `∑' n, p n * x ^ n`. -/
example (x : ℝ) : ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ * x ^ n = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  exact tsum_congr fun n => by rw [smul_eq_mul]

end V2

end LeanChecker.PowerSeriesKit
