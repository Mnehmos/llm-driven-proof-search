import Mathlib

/-!
# Inequality & estimate kit (issue #91)

Reusable contest-style inequality bridges: the square/AM-GM/Cauchy-Schwarz
shapes that `nlinarith` and `positivity` cannot discover on their own,
packaged so a proof reduces to one lemma application plus arithmetic.

## Epistemic status

Kernel-verified only. No empirical or asymptotic-heuristic claims — every
bound here is a Lean theorem over `ℝ` (or an ordered ring).

## When to use what (route guidance)

- `nlinarith [sq_nonneg …, mul_pos …]` — polynomial inequalities once the
  right square/product hints are supplied. Fine for `2ab ≤ a²+b²`-shaped
  goals; the kit's `two_mul_le_add_sq` is exactly that hint packaged.
- `positivity` — pure positivity/nonnegativity of an expression built from
  positive atoms. Denominator cleanup before `nlinarith`.
- **This kit** — when the estimate needs a *named* inequality `nlinarith`
  cannot synthesize: square roots (AM-GM via `sqrt`), fractional powers
  (weighted AM-GM), or a Cauchy-Schwarz/power-mean sum bound. `nlinarith`
  has no access to `Real.sqrt` or `rpow` facts, so `sqrt_mul_le_add_div_two`
  and `geom_mean3` are genuinely out of its reach.

## Target problem families

AM-GM / Cauchy extremal problems, sum-of-squares bounds, `x + 1/x ≥ 2`-style
normalizations, power-mean comparisons, and any Putnam/Erdős estimate that
reduces to a standard named inequality. Complements `PowerSeriesKit`
(analytic), `ArithmeticKit` (discrete), and `RecurrenceGeneratingFunctionKit`.
-/

namespace LeanChecker.InequalityEstimateKit

open Finset

/-- **Square bridge**: `2ab ≤ a² + b²` over a linearly ordered ring — the
canonical `sq_nonneg (a − b)` fact, packaged so callers need not rediscover
the hint. -/
theorem two_mul_le_add_sq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **AM-GM (two variables, `sqrt` form)**: `√(a·b) ≤ (a + b)/2` for
nonnegative reals. Genuinely beyond `nlinarith`, which cannot reason about
`Real.sqrt`. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  calc Real.sqrt (a * b)
      ≤ Real.sqrt (((a + b) / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])
    _ = (a + b) / 2 := Real.sqrt_sq (by linarith)

/-- **Cauchy-Schwarz (finite sums)**: `(∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)`. Re-export
of `Finset.sum_mul_sq_le_sq_mul_sq` under a contest-facing name. -/
theorem cauchy_schwarz {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **Power-mean / QM-AM bridge**: `(∑ fᵢ)² ≤ n · ∑ fᵢ²`, the Cauchy-Schwarz
corollary with `gᵢ = 1` — the workhorse for "sum squared vs sum of squares"
estimates. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := cauchy_schwarz s f (fun _ => 1)
  simpa [mul_comm] using h

/-- **AM-GM (three variables, cube-root form)**: `(a·b·c)^{1/3} ≤ (a+b+c)/3`
for nonnegative reals, via Mathlib's weighted geometric-mean inequality with
equal weights. Categorically beyond `nlinarith`/`polyrith` — fractional
powers are outside polynomial arithmetic. -/
theorem geom_mean3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a * b * c) ^ ((1 : ℝ) / 3) ≤ (a + b + c) / 3 := by
  have key := Real.geom_mean_le_arith_mean3_weighted
    (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (0:ℝ) ≤ 1/3)
    ha hb hc (by norm_num)
  calc (a * b * c) ^ ((1 : ℝ) / 3)
      = a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ ((1 : ℝ) / 3) := by
        rw [Real.mul_rpow (mul_nonneg ha hb) hc, Real.mul_rpow ha hb]
    _ ≤ 1 / 3 * a + 1 / 3 * b + 1 / 3 * c := key
    _ = (a + b + c) / 3 := by ring

/-! ## Fixtures -/

/-- Fixture (issue #91 acceptance — beyond `nlinarith`): the classic
`x + 1/x ≥ 2` for `x > 0`, via the `sqrt` AM-GM bridge. `nlinarith` cannot
supply the `√(x · 1/x) = 1` step. -/
example {x : ℝ} (hx : 0 < x) : 2 ≤ x + 1 / x := by
  have h := sqrt_mul_le_add_div_two hx.le (by positivity : (0 : ℝ) ≤ 1 / x)
  rw [mul_one_div, div_self hx.ne', Real.sqrt_one] at h
  linarith

/-- Fixture (Cauchy-Schwarz application): `(a + b + c)² ≤ 3(a² + b² + c²)`,
closed by the power-mean bridge rather than a hand-tuned `nlinarith` hint
set. -/
example (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin 3)) ![a, b, c]
  simpa [Fin.sum_univ_three] using h

/-- Fixture (three-variable AM-GM in action): the cube-root mean of three
nonnegative reals is at most their arithmetic mean — the flagship estimate
`nlinarith` cannot touch. -/
example : ((8 : ℝ) * 1 * 27) ^ ((1 : ℝ) / 3) ≤ (8 + 1 + 27) / 3 :=
  geom_mean3 (by norm_num) (by norm_num) (by norm_num)

end LeanChecker.InequalityEstimateKit
