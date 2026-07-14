/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

Per-prime GEOMETRIC-TAIL bound (option (c), per-base step) for the non-prime von
Mangoldt correction

    Σ_{d ≤ N, d not prime} Λ(d)/d  =  Σ_{p^k ≤ N, k≥2} (log p)/p^k .

Fixing a base p ≥ 2 and summing its proper-prime-power (k ≥ 2) contributions, the
finite exponent sum (over any cutoff M) is dominated by the closed geometric tail:

    Σ_{k=2}^{M-1} (log p)/p^k
      ≤  (log p) · Σ_{k≥2} p^{-k}
      =  (log p) · p^{-2}/(1 - p^{-1})
      =  (log p)/(p(p-1)),                                   uniformly in M.

Summing this per-prime bound over primes p gives the constant of the Mertens-1
correction, Σ_p (log p)/(p(p-1)) ≈ 0.7554 — the `T` of the `0 ≤ T ≤ 1` tail
hypothesis discharged by the prime Mertens-1 lower assembly (campaign atoms
#51/#52). This atom supplies the per-base finite→geometric domination that the
campaign previously flagged only as "reachable (tsum_geometric_of_lt_one)";
here it is converted into a kernel-verified fact via the turnkey finite bound
`geom_sum_Ico_le_of_lt_one`.

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : a9dcbb0b-4062-41b4-9149-47da2527be72
  episode_id         : 57d5027f-b969-4059-ad89-26ffc5a73044
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 2
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 886170e842f9efde4be1003aee1d614283a2039d7bb39204dcefa37dcd4623c8

Proof sketch.
  (1) Factor the nonnegative `Real.log p` out of the sum: `Finset.mul_sum` plus a
      termwise rewrite `log p / p^k = log p * (p⁻¹)^k` (`inv_pow`,
      `div_eq_mul_inv`).
  (2) Bound the pure exponent sum by the closed geometric tail with
      `geom_sum_Ico_le_of_lt_one` (0 ≤ p⁻¹, p⁻¹ < 1):
          Σ_{k∈Ico 2 M} (p⁻¹)^k ≤ (p⁻¹)^2 / (1 - p⁻¹).
  (3) Scale by `log p ≥ 0` (`mul_le_mul_of_nonneg_left`) and simplify the closed
      form `(p⁻¹)^2 / (1 - p⁻¹) = 1/(p(p-1))` (`field_simp`), then `mul_one_div`.

Key Mathlib lemma (turnkey finite geometric tail):
  `geom_sum_Ico_le_of_lt_one (hx : 0 ≤ x) (h'x : x < 1) :`
  `    ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x)`
  (Mathlib/Algebra/Order/Field/GeomSum.lean).

Note on the sharp upper bound `T ≤ 1` (NOT proved here — the genuine wall).
  Summing this per-prime bound reduces `T ≤ 1` to the TERMINAL numeric estimate
      Σ_{p prime} (log p)/(p(p-1))  ≤  1        (true value ≈ 0.7554),
  or, dropping the prime restriction, the over-estimate
      Σ_{n ≥ 2} (log n)/(n(n-1))               (≈ 1.2578, so > 1: prime
  restriction is essential for `≤ 1`, but this over-estimate does certify `≤ 2`).
  Either way an EXPLICIT numeric bound is needed. Because `Real.log` sits in the
  numerator, no closed-form ζ-value route works: this pin has `riemannZeta_two`
  (ζ(2)=π²/6) and p-series summability (`summable_one_div_nat_rpow`) but no term
  `(log n)/n^s` can be dominated by `c/n²` (log is unbounded), and dominating by
  `c/n^{3/2}` lands on ζ(3/2), for which the pin has no numeric value. The only
  reachable route to a numeric constant is the INTEGRAL TEST
  (`AntitoneOn.sum_le_integral`, Mathlib/Analysis/SumIntegralComparisons.lean)
  applied to the antitone tail of `log x / x²` (antiderivative `-(log x+1)/x`),
  combined with the vonMangoldt→(p,k) reindex (`sum_PrimePow_eq_sum_sum`) — a
  separate multi-atom effort, not a single-episode result.
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

/-- Per-prime geometric-tail bound: for a fixed base `p ≥ 2` and any exponent
cutoff `M`, the finite proper-prime-power (`k ≥ 2`) exponent sum
`Σ_{k∈Ico 2 M} (log p)/p^k` is dominated, uniformly in `M`, by the closed
geometric tail `(log p)/(p(p-1))`. This is the per-base input to the non-prime
von Mangoldt Mertens correction `Σ_{d≤N, ¬prime} Λ(d)/d`. -/
theorem erdos858_mertens1_prime_power_geometric_tail (p : ℕ) (hp : 2 ≤ p) (M : ℕ) :
    ∑ k ∈ Finset.Ico 2 M, Real.log (p : ℝ) / (p : ℝ) ^ k
      ≤ Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpm1' : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm1
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := by
    have h1 : (1 : ℝ) < (p : ℝ) := by linarith
    have h2 := (div_lt_one hp0).mpr h1
    simpa [one_div] using h2
  have hden : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
    exact ne_of_gt hpos
  have key : ∑ k ∈ Finset.Ico 2 M, Real.log (p : ℝ) / (p : ℝ) ^ k
      = Real.log (p : ℝ) * ∑ k ∈ Finset.Ico 2 M, ((p : ℝ)⁻¹) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [inv_pow, div_eq_mul_inv]
  have hgeom : ∑ k ∈ Finset.Ico 2 M, ((p : ℝ)⁻¹) ^ k
      ≤ ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) :=
    geom_sum_Ico_le_of_lt_one hx0 hx1
  have hval : ((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp
  rw [key]
  have hbound : Real.log (p : ℝ) * ∑ k ∈ Finset.Ico 2 M, ((p : ℝ)⁻¹) ^ k
      ≤ Real.log (p : ℝ) * (((p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹)) :=
    mul_le_mul_of_nonneg_left hgeom hlog
  rw [hval, mul_one_div] at hbound
  exact hbound

end Erdos858
