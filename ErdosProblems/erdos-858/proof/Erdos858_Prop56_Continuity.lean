/-
Erdős Problem #858 — Proposition 5.6 (continuity of the prime term of Φ on the
integral-free upper interval [1/3, 1/2]).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

Proposition 5.6 asserts that the limiting prime+semiprime density Φ is continuous
and strictly decreasing on [1/4, 1/2]. On the upper sub-interval [1/3, 1/2] the
semiprime integral term I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv vanishes (the
integration interval is empty there since (1-u)/2 ≤ u), so Φ(u) reduces to its
prime term log((1-u)/u). This snapshot formalizes the continuity of that prime
term on [1/3, 1/2]: the argument (1-u)/u is strictly positive there (u ≥ 1/3 > 0
and 1-u ≥ 1/2 > 0), so Real.log composes with the continuous, nonvanishing
quotient. It is the continuity half of Prop 5.6 restricted to the integral-free
interval; the companion snapshot Erdos858_Prop56_PhiCore established strict
antitonicity and the α₂ < 1/3 placement on the same interval.

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode c116cf66-fef7-48bd-87cd-0090d0b59a48,
problem_version_id de1300cd-e0aa-4fdb-a2df-b0a7fe381fbc.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 93b9a5f9aa0eaea356e21ecfbce48570c47c5cc2e5062c1ad914381060feff31.

Lean note: ContinuousOn.log (Analysis/SpecialFunctions/Log/Basic.lean:479) reduces
to ContinuousOn of the quotient plus a log-argument nonvanishing side condition;
ContinuousOn.div₀ (Topology/Algebra/GroupWithZero.lean:234) handles the quotient,
with fun_prop discharging the numerator (1-u) and denominator u continuity and the
denominator-nonvanishing side condition (u ≠ 0 from u ≥ 1/3 > 0). The log-argument
positivity (1-u)/u > 0 comes from div_pos, and ne_of_gt turns each strict positivity
into the required ≠ 0.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6 (continuity, integral-free interval): the prime term
`log((1-u)/u)` of `Φ` is continuous on `[1/3, 1/2]`, where the semiprime integral
vanishes so `Φ(u) = log((1-u)/u)`. -/
theorem erdos858_prop56_continuity :
    ContinuousOn (fun u : ℝ => Real.log ((1 - u) / u)) (Set.Icc (1/3 : ℝ) (1/2)) := by
  have hupos : ∀ u ∈ Set.Icc (1/3 : ℝ) (1/2), 0 < u := by
    intro u hu
    have h := hu.1
    linarith
  apply ContinuousOn.log
  · apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro u hu
      exact ne_of_gt (hupos u hu)
  · intro u hu
    have h1u : (0:ℝ) < 1 - u := by
      have h := hu.2
      linarith
    exact ne_of_gt (div_pos h1u (hupos u hu))

end Erdos858
