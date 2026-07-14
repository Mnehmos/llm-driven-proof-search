/-
Erdős Problem #858 — §5 sharp-constant localization: the c₂ window 1/2 ≤ c₂ < 3/4.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 985d73f8-4df9-4a1b-8f12-80d13c483800,
problem_version_id b72d1316-2ace-47db-856a-05a45a17f86f.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4526fcde…

The right-endpoint helper `erdos858_phi_half_prime_term` below was kernel-verified
as its own root theorem: episode 6887822c-8031-449b-b0a9-ac60ba83f7d7,
problem_version_id b78566dd-28c4-4ebd-9b88-f26e0fe2839b,
root_statement_hash 186d4b2c… (same toolchain, outcome kernel_verified).

The paper defines the sharp constant as
    c₂ = 1/2 + J,   J = ∫_{α₂}^{1/2} (1 - Φ(u)) du,
where α₂ ∈ (1/4, 1/3) is the unique root of Φ = 1 (Proposition 5.6, whose
existence + uniqueness is separately kernel-verified). Here
Φ(u) = log((1-u)/u) + I(u). On [α₂, 1/2] the integrand satisfies
0 ≤ 1 - Φ(u) ≤ 1 (Φ decreases from Φ(α₂) = 1 to Φ(1/2) = 0 — see the companion
Erdos858_C2Window helper log((1-1/2)/(1/2)) = 0), and the interval has length
1/2 - α₂ < 1/2 - 1/4 = 1/4. Hence the analytic integral bounds
    0 ≤ J ≤ 1/2 - α₂.

This atom is the purely linear glue step that turns those integral bounds into
the two-sided localization of c₂. Conditional on (i) α₂ ∈ (1/4, 1/2) and
(ii) 0 ≤ J ≤ 1/2 - α₂, it proves
    1/2 ≤ 1/2 + J   and   1/2 + J < 3/4,
i.e. 1/2 ≤ c₂ < 3/4 (a fortiori 1/2 ≤ c₂ < 1). The lower bound uses only
0 ≤ J; the upper bound uses J ≤ 1/2 - α₂ together with 1/4 < α₂ (which forces
J < 1/4). Numerically c₂ = 0.6187712…, comfortably inside this window.

Lean note: `intro` the four hypotheses, then each conjunct closes by `linarith`.
No monotonicity, continuity, or integral lemma leaks into this step — the
analytic content is fully quarantined in the hypotheses 0 ≤ J ≤ 1/2 - α₂.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, §5: the c₂ window. Given the endpoint constraint `α₂ ∈ (1/4,1/2)`
and the integral bounds `0 ≤ J ≤ 1/2 - α₂` on `J = ∫_{α₂}^{1/2}(1 - Φ)`, the
sharp constant `c₂ = 1/2 + J` satisfies `1/2 ≤ c₂ < 3/4`. -/
theorem erdos858_c2_window :
    ∀ (α₂ J : ℝ), 1 / 4 < α₂ → α₂ < 1 / 2 → 0 ≤ J → J ≤ 1 / 2 - α₂ →
      (1 : ℝ) / 2 ≤ 1 / 2 + J ∧ 1 / 2 + J < 3 / 4 := by
  intro α₂ J h1 h2 h3 h4
  exact ⟨by linarith, by linarith⟩

/-- Right-endpoint helper used above: the prime term of `Φ` at `u = 1/2` is zero,
`log((1 - 1/2)/(1/2)) = log 1 = 0`, so `Φ(1/2) = 0` (the semiprime term `I(1/2)`
also vanishes). This pins the upper end `1 - Φ(1/2) = 1` of the integrand bound. -/
theorem erdos858_phi_half_prime_term :
    Real.log ((1 - 1 / 2) / (1 / 2)) = 0 := by
  rw [show (1 - 1 / 2) / (1 / 2) = (1 : ℝ) by norm_num, Real.log_one]

end Erdos858
