/-
Erdős Problem #858 — Proposition 5.6 / §5 (Chojecki 2026, "An exact frontier
theorem and the asymptotic constant for Erdős problem #858").

Density prime-term NONNEGATIVITY atom — the ingredient bounding the c₂ integrand
from above.

The limiting prime+semiprime density is Φ(u) = Φ_prime(u) + I(u) with prime term
  Φ_prime(u) = log((1-u)/u),
and on [1/3, 1/2] the semiprime contribution I(u) vanishes so Φ(u) = Φ_prime(u).
For 0 < u ≤ 1/2 we have 1-u ≥ u > 0, hence (1-u)/u ≥ 1 and therefore
  Φ_prime(u) = log((1-u)/u) ≥ 0.
This nonnegativity (up to the vanishing point u = 1/2, where Φ_prime(1/2)=log 1=0)
is exactly what bounds the c₂ integrand: 1 - Φ(u) ≤ 1 on [α₂, 1/2], used in
  c₂ = 1/2 + ∫_{α₂}^{1/2} (1 - Φ(u)) du.
The Meissel–Mertens constant cancels in the interval form, so this needs no
PNT / Mertens — pure real analysis on the explicit elementary prime term.

Proof: `Real.log_nonneg` reduces the goal to `1 ≤ (1-u)/u`; `one_le_div hu`
rewrites this to `u ≤ 1-u`, closed by `linarith` from `u ≤ 1/2`.

Kernel-verified via the proofsearch MCP:
  episode 77cb0493-47b8-4428-925e-d928cb646193,
  problem_version_id db1b5b62-8f04-4569-8b9a-808ad104c0a8.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bea378128d668d91ad587238508d8a46e88b3eb898e27f9d876b089ce4ba892c.
-/
import Mathlib

namespace Erdos858

/-- §5 density prime-term nonnegativity atom: the prime term of the limiting
density, `Φ_prime(u) = log((1-u)/u)`, is nonnegative on `(0, 1/2]` (since
`(1-u)/u ≥ 1` there). This bounds the c₂ integrand `1 - Φ(u) ≤ 1` on `[α₂, 1/2]`
inside `c₂ = 1/2 + ∫_{α₂}^{1/2} (1 - Φ(u)) du`. Pure real analysis, no PNT. -/
theorem erdos858_phi_prime_nonneg :
    ∀ u : ℝ, 0 < u → u ≤ 1 / 2 → 0 ≤ Real.log ((1 - u) / u) := by
  intro u hu hu2
  apply Real.log_nonneg
  rw [one_le_div hu]
  linarith

end Erdos858
