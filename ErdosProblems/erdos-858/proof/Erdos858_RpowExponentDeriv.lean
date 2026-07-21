/-
Erdős Problem #858 — §5.3 dv/v bridge, atom 1 (Chojecki 2026).

`constant-base rpow exponent derivative`: for `c > 0`,

  `d/dx (s·c^x) = s·(c^x·log c)`.

This is the derivative underlying the geometric change of variables `v = s·(t/s)^x`
(with `c = t/s`), used to identify the §5.3 prime-harmonic transfer limit
`L = ∫₀¹ log(t/s)·G(s·(t/s)^x)dx` with the paper's `∫_s^t G(v)/v dv`.

Proof: `c^x = exp(log c · x)` (`Real.rpow_def_of_pos`), whose derivative is
`exp(log c · x)·log c = c^x·log c` (`HasDerivAt.exp` on the linear inner map
`y ↦ log c · y`, whose derivative is `log c`); then scale by `s`
(`HasDerivAt.const_mul`).

Kernel-verified via the proofsearch MCP:
  episode d4e4bf1f-7154-4385-a6aa-24d19d0923e5,
  problem_version_id 893b7bcf-40cd-424a-a798-56b93705258b.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1d2aa503dffe45fdd600eae22436c1d72dcdc2ec6f628112ca12d0edf22ec853.
-/
import Mathlib

namespace Erdos858

/-- §5.3 dv/v bridge atom 1 (rpow exponent derivative): for `c > 0`,
`HasDerivAt (fun y => s·c^y) (s·(c^x·log c)) x`. The derivative of the geometric
substitution. Proof via `c^y = exp(log c · y)` + `HasDerivAt.exp` + `const_mul`. -/
theorem erdos858_rpow_exponent_deriv :
    ∀ (s c : ℝ), 0 < c → ∀ x : ℝ, HasDerivAt (fun y : ℝ => s * c ^ y) (s * (c ^ x * Real.log c)) x := by
  intro s c hc x
  have h1 : HasDerivAt (fun y : ℝ => Real.log c * y) (Real.log c) x := by simpa using (hasDerivAt_id x).const_mul (Real.log c)
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (Real.log c * y)) (Real.exp (Real.log c * x) * Real.log c) x := by simpa using h1.exp
  have hfun : (fun y : ℝ => c ^ y) = (fun y : ℝ => Real.exp (Real.log c * y)) := by funext y; rw [Real.rpow_def_of_pos hc]
  have hbase : HasDerivAt (fun y : ℝ => c ^ y) (c ^ x * Real.log c) x := by rw [hfun, show c ^ x = Real.exp (Real.log c * x) from Real.rpow_def_of_pos hc x]; exact h2
  exact hbase.const_mul s

end Erdos858
