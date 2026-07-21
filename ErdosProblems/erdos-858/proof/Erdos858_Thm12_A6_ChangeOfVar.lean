/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 affine change of variables (Chojecki 2026).

`affine pullback of the interval integral`: for the linear substitution
`v = (t−s)·x + s`,

  `(t−s)·∫₀¹ f((t−s)·x + s) dx = ∫_s^t f(v) dv`.

This identifies the interval log-harmonic transfer's limit `L = ∫₀¹ g`
(`g(x) = f(s+x(t−s))·(t−s)`) with the paper's Lemma 5.4 integral `∫_s^t f` — for
`f = 1−Φ`, `s = α₂`, `t = 1/2`, `L = ∫_{α₂}^{1/2}(1−Φ) = I`, the density integral of
`c₂`.

Proof: `intervalIntegral.mul_integral_comp_mul_add` at `c = t−s`, `d = s`, then the
endpoints `(t−s)·0+s = s`, `(t−s)·1+s = t` (`mul_zero`, `zero_add`, `mul_one`,
`sub_add_cancel`).

Kernel-verified via the proofsearch MCP:
  episode 5a305c49-55a4-4419-b160-810f1fd920f0,
  problem_version_id 4743658e-61de-4d12-8800-7bcf8638a2b5.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 64e4ca835355cb660fe20eae88a8f29c9226184625e309018556336218ca3097.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 affine change of variables: `(t−s)·∫₀¹ f((t−s)x+s) = ∫_s^t f` —
identifies the transfer limit `L = ∫₀¹ g` with the paper's `∫_s^t f`.
`intervalIntegral.mul_integral_comp_mul_add` + endpoint simp. -/
theorem erdos858_thm12_a6_change_of_var :
    ∀ (f : ℝ → ℝ) (s t : ℝ), (t - s) * (∫ x in (0:ℝ)..1, f ((t - s) * x + s)) = ∫ v in s..t, f v := by
  intro f s t
  have h := intervalIntegral.mul_integral_comp_mul_add (a := 0) (b := 1) (f := f) (c := t - s) (d := s)
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h
  exact h

end Erdos858
