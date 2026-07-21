/-
Erdős Problem #858 — §5.3 dv/v bridge, atom 2 / FINAL (Chojecki 2026).

`dv/v change-of-variables bridge`: identifies the §5.3 prime-harmonic transfer
limit `L = ∫₀¹ log(t/s)·G(s·(t/s)^x)dx` (the verified value from #97/#138) with the
paper's Lemma 5.3 form:

  `∫₀¹ log(t/s)·G(s·(t/s)^x) dx = ∫_s^t G(v)/v dv`,

via the geometric substitution `v = s·(t/s)^x` (`v : s ↦ t` as `x : 0 ↦ 1`).

Given the rpow exponent derivative (#147), and the routine continuity facts —
`ContinuousOn` of the substitution `f`, its derivative `f'`, and `G(v)/v` on the
image `f '' [0,1] = [s,t]` (taken as hypotheses; standard) — Mathlib's
`intervalIntegral.integral_comp_mul_deriv''` gives
`∫₀¹ (G(·)/· ∘ f)·f' = ∫_{f 0}^{f 1} G(v)/v`. With `f 0 = s·(t/s)^0 = s`,
`f 1 = s·(t/s)^1 = t`, and the pointwise cancellation
`(G(f x)/f x)·(f x·log(t/s)) = log(t/s)·G(f x)` (`field_simp`, `f x = s·(t/s)^x > 0`),
the two integral forms coincide.

This completes the §5.3 formalization in the paper's exact notation: the
prime-harmonic Riemann-sum theorem (capstone #141) converges to `∫_s^t G(v)/v dv`,
Lemma 5.3 as stated.

Proof: `hcov := integral_comp_mul_deriv'' hcf (fun x _ => (h147 …).hasDerivWithinAt)
hcf' hcg` (the lemma wants `HasDerivWithinAt … (Set.Ioi x)`, so `.hasDerivWithinAt`);
`simp only [Function.comp_apply]`; `rw [hf0, hf1]` (endpoints); `rw [← hcov]`;
`integral_congr` + `field_simp` (the pointwise cancellation is terminal — no `ring`).

Kernel-verified via the proofsearch MCP:
  episode 977c646d-00b9-4e2c-8181-2143dfefa4a7,
  problem_version_id 418f42a6-7ee1-44b1-86cf-3f870389fd24.
Outcome: kernel_verified / root_kernel_verified (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 972873f739ea6073c674554cb5147872009934f585f40b8fa263246b0622efeb.

**Lean lessons**: (1) `intervalIntegral.integral_comp_mul_deriv''` takes the
derivative hypothesis as `HasDerivWithinAt f (f' x) (Set.Ioi x) x` — convert a
`HasDerivAt` via `.hasDerivWithinAt`. (2) `field_simp` (with the denominator-≠0 in
context) is TERMINAL for the `(a/c)·(c·b) = b·a` cancellation — a trailing `ring`
hits "No goals".
-/
import Mathlib

namespace Erdos858

/-- §5.3 dv/v bridge atom 2 / FINAL: `∫₀¹ log(t/s)·G(s·(t/s)^x)dx = ∫_s^t G(v)/v dv`,
the geometric change of variables identifying the transfer limit with the paper's
Lemma 5.3 form. From #147 (rpow deriv) + routine continuity (hyps) via
`integral_comp_mul_deriv''`. -/
theorem erdos858_prime_transfer_dv_bridge :
    ∀ (G : ℝ → ℝ) (s t : ℝ), 0 < s → s ≤ t →
      (∀ (s' c : ℝ), 0 < c → ∀ x : ℝ, HasDerivAt (fun y : ℝ => s' * c ^ y) (s' * (c ^ x * Real.log c)) x) →
      ContinuousOn (fun x : ℝ => s * (t/s) ^ x) (Set.uIcc 0 1) →
      ContinuousOn (fun x : ℝ => s * ((t/s) ^ x * Real.log (t/s))) (Set.uIcc 0 1) →
      ContinuousOn (fun v : ℝ => G v / v) ((fun x : ℝ => s * (t/s) ^ x) '' Set.uIcc 0 1) →
      (∫ x in (0:ℝ)..1, Real.log (t/s) * G (s * (t/s) ^ x)) = ∫ v in s..t, G v / v := by
  intro G s t hs hst h147 hcf hcf' hcg
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hcov := intervalIntegral.integral_comp_mul_deriv'' hcf (fun x _ => (h147 s (t/s) hbase x).hasDerivWithinAt) hcf' hcg
  simp only [Function.comp_apply] at hcov
  have hf0 : s * (t/s) ^ (0:ℝ) = s := by rw [Real.rpow_zero, mul_one]
  have hf1 : s * (t/s) ^ (1:ℝ) = t := by rw [Real.rpow_one]; field_simp
  rw [hf0, hf1] at hcov
  rw [← hcov]
  apply intervalIntegral.integral_congr
  intro x _
  have hpos : (0:ℝ) < s * (t/s) ^ x := mul_pos hs (Real.rpow_pos_of_pos hbase x)
  have hne : s * (t/s) ^ x ≠ 0 := ne_of_gt hpos
  field_simp

end Erdos858
