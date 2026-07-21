/-
Erdős Problem #858 — §5.3 dv/v bridge, atom 3 (Chojecki 2026).

`constant-base rpow exponent continuity`: for `c > 0`, `x ↦ s·c^x` is continuous.
Companion to #147 (its derivative); the reusable continuity of the geometric
substitution `v = s·(t/s)^x`, used to discharge the continuity side-conditions of
the §5.3 dv/v change-of-variables bridge (making it self-contained).

Proof: `c^x = exp(log c · x)` (`Real.rpow_def_of_pos`), a composition of continuous
maps (`Real.continuous_exp.comp (continuous_const.mul continuous_id)`, scaled by
`continuous_const.mul`).

Kernel-verified via the proofsearch MCP:
  episode ba4680ed-e0d1-4239-9a48-3344ec8bce66,
  problem_version_id b5b348a7-cd90-47a0-8a4a-7570bcd69afd.
Outcome: kernel_verified / root_kernel_verified (2nd submission; `Continuous.exp`
is absent in this pin — use `Real.continuous_exp.comp`).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 964f883d5551e230ea445af9b981803576fdd6a9306a6b456cae4299872199e4.

**Lean lesson**: `Continuous.exp` (dot form) does not exist in this pin — compose
via `Real.continuous_exp.comp hf`; the `Real.exp ∘ f` output is defeq to
`fun x => Real.exp (f x)`, so `exact` accepts it against the lambda goal.
-/
import Mathlib

namespace Erdos858

/-- §5.3 dv/v bridge atom 3 (rpow exponent continuity): for `c > 0`,
`Continuous (fun x => s·c^x)`. Companion to #147. Via `c^x = exp(log c · x)`. -/
theorem erdos858_rpow_exponent_continuous :
    ∀ (s c : ℝ), 0 < c → Continuous (fun x : ℝ => s * c ^ x) := by
  intro s c hc
  have hfun : (fun x : ℝ => s * c ^ x) = (fun x : ℝ => s * Real.exp (Real.log c * x)) := by funext x; rw [Real.rpow_def_of_pos hc]
  rw [hfun]
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))

end Erdos858
