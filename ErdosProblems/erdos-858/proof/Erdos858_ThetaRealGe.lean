/-
Erdős Problem #858 — §5 analytic foundation: real-valued Chebyshev ϑ lower bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens bounds.)

Ported byte-faithfully from the kernel-verified Erdős #647 artifact
`erdos647_theta_real_ge` (ErdosProblems/erdos-647/proof/Erdos647_ThetaRealGe.lean).
The statement and proof term are identical; this is an independent re-verification
under a new #858 problem registration. The identical root_statement_hash below
confirms the statement is byte-identical to the #647 original.

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode 040cf08c-4190-45d7-8dc0-4f5f8b8697c6,
problem_version_id baa73c15-f4de-4148-bec9-c6009fee1996.
Outcome: kernel_verified / root_kernel_verified (root_proved).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 72cb80ab472e749d02f2ec9507b84f08254d17a1a8d971e0f5ee69028e709531.

Content: bridges Mathlib's `Chebyshev.theta_ge` — which is stated only at
natural-number points `n` (`(n:ℝ)*log2 - log(n+1) - 2√n·log n ≤ θ(n)`) — to a
bound valid for **all real** `t ≥ 2`, the exact form the θ-substitution in #858's
quantitative-Mertens identities needs:

  ∀ t ≥ 2, (t−1)·log 2 − log(t+2) − 2√t·log t ≤ θ(t).

Proof: let `n = ⌊t⌋`. `θ` is monotone (`Chebyshev.theta_mono`), so
`θ(n) ≤ θ(t)`; apply `theta_ge` at `n`; then dominate termwise using
`n ≤ t < n+1`: `(t−1)log2 ≤ n·log2`, `log(n+1) ≤ log(t+2)` (so the negated
terms compare the other way), and `√n·log n ≤ √t·log t` by monotonicity of
both factors (`mul_le_mul`). This closes the gap between Mathlib's
integer-indexed effective Chebyshev bound and the real-integral form the §5
Mertens estimates consume.
-/
import Mathlib

namespace Erdos858

theorem erdos858_theta_real_ge :
    ∀ t : ℝ, 2 ≤ t → (t - 1) * Real.log 2 - Real.log (t + 2) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
  intro t ht
  set n := ⌊t⌋₊ with hn_def
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hn2 : 2 ≤ n := by
    have h2n : ((2:ℕ):ℝ) ≤ t := by exact_mod_cast ht
    exact_mod_cast Nat.le_floor h2n
  have hnt : (n:ℝ) ≤ t := Nat.floor_le ht0
  have htn1 : t < (n:ℝ) + 1 := Nat.lt_floor_add_one t
  have hthle : Chebyshev.theta (n:ℝ) ≤ Chebyshev.theta t := Chebyshev.theta_mono hnt
  have hnge := Chebyshev.theta_ge n
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm1 : (t-1)*Real.log 2 ≤ (n:ℝ)*Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog2pos)
    linarith [htn1]
  have hterm2 : -Real.log (t+2) ≤ -Real.log ((n:ℝ)+1) := by
    have hle : Real.log ((n:ℝ)+1) ≤ Real.log (t+2) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have hterm3 : -2*Real.sqrt t*Real.log t ≤ -2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
    have hsqrt_mono : Real.sqrt (n:ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hnt
    have hlog_mono : Real.log (n:ℝ) ≤ Real.log t := Real.log_le_log hnpos hnt
    have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith [hn2, hnpos])
    have hsqt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hmul : Real.sqrt (n:ℝ) * Real.log (n:ℝ) ≤ Real.sqrt t * Real.log t := mul_le_mul hsqrt_mono hlog_mono hln hsqt
    nlinarith [hmul]
  calc (t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t
      ≤ (n:ℝ)*Real.log 2 - Real.log ((n:ℝ)+1) - 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by linarith [hterm1, hterm2, hterm3]
    _ ≤ Chebyshev.theta (n:ℝ) := hnge
    _ ≤ Chebyshev.theta t := hthle

end Erdos858
