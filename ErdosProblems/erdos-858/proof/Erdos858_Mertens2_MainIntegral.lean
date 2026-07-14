/-
Erdős Problem #858 — §5, toward the sharp asymptotic constant c₂: the Mertens-2
MAIN integral, evaluated in closed form via the fundamental theorem of calculus.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 exact-constant development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP pipeline.
  problem_version_id  48d2495c-f1df-4fb8-b353-4fe53575d76a
  episode_id          94a0f7f5-dcb1-4810-afd0-b7fa7efcd0ba
  root_statement_hash e871619be0161189ae498e0642088168e34a3a748e4ffcb7b771372e77141f82
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

────────────────────────────────────────────────────────────────────────────────
CONTENT.  This is the J term of the Abel/partial-summation reduction of Mertens'
second theorem (`erdos858_mertens2_abel_reduction`, hypothesis `hJval`).  In that
reduction the prime-reciprocal sum is split as
    Σ_{p≤x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t log²t) dt,
and after writing A(t) = log t + r(t) the main piece of the integral is exactly
    J := ∫₂ˣ 1/(t log t) dt = loglog x − loglog 2,
the double-log growth that carries Mertens' second theorem.

The antiderivative of the integrand `1/(t·log t)` is `F(t) = log(log t)`, since by
the chain rule
    d/dt log(log t) = (1/log t)·(1/t) = 1/(t·log t).
On `[2, x]` we have `t ≥ 2 > 1`, so `log t > 0`, hence `log t ≠ 0` and `t ≠ 0`;
both chain-rule log derivatives are well-defined and the integrand is continuous.
The fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) then gives, for `x ≥ 2`,
    ∫₂ˣ 1/(t·log t) dt = log(log x) − log(log 2).

────────────────────────────────────────────────────────────────────────────────
TECHNIQUE.  Mirrors the campaign-sibling FTC template `erdos647_mertens_mainterm`
(Erdős #647, main-term antiderivative).  Only the integrand and antiderivative
differ:
  • `hmain`  — `HasDerivAt (fun s => log (log s)) (1/(t·log t)) t` built from
    `(Real.hasDerivAt_log hlogtne).comp t (Real.hasDerivAt_log htne)`, whose value
    `(log t)⁻¹ * t⁻¹` is reconciled to `1/(t·log t)` by `rw [one_div, mul_inv]; ring`
    (deterministic, avoiding `field_simp`'s close-or-leave ambiguity);
  • `hcont`  — `ContinuousOn.div` with a constant numerator (`continuousOn_const`),
    denominator `continuousOn_id.mul (Real.continuousOn_log.mono hsubset)`, and
    nonvanishing via `mul_ne_zero`;
  • `hint`   — `hcont.intervalIntegrable`;
  • conclude by `rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]`,
    which closes by `rfl` since the RHS is already `log (log x) − log (log 2)`.

Lean notes (this pin): the commutative inverse split is `mul_inv`
(`(a*b)⁻¹ = a⁻¹ * b⁻¹`, Algebra/Group/Basic.lean:513) and `one_div`
(`1/a = a⁻¹`, Algebra/Group/Defs.lean:1090); `Real.continuousOn_log` has domain
`{0}ᶜ`, which `.mono` accepts against `{t | t ≠ 0}`.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens' second theorem — the MAIN integral (J term of the Abel
reduction).  For all real `x ≥ 2`, the fundamental theorem of calculus with
antiderivative `F(t) = log (log t)` gives
`∫₂ˣ 1/(t·log t) dt = log (log x) − log (log 2)`, the double-log growth of
`Σ_{p≤x} 1/p`. -/
theorem erdos858_mertens2_main_integral :
    ∀ x : ℝ, 2 ≤ x →
      (∫ t in (2:ℝ)..x, 1 / (t * Real.log t))
        = Real.log (Real.log x) - Real.log (Real.log 2) := by
  intro x hx
  have hsubset : Set.Icc (2:ℝ) x ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hmain : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun s => Real.log (Real.log s))
        (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
    have hloglog : HasDerivAt (fun s => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
      (Real.hasDerivAt_log hlogtne).comp t hlog
    have hval : (Real.log t)⁻¹ * t⁻¹ = 1 / (t * Real.log t) := by
      rw [one_div, mul_inv]; ring
    rw [hval] at hloglog
    exact hloglog
  have hcont : ContinuousOn (fun t => 1 / (t * Real.log t)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id.mul (Real.continuousOn_log.mono hsubset)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero htne hlogtne
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t)) MeasureTheory.volume 2 x :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]

end Erdos858
