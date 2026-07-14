/-
Erdős Problem #858 — §5.3/§5.4 foundation (Chojecki 2026, "An exact frontier
theorem and the asymptotic constant for Erdős problem #858").

Harmonic ratio asymptotic `harmonic n / log n → 1` — the normalized form of
"harmonic sum ~ log", underpinning the harmonic Riemann sums of §5.4 (toward the
asymptotic law Theorem 1.2).

From Mathlib's `Real.tendsto_harmonic_sub_log` (`harmonic n − log n → γ`, the
Euler–Mascheroni constant), writing `harmonic n / log n = (harmonic n − log n)/log n
+ 1`: the first term is a convergent numerator over `log n → ∞`, hence `→ 0`, so the
ratio `→ 1`. Elementary, no PNT.

Proof: `Tendsto.div_atTop` (`(harmonic n − log n)/log n → 0`, from the `→ γ`
numerator and `log n → ∞`) `+ .add_const 1`, transported by `Tendsto.congr'` +
`filter_upwards [eventually_ge_atTop 2]` (where `log n ≠ 0`) with `field_simp; ring`.

Kernel-verified via the proofsearch MCP:
  episode f9edfc23-e956-4bac-8095-1d9df66118e1,
  problem_version_id aeaa6da5-a618-4249-b29b-8e9af51c97c5.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a95a2b9a17ff006fe9ac7eec6535c7ace88ab7270133e18e768c35d35a640797.
-/
import Mathlib

namespace Erdos858

/-- `harmonic n / log n → 1`: the harmonic sum is asymptotic to `log n`. The
normalized asymptotic underpinning the §5.4 harmonic Riemann sums (toward Theorem
1.2). Proved from `Real.tendsto_harmonic_sub_log` (`harmonic n − log n → γ`). -/
theorem erdos858_harmonic_ratio_limit :
    Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log (n : ℝ)) Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have key := (Real.tendsto_harmonic_sub_log.div_atTop hlog).add_const 1
  simp only [zero_add] at key
  refine key.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlogne : Real.log (n:ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp
  ring

end Erdos858
