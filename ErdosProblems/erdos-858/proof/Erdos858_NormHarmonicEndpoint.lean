/-
Erdős Problem #858 — §5.4 log-harmonic transfer, rung 1 (Chojecki 2026).

`normalized harmonic endpoint`: the log-scale block mass. For `x > 0`,
  `harmonic(⌊N^x⌋) / log N  →  x`   as `N → ∞`,
i.e. `(1/log N) Σ_{a ≤ ⌊N^x⌋} 1/a → x`. This is the harmonic (log-scale) analogue
of the equispaced count `(1/K)·j → j/K` used in the durable Riemann-sum theorem
(#97); it is the first rung of the log-harmonic transfer that carries the analytic
weight of the sum onto the interval integral (toward the asymptotic law Theorem 1.2,
routed through §6 eventual frontier exactness).

Conditional on the floor block-endpoint limit `log⌊N^x⌋/log N → x` (kernel-verified
#91, taken as hypothesis since problem_versions cannot cross-reference). Proof:
`harmonic(⌊N^x⌋)/log N = log⌊N^x⌋/log N + (harmonic(⌊N^x⌋) − log⌊N^x⌋)/log N`; the
first term → x (hypothesis), the second → 0 because `harmonic(m) − log m → γ`
(Euler–Mascheroni, `Real.tendsto_harmonic_sub_log`, composed with `⌊N^x⌋ → ∞` via
`tendsto_nat_floor_atTop`) is bounded while `log N → ∞` (`Tendsto.div_atTop`).
Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode eb1457ce-b9c0-41ca-87bd-2b670cad97d5,
  problem_version_id 016d526f-59f0-4bec-8c8c-dd5bff9a23f4.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ade71283ccd2aedcc1a9db7f71f13d395f034ed01a62f0a8398ccf5e6370720d.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer rung 1 (normalized harmonic endpoint / log-scale block
mass): for `x > 0`, given `log⌊N^x⌋/log N → x` (#91), `harmonic(⌊N^x⌋)/log N → x`.
The harmonic analogue of the equispaced count in the durable Riemann-sum theorem
(#97). Proof: split off the bounded `harmonic − log → γ` correction (`/log N → 0`).
Toward the asymptotic law Theorem 1.2. -/
theorem erdos858_norm_harmonic_endpoint :
    ∀ x : ℝ, 0 < x →
      Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x) →
      Filter.Tendsto (fun N : ℕ => (harmonic (⌊(N:ℝ)^x⌋₊) : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds x) := by
  intro x hx hlog_endpoint
  have hNx : Filter.Tendsto (fun N:ℕ => (N:ℝ)^x) Filter.atTop Filter.atTop := (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  have hfloor : Filter.Tendsto (fun N:ℕ => ⌊(N:ℝ)^x⌋₊) Filter.atTop Filter.atTop := tendsto_nat_floor_atTop.comp hNx
  have hlogN : Filter.Tendsto (fun N:ℕ => Real.log (N:ℝ)) Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcorr : Filter.Tendsto (fun N:ℕ => ((harmonic (⌊(N:ℝ)^x⌋₊) : ℝ) - Real.log (⌊(N:ℝ)^x⌋₊))) Filter.atTop (nhds Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log.comp hfloor
  have hcorr0 : Filter.Tendsto (fun N:ℕ => ((harmonic (⌊(N:ℝ)^x⌋₊) : ℝ) - Real.log (⌊(N:ℝ)^x⌋₊))/Real.log (N:ℝ)) Filter.atTop (nhds 0) := hcorr.div_atTop hlogN
  have hsum := hlog_endpoint.add hcorr0
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  ring

end Erdos858
