/-
Erdős Problem #858 — §5.3 o(1)-Mertens arc, atom 11 (Chojecki 2026).

`loglog floor-endpoint limit`: for `x > 0`, given `log⌊N^x⌋/log N → x` (#91's
conclusion, hypothesis),

  `loglog⌊N^x⌋ − loglog N  →  log x`.

Proof: apply `Real.log`-continuity to the ratio limit (`Filter.Tendsto.log` at
`x ≠ 0`), then rewrite `log(log⌊N^x⌋/log N) = loglog⌊N^x⌋ − loglog N`
eventually (both logs eventually positive: `N ≥ 2`, and `⌊N^x⌋ ≥ 2` eventually
from the rpow/floor atTop chain), transporting along `Tendsto.congr'`.

Subtracting two instances (at `t` and `s`) cancels `loglog N`:
`loglog⌊N^t⌋ − loglog⌊N^s⌋ → log t − log s` — the main-term limit of the
interval-Mertens assembly, i.e. the value of the §5.3 prime block masses.

Kernel-verified via the proofsearch MCP:
  episode ec737afb-5236-4f9e-9b80-2bca2d64d519,
  problem_version_id 571894c7-877c-42e5-a5ed-aa894a0de0b2.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 87d2c0ed091965b05fbe9552e52ffd4a62c11731169994157b2a5e897901e24f.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 11 (loglog floor-endpoint limit): for `x > 0`, given
`log⌊N^x⌋/log N → x` (#91), `loglog⌊N^x⌋ − loglog N → log x`. Two instances
subtracted give the §5.3 main-term limit `log t − log s`. -/
theorem erdos858_loglog_floor_limit :
    ∀ x : ℝ, 0 < x →
      Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x) →
      Filter.Tendsto (fun N : ℕ => Real.log (Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ))) - Real.log (Real.log (N:ℝ))) Filter.atTop (nhds (Real.log x)) := by
  intro x hx h91
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ))) Filter.atTop (nhds (Real.log x)) := h91.log (ne_of_gt hx)
  have hNx : Filter.Tendsto (fun N : ℕ => (N:ℝ)^x) Filter.atTop Filter.atTop := (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  have hfloor : Filter.Tendsto (fun N : ℕ => ⌊(N:ℝ)^x⌋₊) Filter.atTop Filter.atTop := tendsto_nat_floor_atTop.comp hNx
  have hev2 : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ ⌊(N:ℝ)^x⌋₊ := hfloor.eventually_ge_atTop 2
  refine hlog.congr' ?_
  filter_upwards [hev2, Filter.eventually_ge_atTop 2] with N hf2 hN2
  have hfr : (2:ℝ) ≤ ((⌊(N:ℝ)^x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hf2
  have hNr : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  rw [Real.log_div (ne_of_gt (Real.log_pos (by linarith))) (ne_of_gt (Real.log_pos (by linarith)))]

end Erdos858
