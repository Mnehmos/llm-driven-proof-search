/-
Erdős Problem #858 — §5.4 log-harmonic transfer, rung 2 (Chojecki 2026).

`log-harmonic block mass`: for `0 < s < t`,
  `(harmonic(⌊N^t⌋) − harmonic(⌊N^s⌋)) / log N  →  t − s`   as `N → ∞`,
i.e. the log-scale mass of a single block `N^s < a ≤ N^t`,
  `(1/log N) · Σ_{⌊N^s⌋ < a ≤ ⌊N^t⌋} 1/a  →  t − s`,
is exactly the block width `t − s` in the u = log a / log N coordinate. This is the
harmonic analogue of the width `(j+1)/K − j/K = 1/K` of a partition block, and the
second rung of the log-harmonic transfer that carries the sum onto the interval
integral (toward the asymptotic law Theorem 1.2, routed through §6 eventual frontier
exactness).

Conditional on the two normalized-endpoint limits `harmonic(⌊N^s⌋)/log N → s` and
`harmonic(⌊N^t⌋)/log N → t` (kernel-verified rung 1, atom #98, taken as hypotheses
since problem_versions cannot cross-reference). Proof: subtract the two limits
(`Filter.Tendsto.sub`) to get the difference of quotients tending to `t − s`, then
transport pointwise via `a/L − b/L = (a−b)/L` (a `ring` identity that holds even at
`L = 0`). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode eedeed16-3f8d-4219-9803-8afdbe236eab,
  problem_version_id b12afd35-5b51-44af-a272-1ac96b611df0.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f64d151e287336d5f4eae4bbd7378d1c0eb6c77992646be61dbb8e3cf2afae7d.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer rung 2 (block mass): for `0 < s < t`, given the two
normalized-endpoint limits (#98), the log-scale mass of the block `N^s < a ≤ N^t` is
`(harmonic(⌊N^t⌋) − harmonic(⌊N^s⌋))/log N → t − s`. The harmonic analogue of a
partition-block width. Proof: `Tendsto.sub` then the ring identity `a/L − b/L =
(a−b)/L`. Toward the asymptotic law Theorem 1.2. -/
theorem erdos858_log_block_mass :
    ∀ s t : ℝ, 0 < s → s < t →
      Filter.Tendsto (fun N : ℕ => (harmonic (⌊(N:ℝ)^s⌋₊) : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds s) →
      Filter.Tendsto (fun N : ℕ => (harmonic (⌊(N:ℝ)^t⌋₊) : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds t) →
      Filter.Tendsto (fun N : ℕ => ((harmonic (⌊(N:ℝ)^t⌋₊) : ℝ) - (harmonic (⌊(N:ℝ)^s⌋₊) : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (t - s)) := by
  intro s t hs hst hslim htlim
  have h := htlim.sub hslim
  refine h.congr' ?_
  filter_upwards with N
  ring

end Erdos858
