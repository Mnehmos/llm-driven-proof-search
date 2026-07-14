/-
Erdős Problem #858 — §5.4 log-harmonic transfer, rung 3 (Chojecki 2026).

`fixed-K weighted block-sum limit` (Riemann step-sum assembly): for a fixed number
of blocks `K`, weights `c : ℕ → ℝ`, block-mass sequences `g : ℕ → ℕ → ℝ` and their
limits `L : ℕ → ℝ`, if for every `j < K` the sequence `N ↦ g N j → L j`, then
  `N ↦ Σ_{j < K} c j · g N j  →  Σ_{j < K} c j · L j`.

Specialized with `c j = f(j/K)`, `g N j =` the normalized log-scale mass of block `j`
(the interval `N^{j/K} < a ≤ N^{(j+1)/K}`, whose mass → `1/K` by rung 2, atom #99) and
`L j = 1/K`, this gives the Riemann step-sum
  `Σ_{j < K} f(j/K) · (1/K)  =  R_K(f)`
as the fixed-K, `N → ∞` limit of the log-harmonic weighted block sum. Combined with the
durable Riemann-sum theorem (#97, `R_K(f) → ∫₀¹ f` as `K → ∞`), the two-limit squeeze
(`N → ∞` for fixed `K`, then `K → ∞`) yields the full log-harmonic transfer
`(1/log N) Σ_{1<a≤N} f(log a/log N)/a → ∫₀¹ f`, the analytic engine of the asymptotic
law Theorem 1.2 (routed through §6 eventual frontier exactness).

Proof: `tendsto_finset_sum` reduces to per-block convergence; each summand
`N ↦ c j · g N j` converges by `Tendsto.mul` of the constant `c j`
(`tendsto_const_nhds`) with the block-mass hypothesis. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 0f811ba8-f204-4897-b2fb-da26cc030f25,
  problem_version_id 6110060c-586f-430f-a99f-6cdb980af045.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 158f0af5f137ccbe5ba1c71ffea1a232ca20d5f20119a20b714ec1e801a12b0c.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer rung 3 (Riemann step-sum assembly): a finite weighted sum
of convergent block-mass sequences converges to the weighted sum of limits. With
`c j = f(j/K)`, `L j = 1/K` this is exactly the step-sum `R_K(f)` as the fixed-K,
`N→∞` limit; combined with #97 it drives the full log-harmonic transfer toward the
asymptotic law Theorem 1.2. Proof: `tendsto_finset_sum` + `tendsto_const_nhds.mul`. -/
theorem erdos858_weighted_block_sum :
    ∀ (K : ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (L : ℕ → ℝ),
      (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (L j))) →
      Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * L j)) := by
  intro K c g L hg
  apply tendsto_finset_sum
  intro j hj
  exact (tendsto_const_nhds).mul (hg j hj)

end Erdos858
