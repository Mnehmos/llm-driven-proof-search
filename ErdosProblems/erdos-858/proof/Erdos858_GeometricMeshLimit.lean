/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 4 (Chojecki 2026).

`geometric mesh limit`: for any `r > 0`,

  `r^(1/K)  →  1`   as `K → ∞`.

Proof: `r^(1/K) = exp(log r · (1/K))` (`Real.rpow_def_of_pos`); `log r · (1/K)
→ 0` (`tendsto_one_div_atTop_nhds_zero_nat` + `const_mul`); `exp` continuous,
`exp 0 = 1`.

Instantiated at `r = t/s`, this gives the geometric grid's mesh → 0: with
`v_j = s·(t/s)^{j/K}`, the block width `v_{j+1} − v_j = s·(t/s)^{j/K}·((t/s)^{1/K}
− 1) ≤ t·((t/s)^{1/K} − 1) → 0` as `K → ∞`, so eventually every block width is
below the uniform-continuity modulus `δ` — the refinement input (`herr`) of the
§5.3 prime-harmonic transfer.

Kernel-verified via the proofsearch MCP:
  episode a66e1427-a85f-4e4a-bee2-dd91328e96ea,
  problem_version_id a13fc978-a4be-4b74-ad54-a7d6c072dff8.
Outcome: kernel_verified / root_kernel_verified (2nd submission; the `.comp`
produced `Real.exp ∘ f` — bridged to the lambda form with `Function.comp_def`
in the `simpa` set, the recurring #98 fix).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d7937841a95db4a173777a661405343b9a96a14d55cd32be55ef6191717ee0f8.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 4 (geometric mesh limit): `r^(1/K) → 1` for `r > 0`, via
`r^(1/K) = exp(log r·(1/K))` and `log r·(1/K) → 0`. At `r = t/s` this gives the
geometric grid's vanishing mesh. -/
theorem erdos858_geometric_mesh_limit :
    ∀ r : ℝ, 0 < r →
      Filter.Tendsto (fun K : ℕ => r ^ ((1:ℝ) / (K:ℝ))) Filter.atTop (nhds 1) := by
  intro r hr
  have hinv : Filter.Tendsto (fun K : ℕ => (1:ℝ) / (K:ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hprod : Filter.Tendsto (fun K : ℕ => Real.log r * ((1:ℝ) / (K:ℝ))) Filter.atTop (nhds 0) := by simpa using hinv.const_mul (Real.log r)
  have hexp : Filter.Tendsto (fun K : ℕ => Real.exp (Real.log r * ((1:ℝ) / (K:ℝ)))) Filter.atTop (nhds 1) := by simpa [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hprod
  refine hexp.congr' ?_
  filter_upwards with K
  rw [Real.rpow_def_of_pos hr]

end Erdos858
