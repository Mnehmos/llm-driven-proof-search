/-
Erdős Problem #858 — §5.2/§5.3 o(1)-Mertens arc, atom 12 (Chojecki 2026).

`A-ratio floor-endpoint limit` (bounded remainder): for `A : ℕ → ℝ` with
`|A(k) − log k| ≤ C` for `k ≥ 2` (the Mertens-1 stack supplies this for
`A = Σ_{p≤k} log p/p`) and `x > 0`,

  `A(⌊N^x⌋)/log⌊N^x⌋ − 1  →  0`.

Proof: `|A(k)/log k − 1| = |A(k) − log k|/log k ≤ C/log k`, and
`C/log⌊N^x⌋ → 0` along the rpow/floor/log atTop chain; `squeeze_zero_norm'`.
Two instances give the vanishing of the boundary terms
`A(n)/log n − A(m)/log m` in the interval-Mertens limit.

With this, ALL ingredients of the §5.3 prime-block-mass limit are verified:
the deterministic identity (#125 + #126 + #123), the loglog main term
(#127 ×2 → `log t − log s`), the boundary ratios (this, ×2 → 0), and the tail
(`C/log⌊N^s⌋ → 0`). The final Tendsto assembly yields
`Σ_{N^s<p≤N^t} 1/p → log(t/s)`.

Kernel-verified via the proofsearch MCP:
  episode 41ccb206-dcfd-46aa-aa6c-cc3775c09fa4,
  problem_version_id 7eda46c2-9ca1-427e-9631-1637cc6d3d7c.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f071aaba2f7632f310612b07553a7d45f16c8d96f1e41cf73ef7bdc3bd7f1da6.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 12 (A-ratio floor limit): `|A(k) − log k| ≤ C` for
`k ≥ 2` implies `A(⌊N^x⌋)/log⌊N^x⌋ − 1 → 0` for `x > 0`, via
`squeeze_zero_norm'` against `C/log⌊N^x⌋ → 0`. -/
theorem erdos858_a_ratio_floor_limit :
    ∀ (A : ℕ → ℝ) (C x : ℝ), 0 < x →
      (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
      Filter.Tendsto (fun N : ℕ => A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) - 1) Filter.atTop (nhds 0) := by
  intro A C x hx hA
  have hNx : Filter.Tendsto (fun N : ℕ => (N:ℝ)^x) Filter.atTop Filter.atTop := (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  have hfloor : Filter.Tendsto (fun N : ℕ => ⌊(N:ℝ)^x⌋₊) Filter.atTop Filter.atTop := tendsto_nat_floor_atTop.comp hNx
  have hlogT : Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ))) Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hfloor)
  have hg : Filter.Tendsto (fun N : ℕ => C / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ))) Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogT
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ‖A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) - 1‖ ≤ C / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) := by filter_upwards [hfloor.eventually_ge_atTop 2] with N hf2; have hfr : (2:ℝ) ≤ ((⌊(N:ℝ)^x⌋₊ : ℕ) : ℝ) := (by exact_mod_cast hf2); have hlogpos : (0:ℝ) < Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) := Real.log_pos (by linarith); have hEq : A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) - 1 = (A ⌊(N:ℝ)^x⌋₊ - Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ))) / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) := (by field_simp); rw [Real.norm_eq_abs, hEq, abs_div, abs_of_pos hlogpos]; exact mul_le_mul_of_nonneg_right (hA ⌊(N:ℝ)^x⌋₊ hf2) (inv_nonneg.mpr (le_of_lt hlogpos))
  exact squeeze_zero_norm' hev hg

end Erdos858
