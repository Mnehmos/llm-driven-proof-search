/-
Erdős Problem #858 — §5.4 foundation (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

General block-endpoint limit `log(N^x − 1)/log N → x` — the rpow core for the
log-scale partition of the §5.4 harmonic Riemann sum (toward Theorem 1.2).

For the log-scale partition, the block up to `N^x` has right endpoint `⌊N^x⌋`, and
`log⌊N^x⌋/log N → x`. The reusable core is `log(N^x − 1)/log N → x` (the floor
value satisfies `N^x − 1 < ⌊N^x⌋ ≤ N^x`, so `log⌊N^x⌋/log N` is squeezed between
this and `log(N^x)/log N = x`).

Proof: `log(N^x − 1) = log(N^x·(1 − N^{−x})) = x·log N + log(1 − N^{−x})` (via
`Real.log_mul` + `Real.log_rpow`); dividing by `log N` gives `x + log(1 −
N^{−x})/log N`, and the second term `→ 0` — since `N^{−x} = (N^x)^{−1} → 0`
(`tendsto_rpow_atTop` + `Tendsto.inv_tendsto_atTop`), `log(1 − N^{−x}) → log 1 = 0`
(`Real.continuousAt_log`), over `log N → ∞` (`Tendsto.div_atTop`). Elementary, no
PNT.

Kernel-verified via the proofsearch MCP:
  episode 44ca9c9f-f975-4178-9067-a90263752982,
  problem_version_id 3033e0c0-d8e4-4823-9a02-bbb0230682d3.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c58f06447669babaa435f129874541500be87b5c9d3076a90288c5d70fad3a2e.
-/
import Mathlib

namespace Erdos858

/-- General block-endpoint limit: for `x > 0`, `log(N^x − 1)/log N → x`. The rpow
core of the §5.4 log-scale partition — the floor value `log⌊N^x⌋/log N` is squeezed
between this and `log(N^x)/log N = x`. Toward Theorem 1.2. -/
theorem erdos858_rpow_block_limit :
    ∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => Real.log ((N:ℝ)^x - 1) / Real.log (N:ℝ)) Filter.atTop (nhds x) := by
  intro x hx
  have hlogN : Filter.Tendsto (fun N : ℕ => Real.log (N:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNx : Filter.Tendsto (fun N : ℕ => (N:ℝ)^x) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  have hNegx : Filter.Tendsto (fun N : ℕ => ((N:ℝ)^x)⁻¹) Filter.atTop (nhds 0) := hNx.inv_tendsto_atTop
  have h1sub : Filter.Tendsto (fun N : ℕ => 1 - ((N:ℝ)^x)⁻¹) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hNegx
  have hlog1 : Filter.Tendsto (fun N : ℕ => Real.log (1 - ((N:ℝ)^x)⁻¹)) Filter.atTop (nhds 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto
    simpa [Function.comp_def] using hcont.comp h1sub
  have hratio0 : Filter.Tendsto (fun N : ℕ => Real.log (1 - ((N:ℝ)^x)⁻¹) / Real.log (N:ℝ)) Filter.atTop (nhds 0) :=
    hlog1.div_atTop hlogN
  have key := hratio0.const_add x
  simp only [add_zero] at key
  refine key.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with N hN
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNxpos : (0:ℝ) < (N:ℝ)^x := Real.rpow_pos_of_pos hNpos x
  have hNxgt1 : (1:ℝ) < (N:ℝ)^x := (Real.one_lt_rpow_iff_of_pos hNpos).mpr (Or.inl ⟨hN1, hx⟩)
  have hlogNne : Real.log (N:ℝ) ≠ 0 := (Real.log_pos hN1).ne'
  have hinv1 : ((N:ℝ)^x)⁻¹ < 1 := by rw [inv_lt_one₀ hNxpos]; exact hNxgt1
  have h1subpos : (0:ℝ) < 1 - ((N:ℝ)^x)⁻¹ := by linarith
  have hmul : (N:ℝ)^x * (1 - ((N:ℝ)^x)⁻¹) = (N:ℝ)^x - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hNxpos)]
  have hid : Real.log ((N:ℝ)^x - 1) = x * Real.log (N:ℝ) + Real.log (1 - ((N:ℝ)^x)⁻¹) := by
    rw [← hmul, Real.log_mul (ne_of_gt hNxpos) (ne_of_gt h1subpos), Real.log_rpow hNpos]
  rw [hid]
  field_simp

end Erdos858
