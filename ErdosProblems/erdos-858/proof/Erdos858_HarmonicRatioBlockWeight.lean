/-
Erdős Problem #858 — §5.4 foundation (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

General integer-ratio harmonic block weight `harmonic(kn) − harmonic(n) → log k` —
the §5.4 Riemann-sum block weight for any block ratio (toward Theorem 1.2).

Generalizing the dyadic case (`erdos858_harmonic_doubling_weight`, #88, k=2): for
any integer `k ≥ 1`, the block `[n, kn]` carries harmonic weight
`Σ_{n<a≤kn} 1/a = harmonic(kn) − harmonic(n) → log k` — the log-scale length of the
block. Proof: `harmonic(kn) − harmonic(n) = (harmonic(kn) − log(kn)) − (harmonic(n)
− log(n)) + (log(kn) − log(n))`; the first two terms each `→ γ`
(`Real.tendsto_harmonic_sub_log`, the first composed with `k·`) and cancel, while
`log(kn) − log(n) = log k` (`Real.log_mul`). Together with the rpow block-endpoint
limit (`erdos858_rpow_block_limit`, #89) this covers the §5.4 block-weight machinery
for both integer and continuous block ratios. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 1cb8e26c-e695-4d9f-939a-d2c304c47c46,
  problem_version_id 2b9be4bb-1925-4790-9930-66cdc464d81c.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ba71e1cf015843298805b4dce32fa4aaec3069fca66b5ecc66a6af74b0152b19.
-/
import Mathlib

namespace Erdos858

/-- General integer-ratio harmonic block weight: for `k ≥ 1`,
`harmonic(kn) − harmonic(n) = Σ_{n<a≤kn} 1/a → log k`. The §5.4 Riemann-sum block
weight for any block ratio (generalizes the dyadic #88). Toward Theorem 1.2. -/
theorem erdos858_harmonic_ratio_block_weight :
    ∀ k : ℕ, 1 ≤ k → Filter.Tendsto (fun n : ℕ => (harmonic (k * n) : ℝ) - (harmonic n : ℝ)) Filter.atTop (nhds (Real.log (k : ℝ))) := by
  intro k hk
  have hkn : Filter.Tendsto (fun n : ℕ => k * n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.2
    intro b
    exact ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hk)⟩
  have hA : Filter.Tendsto (fun n : ℕ => (harmonic (k * n) : ℝ) - Real.log ((k * n : ℕ) : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp hkn
  have hB : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hC := (hA.sub hB).add_const (Real.log (k:ℝ))
  simp only [sub_self, zero_add] at hC
  refine hC.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  rw [Real.log_mul hk0 hn0]
  ring

end Erdos858
