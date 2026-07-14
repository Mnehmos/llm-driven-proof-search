/-
Erdős Problem #858 — §5.4 foundation (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

Harmonic block-weight limit `harmonic(2n) − harmonic(n) → log 2` — the concrete,
floor-free instance of the §5.4 harmonic Riemann-sum block weight (toward the
asymptotic law Theorem 1.2).

The dyadic block `[n, 2n]` carries harmonic weight `Σ_{n<a≤2n} 1/a = harmonic(2n)
− harmonic(n)`, which converges to `log 2` — the "length" of the block under the
log-scale measure. This is exactly the mechanism of §5.4: the block
`{a : s ≤ log a/log N ≤ t}` has weight `→ t − s`; here `[n,2n]` in log-scale has
length `log 2`.

Proof: `harmonic(2n) − harmonic(n) = (harmonic(2n) − log(2n)) − (harmonic(n) −
log(n)) + (log(2n) − log(n))`; the first two terms each `→ γ` (Euler–Mascheroni,
via `Real.tendsto_harmonic_sub_log`, the second composed with `2·`) and cancel,
while `log(2n) − log(n) = log 2` (via `Real.log_mul`). Assembled with
`Tendsto.sub`/`.add_const`/`.congr'`. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 3f44886e-4f19-4005-95ec-648818a36c20,
  problem_version_id 74729e2b-bb38-4e7a-9c5f-993093f74250.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ce8088f281a5004e472c880c2a1373a2ffe5a703c8eb345e9ec5eba1182899ba.
-/
import Mathlib

namespace Erdos858

/-- Harmonic block-weight limit: `harmonic(2n) − harmonic(n) = Σ_{n<a≤2n} 1/a →
log 2`. The concrete floor-free instance of the §5.4 Riemann-sum block weight
(block `[n,2n]` has log-scale length `log 2`), toward Theorem 1.2. -/
theorem erdos858_harmonic_doubling_weight :
    Filter.Tendsto (fun n : ℕ => (harmonic (2 * n) : ℝ) - (harmonic n : ℝ)) Filter.atTop (nhds (Real.log 2)) := by
  have h2n : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.2
    intro b
    use b
    intro a ha
    omega
  have hA : Filter.Tendsto (fun n : ℕ => (harmonic (2 * n) : ℝ) - Real.log ((2 * n : ℕ) : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp h2n
  have hB : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hC := (hA.sub hB).add_const (Real.log 2)
  simp only [sub_self, zero_add] at hC
  refine hC.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  rw [Real.log_mul (by norm_num) hn0]
  ring

end Erdos858
