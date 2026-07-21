/-
Erdős Problem #858 — §5.4 log-harmonic transfer, discharge atom 3 (Chojecki 2026).

`eventual harmonic-vs-2log bound` (hharm2): from the harmonic-ratio limit
`harmonic N/log N → 1` (#87's conclusion, via Mathlib's Euler–Mascheroni
`Real.tendsto_harmonic_sub_log`), eventually in `N`:

  `harmonic N − harmonic 1 ≤ 2·log N`.

This discharges the `hharm2` hypothesis of the eventual transfer error (#110).
Proof: at `ε = 1/2` the ratio is eventually `< 3/2`, so `harmonic N <
(3/2)·log N` for `N ≥ max N₀ 2` (where `log N > 0`); since `harmonic 1 = 1 > 0`,
the difference is `< (3/2)·log N ≤ 2·log N`.

Kernel-verified via the proofsearch MCP:
  episode 447541f5-2ff5-4bc6-aa18-4d50ca4db891,
  problem_version_id 48b1ec48-654d-4b26-8aac-620aa213d8aa.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 92455c2d2b82a39ed4b4ff7ae4b4859e9a15ea42b3ae60deb10e85e10bf30356.

**Lean note**: `harmonic 1 = 1` needs the literal-vs-succ pattern bridge
`rw [show (1:ℕ) = 0 + 1 from rfl]` before `harmonic_succ` can fire (the OfNat
literal `1` does not syntactically match the `(n+1)` pattern; the defeq
rfl-rewrite fixes the syntax), then `harmonic_zero` + `norm_num`.
-/
import Mathlib

namespace Erdos858

/-- Discharge atom 3 (hharm2): from `harmonic N/log N → 1` (#87), eventually
`harmonic N − harmonic 1 ≤ 2·log N`. Feeds the herr atom (#110). -/
theorem erdos858_harmonic_vs_two_log :
    Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log (n:ℝ)) Filter.atTop (nhds 1) →
    ∀ᶠ N : ℕ in Filter.atTop, (harmonic N : ℝ) - (harmonic 1 : ℝ) ≤ 2 * Real.log (N:ℝ) := by
  intro h87
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp h87 (1/2) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (max N₀ 2)] with N hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1n : 1 < N := hN2
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN1n
  have hlogpos : (0:ℝ) < Real.log (N:ℝ) := Real.log_pos hN1
  have hd := hN₀ N hNN₀
  rw [Real.dist_eq] at hd
  have hub : (harmonic N : ℝ) / Real.log (N:ℝ) - 1 < 1/2 := (abs_lt.mp hd).2
  have hratio : (harmonic N : ℝ) / Real.log (N:ℝ) < 3/2 := by linarith
  have hharm : (harmonic N : ℝ) < 3/2 * Real.log (N:ℝ) := (div_lt_iff₀ hlogpos).mp hratio
  have h1q : (harmonic 1 : ℚ) = 1 := by rw [show (1:ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero]; norm_num
  have h1r : (harmonic 1 : ℝ) = 1 := by exact_mod_cast h1q
  rw [h1r]
  linarith

end Erdos858
