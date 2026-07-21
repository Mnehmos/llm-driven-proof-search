/-
Erdős Problem #858 — Theorem 1.2 assembly, swap-vanishing lemma (Chojecki 2026).

Bridges the uniform Lemma 5.5 discrepancy bound to the tail connector's `swap → 0`
input: if `|Φ(u_a)−R_N(a)| ≤ ε_N → 0` uniformly on the frontier range and the
normalized harmonic mass is bounded, the normalized swap sum → 0. Isolates uniform
Lemma 5.5 as the single remaining analytic leaf of Theorem 1.2.

Proof: triangle inequality (`Finset.abs_sum_le_sum_abs`) + per-term bound
(`abs_div`, `gcongr`) gives `|Σg/a| ≤ ε_N·Σ1/a`; divide by `L_N`, bound the mass by
`M`, `mul_le_mul_of_nonneg_left`; squeeze (`squeeze_zero_norm`) against `ε_N·M → 0`.

Kernel-verified via the proofsearch MCP:
  episode f25cbabc-407b-4c9c-b5b0-d721d30d5ab9,
  problem_version_id 5105d7fb-e8a5-4766-9529-b20acf69fe08.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash efd18d2de2c67312a44e9be477b6b26082a706a3456477a1dd8d97e68755ed7a.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 swap-vanishing: uniform bound `|g N a| ≤ ε N → 0` over bounded
normalized mass `⟹` normalized swap sum `→ 0`. Bridges uniform Lemma 5.5 to the
tail connector. -/
theorem erdos858_thm12_swap_vanishing :
    ∀ (g : ℕ → ℕ → ℝ) (ε L : ℕ → ℝ) (M : ℝ) (K sqrtN : ℕ → ℕ),
      (∀ N, 0 < L N) →
      (∀ N a, a ∈ Finset.Ioc (K N) (sqrtN N) → |g N a| ≤ ε N) →
      (∀ N, 0 ≤ ε N) →
      (∀ N, (∑ a ∈ Finset.Ioc (K N) (sqrtN N), 1/(a:ℝ)) / L N ≤ M) →
      Filter.Tendsto ε Filter.atTop (nhds 0) →
      Filter.Tendsto (fun N => (∑ a ∈ Finset.Ioc (K N) (sqrtN N), g N a / (a:ℝ)) / L N) Filter.atTop (nhds 0) := by
  intro g ε L M K sqrtN hL hbound hε hmass hε0
  have hterm : ∀ (N a : ℕ), a ∈ Finset.Ioc (K N) (sqrtN N) → |g N a / (a:ℝ)| ≤ ε N / (a:ℝ) := by intro N a ha; have ha0 : (0:ℝ) < (a:ℝ) := (by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le (K N)) (Finset.mem_Ioc.mp ha).1); rw [abs_div, abs_of_pos ha0]; gcongr; exact hbound N a ha
  have habs : ∀ N, |∑ a ∈ Finset.Ioc (K N) (sqrtN N), g N a / (a:ℝ)| ≤ ε N * ∑ a ∈ Finset.Ioc (K N) (sqrtN N), 1/(a:ℝ) := by intro N; refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_; rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun a ha => by rw [mul_one_div]; exact hterm N a ha)
  have hfinal : ∀ N, ‖(∑ a ∈ Finset.Ioc (K N) (sqrtN N), g N a / (a:ℝ)) / L N‖ ≤ ε N * M := by intro N; rw [Real.norm_eq_abs, abs_div, abs_of_pos (hL N), div_le_iff₀ (hL N)]; have hmass' : (∑ a ∈ Finset.Ioc (K N) (sqrtN N), 1/(a:ℝ)) ≤ M * L N := (div_le_iff₀ (hL N)).mp (hmass N); have hstep : ε N * (∑ a ∈ Finset.Ioc (K N) (sqrtN N), 1/(a:ℝ)) ≤ ε N * (M * L N) := mul_le_mul_of_nonneg_left hmass' (hε N); nlinarith [habs N, hstep]
  have hg0 : Filter.Tendsto (fun N => ε N * M) Filter.atTop (nhds 0) := by simpa using hε0.mul_const M
  exact squeeze_zero_norm hfinal hg0

end Erdos858
