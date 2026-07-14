/-
Erdős Problem #858 — Proposition 3.2 (frontier sweep), abstract telescoping.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 3.2.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode e347aa8f-a9b9-481f-af7f-e22a62f47a18,
problem_version_id 538459d3-fca2-4c87-b695-2eccb5a564c9.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 18493e66…

The telescoping half of Proposition 3.2: if s 0 = 1 and s(K+1) = s K + g(K+1)
(the frontier increment identity, Erdos858_FrontierSweepStep with s = S_N,
g = q_N and base Erdos858_FrontierBaseZero giving s 0 = 1), then
s K = 1 + Σ_{a=1}^K g a. Instantiated: S_N(K) = 1 + Σ_{a≤K} q_N(a).

Proved by an ultracode subagent; verified first submission.
-/
import Mathlib

namespace Erdos858

/-- Proposition 3.2, telescoping: from `s 0 = 1` and the increment
`s (K+1) = s K + g (K+1)`, conclude `s K = 1 + Σ_{a=1}^K g a`. -/
theorem frontier_sweep_telescope :
    ∀ (s g : ℕ → ℚ), s 0 = 1 → (∀ K : ℕ, s (K + 1) = s K + g (K + 1)) →
      ∀ K : ℕ, s K = 1 + ∑ a ∈ Finset.Icc 1 K, g a := by
  intro s g h0 hstep K
  induction K with
  | zero => rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, add_zero]; exact h0
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ K + 1), hstep K, ih]
    ring

end Erdos858
