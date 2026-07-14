/-
Erdős Problem #858 — Proposition 3.2 base case: A_N(0) = {1}.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 3.2, S_N(0) = 1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 4a2263f0-2ea3-4bdf-893d-fa67d9a01d3a,
problem_version_id 9f3c42cb-4a78-4888-ab97-7a8ba65ad396.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 715ada62…

The frontier at cutoff K = 0 is exactly {1}: A_N(0) = {n ≤ N : π n ≤ 0 < n} =
{1}, since π 1 = 0 and every n ≥ 2 has π n ≥ 1. Hence S_N(0) = 1/1 = 1, the base
of the frontier sweep (feeding `s 0 = 1` into Erdos858_FrontierSweepTelescope).

Proved by an ultracode subagent; verified first submission.
-/
import Mathlib

namespace Erdos858

/-- Proposition 3.2 base: the K = 0 frontier is `{1}`. -/
theorem frontier_base_zero :
    ∀ (π : ℕ → ℕ) (N : ℕ), 1 ≤ N → π 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n) →
      (Finset.Icc 1 N).filter (fun n => π n ≤ 0 ∧ 0 < n) = {1} := by
  intro π N hN hπ1 hax
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, hN'⟩, hπ0, -⟩
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hp := hax n hn2 hN'
    omega
  · rintro rfl
    exact ⟨⟨le_refl 1, hN⟩, le_of_eq hπ1, by norm_num⟩

end Erdos858
