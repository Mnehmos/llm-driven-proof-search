/-
Erdős Problem #858 — §5 quantitative Mertens, Chebyshev ψ linear bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5; the O(x) Chebyshev input to Mertens' FIRST theorem
Σ_{p≤x}(log p)/p = log x + O(1), whose exact constant c₂ #858 needs.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 46121fef-5e5d-49e5-bec4-34f36f5c1dff,
problem_version_id 725fa23b-04a9-4cce-ace3-bc378b35caf8.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4bf8ea3e…

Result:  ∀ N : ℕ,  Σ_{n=1}^{N} Λ(n) ≤ (log 4 + 4)·N,

i.e. ψ(N) ≤ (log 4 + 4)·N — Chebyshev's upper bound ψ(x) = O(x) packaged into
the finite-sum form Mertens' first theorem consumes. This is step (2) of the
classical Mertens-1 proof (log n = Σ_{d|n} Λ(d); ψ(x)=O(x); Stirling): the
statement that the von Mangoldt partial sum grows at most linearly.

Proof: a direct repackaging of Mathlib's Chebyshev.psi_le_const_mul_self.
  1. Chebyshev.psi_le_const_mul_self (0 ≤ (N:ℝ) by positivity) :
        ψ (N:ℝ) ≤ (Real.log 4 + 4) · (N:ℝ).
  2. Unfold Chebyshev.psi : ψ x = Σ_{n ∈ Finset.Ioc 0 ⌊x⌋₊} Λ n.
  3. ⌊(N:ℝ)⌋₊ = N  (Nat.floor_natCast).
  4. Reindex the sum's index set: Finset.Icc 1 N = Finset.Ioc 0 N
     (Finset.Icc_succ_left_eq_Ioc 0 N, using Order.succ 0 ≡ 1 on ℕ).

Constant note: Mathlib also has the sharper Chebyshev.psi_le
(ψ x ≤ log 4 · x + 2√x · log x), whose main coefficient is log 4 = 2 log 2,
but that carries a √x·log x remainder and is not a clean linear bound; the
const-multiple form log 4 + 4 (≈ 5.386) is the right O(x) input here.

Self-contained; verified against the pinned Mathlib. The proof term below is the
exact byte-for-byte tactic block accepted by the kernel via episode_step.
-/
import Mathlib

open Finset

theorem erdos858_mertens1_psi_le_linear :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n
        ≤ (Real.log 4 + 4) * (N : ℝ) := by
  intro N
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  unfold Chebyshev.psi at h
  rw [Nat.floor_natCast] at h
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N from Finset.Icc_succ_left_eq_Ioc 0 N]
  exact h
