/-
Erdős Problem #858 — §5.3/§5.4 foundation (Chojecki 2026, "An exact frontier
theorem and the asymptotic constant for Erdős problem #858").

Harmonic interval-sum bound — the "weight" primitive for the prime-harmonic /
harmonic Riemann sums (Lemma 5.3/5.4), toward the asymptotic law Theorem 1.2.

The harmonic interval sum `Σ_{m<a≤n} 1/a = harmonic n − harmonic m` (`harmonic k =
Σ_{a=1}^k 1/a`, Mathlib's `harmonic`) equals `log(n/m) + O(1)` with an EXPLICIT
`O(1)`: Mathlib's tight harmonic bounds `log(n+1) ≤ harmonic n ≤ 1 + log n`
(`log_add_one_le_harmonic`, `harmonic_le_one_add_log`) sandwich it as
  `log(n+1) − (1 + log m) ≤ harmonic n − harmonic m ≤ (1 + log n) − log(m+1)`,
so the deviation from `log n − log m` is bounded by an absolute constant (≤ 2).

This is the foundation stone for the Riemann-sum keystone of §5.4: partitioning
`[1,N]` by `log a / log N ∈ [s,t]` gives block weight `Σ 1/a ≈ (t−s)·log N`, which
drives `(1/log N) Σ f(log a/log N)/a → ∫₀¹ f` and hence the asymptotic law
`M(N) = (c₂+o(1)) log N`. Purely elementary — no PNT; the `O(1)` is Mathlib-provided
(and the exact limit is the Euler–Mascheroni constant via
`tendsto_harmonic_sub_log`).

Proof: `constructor`; each side by `linarith` from `log_add_one_le_harmonic` and
`harmonic_le_one_add_log` instantiated at `n` and `m` (with `push_cast` to bridge
`↑(k+1) = ↑k + 1`).

Kernel-verified via the proofsearch MCP:
  episode 42abd404-e5da-43c7-8cf2-f5c95c1e8556,
  problem_version_id 8b32a247-b7d4-411c-bb66-a3e37bd18447.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d799ced711a5b4b2e4bac4f3b6bc783144d2688b12a401458e2ebb128d053c80.
-/
import Mathlib

namespace Erdos858

/-- Harmonic interval-sum bound: `harmonic n − harmonic m = Σ_{m<a≤n} 1/a` lies within
an absolute constant of `log n − log m` — precisely
`log(n+1) − (1 + log m) ≤ harmonic n − harmonic m ≤ (1 + log n) − log(m+1)`.
The "weight" primitive for the §5.4 harmonic Riemann sums (toward Theorem 1.2). -/
theorem erdos858_harmonic_interval_bound :
    ∀ m n : ℕ,
      Real.log ((n : ℝ) + 1) - (1 + Real.log (m : ℝ)) ≤ ((harmonic n : ℝ) - (harmonic m : ℝ)) ∧
      ((harmonic n : ℝ) - (harmonic m : ℝ)) ≤ (1 + Real.log (n : ℝ)) - Real.log ((m : ℝ) + 1) := by
  intro m n
  refine ⟨?_, ?_⟩
  · have h1 := log_add_one_le_harmonic n
    have h2 := harmonic_le_one_add_log m
    push_cast at h1
    linarith
  · have h1 := harmonic_le_one_add_log n
    have h2 := log_add_one_le_harmonic m
    push_cast at h2
    linarith

end Erdos858
