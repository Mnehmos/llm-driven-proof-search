/-
Erdős Problem #858 — Lemma 4.3 (Chojecki 2026, "An exact frontier theorem and
the asymptotic constant for Erdős problem #858").

Low-layer prime bound — CONDITIONAL REDUCTION to the Kinlaw–Pomerance error input.

Lemma 4.3 states `Σ_{a<p≤a³} 1/p > 1` for every integer `a ≥ 20`. The paper
derives it from Mertens' second theorem plus explicit Kinlaw–Pomerance bounds on
the error term `E(x) := Σ_{p≤x} 1/p − loglog x − M` (`M` = Meissel–Mertens
constant). This atom isolates the analytic core as a conditional reduction.

Model the two Mertens partial sums by their asymptotic form with a COMMON constant
`M` and error terms `Ea`, `Ea3`:
  `S_a  = Σ_{p≤a}  1/p = loglog a    + M + Ea`,
  `S_a3 = Σ_{p≤a³} 1/p = loglog(a³) + M + Ea3`.
The interval sum is `Σ_{a<p≤a³} 1/p = S_a3 − S_a`. Because
  `loglog(a³) − loglog a = log(3 · log a) − log(log a) = log 3`   (for `a > 1`),
the Meissel–Mertens constant `M` and the `loglog a` term both CANCEL, leaving
  `S_a3 − S_a = log 3 + (Ea3 − Ea)`.
Since `log 3 ≈ 1.0986 > 1`, the interval sum exceeds `1` as soon as the error
DIFFERENCE satisfies `|Ea3 − Ea| < log 3 − 1 ≈ 0.0986` — exactly the explicit
control Kinlaw–Pomerance supply for `a ≥ 20` (`a³ ≥ 8000`).

Consequence: via the kernel-verified chain
  Lemma 4.3  ⇒  Cor 4.4 (#75)  ⇒  sign theorem (#76)  ⇒  Theorem 1.1 (#73),
the ENTIRE remaining gap to unconditional Theorem 1.1 (`M(N) = M_fr(N)`) is this
single explicit inequality on the Mertens-error difference. No PNT is needed, and
the (PNT-grade) sharp value of `M` is irrelevant — it cancels. Pure real analysis;
the `log`-cancellation identity is the mathematical content.

Proof: `Real.log_pow` gives `log(a³) = 3·log a`; `Real.log_mul` (with `3 ≠ 0` and
`log a ≠ 0` from `a > 1`) splits `log(3·log a) = log 3 + log(log a)`, so
`loglog(a³) = log 3 + loglog a`; substituting the two sum hypotheses, `M` and
`loglog a` cancel, and `abs_lt` + `linarith` close `1 < log 3 + (Ea3 − Ea)`.

Kernel-verified via the proofsearch MCP:
  episode 0797b269-69e7-4fc1-89a7-1d54a052f985,
  problem_version_id 9ac90b1b-7029-44e7-a78b-dac99b6cc1c0.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4306ebb61dc2faad205b4b0de90930da0588a8a23a59d0d08a8543094028644d.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.3 conditional reduction: if the prime-reciprocal partial sums up to `a`
and up to `a³` both have the Mertens form `loglog + M + error` with a common
constant `M`, and the error difference satisfies `|Ea3 − Ea| < log 3 − 1`, then the
interval sum `Σ_{a<p≤a³} 1/p = S_a3 − S_a` exceeds `1`. The Meissel–Mertens
constant `M` cancels (via `loglog(a³) − loglog a = log 3`), so unconditional
Theorem 1.1 reduces to this single explicit Kinlaw–Pomerance error-difference
inequality — no PNT, no sharp `M`. -/
theorem erdos858_lemma43_reduction :
    ∀ (a M Ea Ea3 S_a S_a3 : ℝ), 1 < a →
      S_a = Real.log (Real.log a) + M + Ea →
      S_a3 = Real.log (Real.log (a ^ 3)) + M + Ea3 →
      |Ea3 - Ea| < Real.log 3 - 1 →
      1 < S_a3 - S_a := by
  intro a M Ea Ea3 S_a S_a3 ha1 hSa hSa3 hE
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hloga_ne : Real.log a ≠ 0 := ne_of_gt hloga
  have hll : Real.log (Real.log (a ^ 3)) = Real.log 3 + Real.log (Real.log a) := by
    rw [Real.log_pow, Real.log_mul (by norm_num : ((3:ℕ):ℝ) ≠ 0) hloga_ne]
    norm_num
  rw [hSa, hSa3, hll]
  rw [abs_lt] at hE
  linarith [hE.1]

end Erdos858
