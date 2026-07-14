/-
Erdős Problem #858 — §5 analytic foundation: Mertens' first theorem, LOWER-bound
assembly. Conditional assembly of the von Mangoldt log-sum lower bound
Σ_{d≤N} Λ(d)/d ≥ log N − 1 from the campaign's verified building blocks.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode c3e63438-1a4a-4da7-aed4-89b0c1ddb1f9,
problem_version_id 72849c7f-a813-44ed-8fe8-5a6d1ce674ea.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bf2abe3ac717422014270fe646bfa64863cfb0dfd92ce6bb8c56ff3707f60597.

Content: the exact constant c₂ of #858 needs Mertens' first theorem, whose LOWER
half for the von Mangoldt weight is  Σ_{d≤N} Λ(d)/d ≥ log N − 1. Its elementary
proof chains three building blocks, each already kernel-verified in this campaign
and here TAKEN AS HYPOTHESES (mirroring the cor35_max_eq / thm24_value_recursion
technique — assemble abstractly over the building-block conclusions):
  • #41+#43:            log(N!) = Σ_{d≤N} Λ(d)·⌊N/d⌋   ⟹ set F := log(N!),
                        P := that von Mangoldt sum, giving the hypothesis F = P;
  • fractional-part:    Σ_d Λ(d)·⌊N/d⌋ ≤ N · Σ_d Λ(d)/d ⟹ set S := Σ_{d≤N} Λ(d)/d,
                        giving the hypothesis P ≤ N·S;
  • Stirling lower:     N·log N − N ≤ log(N!)          ⟹ the hypothesis
                        N·log N − N ≤ F.
The assembly then concludes log N − 1 ≤ S. Substituting the intended meanings of
F, P, S this is exactly Σ_{d≤N} Λ(d)/d ≥ log N − 1, one direction of Mertens'
first theorem for the von Mangoldt sum — a genuine milestone toward c₂.

Proof: pure real arithmetic. From N·log N − N ≤ F = P ≤ N·S obtain the chain
N·log N − N ≤ N·S, i.e. N·(log N − 1) ≤ N·S; since 0 < N (cast from 0 < N on ℕ
via `exact_mod_cast`) dividing through yields log N − 1 ≤ S. Discharged by
`nlinarith`: the sole nonlinear step is the product of `hN' : 0 < ↑N` with the
negated goal `log N − 1 − S > 0`, which contradicts the linear chain; `Real.log ↑N`
is carried as an opaque atom and matches the `↑N * Real.log ↑N` monomial of the
Stirling hypothesis. This is a CONDITIONAL assembly: the three feeder building
blocks (#41+#43 log-factorial identity, the fractional-part/⌊N/d⌋≤N/d step, and
the Stirling lower bound `Stirling.le_log_factorial_stirling`) are proved
separately; wiring their conclusions in yields the unconditional lower bound.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens-1 LOWER-bound assembly. Given the three building-block
conclusions as hypotheses — `F = P` (log(N!) equals the von Mangoldt sum, #41+#43),
`P ≤ N·S` (the fractional-part step Σ Λ(d)·⌊N/d⌋ ≤ N·Σ Λ(d)/d), and
`N·log N − N ≤ F` (Stirling lower bound) — with `0 < N`, the von Mangoldt log-sum
`S := Σ_{d≤N} Λ(d)/d` satisfies `log N − 1 ≤ S`. This is one direction of Mertens'
first theorem for the von Mangoldt weight. -/
theorem erdos858_mertens1_lower_assembly :
    ∀ (N : ℕ) (S P F : ℝ), 0 < N → F = P → P ≤ (N : ℝ) * S →
      (N : ℝ) * Real.log N - (N : ℝ) ≤ F → Real.log N - 1 ≤ S := by
  intro N S P F hN hFP hPS hStir
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  nlinarith [hN', hFP, hPS, hStir]

end Erdos858
