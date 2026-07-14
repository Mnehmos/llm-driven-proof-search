/-
Erdős Problem #858 — §5 analytic foundation: PRIME-SUM Mertens' first theorem,
LOWER-bound assembly. Conditional assembly of the prime-sum lower bound
Σ_{p≤N}(log p)/p ≥ log N − 2 from the campaign's verified von Mangoldt log-sum
lower bound (#47) plus a prime-power tail bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode 366e5cae-5e60-4602-bd41-2a55bb483a5a,
problem_version_id f81f9ceb-51ba-41b9-819c-646ea633a9c2.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0f5ce968caa010ac8b9b93139c5b347718916b8926c751aab8b7d6163d081963.

Content: the exact constant c₂ of #858 needs Mertens' first theorem for the PRIME
sum  Sp := Σ_{p≤N}(log p)/p.  It descends from the von Mangoldt log-sum version
by peeling the proper-prime-power tail.  Write Sl := Σ_{d≤N} Λ(d)/d for the von
Mangoldt log-sum, Sp for the prime sum, and T := Sl − Sp for the contribution of
proper prime powers p^k (k ≥ 2).  Two elementary facts, TAKEN AS HYPOTHESES here
(mirroring the erdos858_mertens1_lower_assembly / cor35_max_eq technique —
assemble abstractly over feeder conclusions):
  • decomposition:      Sl = Sp + T;
  • tail bounds:        0 ≤ T   and   T ≤ 1
                        (the true tail Σ_{p,k≥2}(log p)/p^k < 1, an absolute
                        constant — nonneg since every term is nonneg);
together with the campaign-verified von Mangoldt LOWER bound (#47):
  • von Mangoldt #47:   Real.log N − 1 ≤ Sl.
The assembly then concludes  Real.log N − 2 ≤ Sp.  Substituting the intended
meanings of Sp, Sl, T this is exactly Σ_{p≤N}(log p)/p ≥ log N − 2, the PRIME-sum
form of one direction of Mertens' first theorem — the object §5 actually feeds
into the exact constant c₂.

Proof: pure real arithmetic. From Sl = Sp + T obtain Sp = Sl − T; then
Sp = Sl − T ≥ (log N − 1) − 1 = log N − 2, using log N − 1 ≤ Sl and T ≤ 1.
`Real.log ↑N` is carried as an opaque atom; the chain is linear, so a single
`linarith` discharges it. This is a CONDITIONAL assembly: the feeders (the von
Mangoldt lower bound #47, and the prime-power tail decomposition/bound) are
established separately; wiring their conclusions in yields the unconditional
prime-sum Mertens-1 lower bound.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, PRIME-SUM Mertens-1 LOWER-bound assembly. Given the prime-power
tail decomposition `Sl = Sp + T` (with `Sl := Σ_{d≤N} Λ(d)/d`,
`Sp := Σ_{p≤N}(log p)/p`, `T := Sl − Sp` the proper-prime-power tail), the tail
bounds `0 ≤ T` and `T ≤ 1`, and the campaign-verified von Mangoldt lower bound
`log N − 1 ≤ Sl` (#47), the prime sum satisfies `log N − 2 ≤ Sp`. This is the
PRIME-sum form of one direction of Mertens' first theorem. -/
theorem erdos858_prime_mertens1_lower_assembly :
    ∀ (N : ℕ) (Sp Sl T : ℝ), Sl = Sp + T → 0 ≤ T → T ≤ 1 →
      Real.log (N : ℝ) - 1 ≤ Sl → Real.log (N : ℝ) - 2 ≤ Sp := by
  intro N Sp Sl T hSl hT0 hT1 hLow
  linarith

end Erdos858
