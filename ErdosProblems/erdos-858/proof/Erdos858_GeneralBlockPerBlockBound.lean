/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 3 (Chojecki 2026).

`general-block weighted per-block bound` (the §5.3 analogue of #108, GENERIC in
the weight `h`): combining the general block-membership bound (#131), the
general oscillation bound (#132), and the weighted pointwise-to-sum bound (#105)
as hypotheses, for `G` with a δ-ε modulus, `1 < N`, exponents `v ≤ w` with
`w − v ≤ δ`, and any nonnegative weight `h : ℕ → ℝ`:

  `|Σ_{a∈(⌊N^v⌋,⌊N^w⌋]} G(log a/log N)·h(a) − G(v)·Σ h(a)|  ≤  ε·Σ h(a)`.

The membership bound (#131) holds for EVERY `a` in the block regardless of
primality, so `g(a) = G(log a/log N)` is within `ε` of `G(v)` on all of the
block — no prime-specific handling is needed in the analytic step. Instantiating
`h(a) = (if a.Prime then 1/a else 0)` gives the prime per-block bound of the
§5.3 prime-harmonic Riemann-sum argument.

Kernel-verified via the proofsearch MCP:
  episode 4ac828f5-e46d-4ed5-ad5e-071a2dc791d1,
  problem_version_id 61c9a343-8d1b-4718-88da-af05b978c837.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f27ae804fd03ecf437ca478a4ffe2cd2e8da6e1e0889c6781fda4792767323ba.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 3 (general per-block bound, generic weight `h ≥ 0`): from
#131 + #132 + #105 (hypotheses), the true block sum `Σ G(u_a)·h(a)` is within
`ε·Σh` of `G(v)·Σh`. Prime case: `h = [prime]·1/a`. Analogue of #108. -/
theorem erdos858_general_block_per_block_bound :
    (∀ (N : ℕ) (v w : ℝ), 1 < (N:ℝ) → ∀ a : ℕ,
        a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊ →
        v < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ w) →
      (∀ (G : ℝ → ℝ) (δ ε v w : ℝ),
        (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
        v ≤ w → w - v ≤ δ →
        ∀ u : ℝ, v < u → u ≤ w → |G u - G v| ≤ ε) →
      (∀ (s : Finset ℕ) (g h : ℕ → ℝ) (c ε : ℝ),
        (∀ a ∈ s, |g a - c| ≤ ε) → (∀ a ∈ s, 0 ≤ h a) →
        |(∑ a ∈ s, g a * h a) - c * (∑ a ∈ s, h a)| ≤ ε * (∑ a ∈ s, h a)) →
      ∀ (G : ℝ → ℝ) (h : ℕ → ℝ) (N : ℕ) (δ ε v w : ℝ),
        1 < (N:ℝ) → v ≤ w → w - v ≤ δ → (∀ k : ℕ, 0 ≤ h k) →
        (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a)
          - G v * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, h a)|
        ≤ ε * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, h a) := by
  intro h131 h132 h105 G h N δ ε v w hN hvw hwv hh hmod
  have hpt : ∀ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, |G (Real.log (a:ℝ) / Real.log (N:ℝ)) - G v| ≤ ε := fun a ha => h132 G δ ε v w hmod hvw hwv (Real.log (a:ℝ) / Real.log (N:ℝ)) (h131 N v w hN a ha).1 (h131 N v w hN a ha).2
  have hhpos : ∀ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, (0:ℝ) ≤ h a := fun a _ => hh a
  exact h105 (Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊) (fun a => G (Real.log (a:ℝ) / Real.log (N:ℝ))) h (G v) ε hpt hhpos

end Erdos858
