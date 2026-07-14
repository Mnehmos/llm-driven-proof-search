/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete assembly atom 1/3 (Chojecki 2026).

`discrete block-partition sum identity` (Ioc telescoping): for a fixed number of
blocks `K` and a monotone nat-valued endpoint sequence `e : ℕ → ℕ` (e.g.
`e j = ⌊N^{j/K}⌋₊`), the sum of block sums over `Finset.Ioc (e j) (e (j+1))` for
`j` in `range K` telescopes to the single sum over `Finset.Ioc (e 0) (e K)`:
  `Σ_{j<K} Σ_{a ∈ Ioc (e j) (e (j+1))} h a  =  Σ_{a ∈ Ioc (e 0) (e K)} h a`.

Stated generically (no `N`, `K`, `log`, or `rpow` baked in), this is the discrete
counterpart of the continuous partition identity already used for the pure
Riemann-sum theorem (#93, `intervalIntegral.sum_integral_adjacent_intervals`), and
is deliberately reusable: instantiated with `e j = ⌊N^{j/K}⌋₊` it expresses the true
log-harmonic sum `Σ_{1<a≤N} f(u_a)/a` as a sum of block sums (toward Theorem 1.2);
instantiated with a prime-counting endpoint sequence it will serve the analogous
§5.3 prime-harmonic transfer without modification — the "convergence engine" is
shared, only the block-mass sequence changes.

Proof: induction on `K`. Base case both sides are sums over the empty range/`Ioc x x`
(`simp`). Successor case: `Finset.sum_range_succ` peels off the last block, the
inductive hypothesis handles the first `K` blocks, and `Finset.sum_Ioc_consecutive`
(the telescoping law `(Σ_{Ioc m n} f) + (Σ_{Ioc n k} f) = Σ_{Ioc m k} f` for `m≤n≤k`)
glues it to the new block, using monotonicity of `e` for the two order hypotheses.
Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 71b9c23b-beb2-4727-a4c8-3759baa21963,
  problem_version_id 4cd2fc14-97d7-4e87-abef-581c706cff6f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 77de62f60b93c43128769c28b39de102eaff115feed664ff16fff299d9cf145d.
-/
import Mathlib

namespace Erdos858

/-- Concrete assembly atom 1/3 (discrete block-partition sum identity / Ioc
telescoping): a finite sum over `K` adjacent `Ioc`-blocks of a monotone nat
endpoint sequence `e` equals the single sum over the outer interval. Generic in
`e` and `h` — reusable for both the log-harmonic transfer (`e j = ⌊N^{j/K}⌋₊`) and
the §5.3 prime-harmonic transfer. Proof: induction + `Finset.sum_Ioc_consecutive`. -/
theorem erdos858_block_partition_sum :
    ∀ (K : ℕ) (e : ℕ → ℕ), Monotone e → ∀ (h : ℕ → ℝ),
      ∑ j ∈ Finset.range K, ∑ a ∈ Finset.Ioc (e j) (e (j + 1)), h a = ∑ a ∈ Finset.Ioc (e 0) (e K), h a := by
  intro K e he h
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ioc_consecutive h (he (Nat.zero_le K)) (he (Nat.le_succ K))

end Erdos858
