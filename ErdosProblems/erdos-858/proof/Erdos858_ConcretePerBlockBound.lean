/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete instantiation atom 1 (Chojecki 2026).

`concrete per-block sum bound`: combining the block-membership bound (#104),
block oscillation bound (#106), weighted pointwise-to-sum bound (#105), and the
harmonic-difference-as-sum connector (#107) as hypotheses (conditional
assembly, since problem_versions cannot cross-reference), derives the concrete
per-block sum bound needed for the log-harmonic transfer: for `f` with a
δ-ε modulus of continuity at scale `1/K≤δ`, `N>1`, `K>0`, `j<K`, the true
partial sum over block `j` is within `ε·mass` of the weighted approximation
`f(j/K)·mass`, where `mass = harmonic(⌊N^{(j+1)/K}⌋) − harmonic(⌊N^{j/K}⌋)`.
This is the exact per-block hypothesis format needed by the aggregation
theorem (#101) for the full concrete log-harmonic Riemann theorem.

Proof: the pointwise oscillation bound for `a` in the block follows from
#104 + #106 (pure term-mode composition); the weighted pointwise-to-sum
bound (#105) instantiated with `g a = f(u_a)`, `h a = 1/a`, `c = f(j/K)` gives
the sum-form error bound (normalized from `g·h` to `f(u_a)/a` via
`mul_one_div`); the block-endpoint monotonicity `e_0 ≤ e_1` follows from
`Nat.floor_mono ∘ Real.rpow_le_rpow_of_exponent_le`; and #107 converts the
mass sum `Σ 1/a` into the harmonic difference. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode f7d4edf1-411d-487e-91ea-412567ba8d2f,
  problem_version_id f3c9521f-0275-4cec-8164-7805d1061456.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b458b72369c0103666495e73bf8415f24d2d353ae1dd37b6103d79909999fd3b.

**Lean lesson (recurred a 3rd time this session — must be applied
mechanically, not just recalled)**: the multi-line nested `have := by\n  ...`
scoping bug struck again on the FIRST draft of this atom, on a fresh `have`
that looked nothing like the earlier failures. Working rule: default to PURE
TERM-MODE for any `have` whose proof is just function application
(`fun a ha => ...`); when a `by` is unavoidable it must be either a single
tactic, or a semicolon-chain with ZERO nested `have`/`show...from...by`
sub-blocks that themselves need more than one tactic — if a sub-fact needs 2+
tactics, factor it out as its OWN top-level `have` (single-line) BEFORE the
`have` that uses it, never inline it inside another tactic block.
-/
import Mathlib

namespace Erdos858

/-- Concrete instantiation atom 1 (concrete per-block sum bound): assembling
#104+#105+#106+#107 (as hypotheses), the true block-j sum is within `ε·mass`
of `f(j/K)·mass`, `mass = harmonic(⌊N^{(j+1)/K}⌋) − harmonic(⌊N^{j/K}⌋)` — the
exact per-block hypothesis format the aggregation theorem (#101) needs. -/
theorem erdos858_concrete_per_block_bound :
    (∀ (N K j : ℕ), 1 < (N:ℝ) → 0 < K → j < K → ∀ (a : ℕ),
        a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊) →
        (j:ℝ) / (K:ℝ) < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ ((j:ℝ) + 1) / (K:ℝ)) →
      (∀ (f : ℝ → ℝ) (K j : ℕ) (δ ε : ℝ), 0 < K → (1:ℝ) / (K:ℝ) ≤ δ →
        (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
        ∀ u : ℝ, (j:ℝ) / (K:ℝ) < u → u ≤ ((j:ℝ) + 1) / (K:ℝ) →
        |f u - f ((j:ℝ) / (K:ℝ))| ≤ ε) →
      (∀ (s : Finset ℕ) (g h : ℕ → ℝ) (c ε : ℝ),
        (∀ a ∈ s, |g a - c| ≤ ε) → (∀ a ∈ s, 0 ≤ h a) →
        |(∑ a ∈ s, g a * h a) - c * (∑ a ∈ s, h a)| ≤ ε * (∑ a ∈ s, h a)) →
      (∀ m n : ℕ, m ≤ n →
        (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
      ∀ (f : ℝ → ℝ) (N K j : ℕ) (δ ε : ℝ),
        1 < (N:ℝ) → 0 < K → j < K → (1:ℝ) / (K:ℝ) ≤ δ →
        (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
        |(∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ))
          - f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))|
        ≤ ε * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) := by
  intro hblock hosc hweighted hharmdiff f N K j δ ε hN hK hj hKd hmod
  set e0 := ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ with he0
  set e1 := ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ with he1
  have hpt : ∀ a ∈ Finset.Ioc e0 e1, |f (Real.log (a:ℝ)/Real.log (N:ℝ)) - f ((j:ℝ)/(K:ℝ))| ≤ ε := fun a ha => hosc f K j δ ε hK hKd hmod (Real.log (a:ℝ)/Real.log (N:ℝ)) (hblock N K j hN hK hj a ha).1 (hblock N K j hN hK hj a ha).2
  have hhpos : ∀ a ∈ Finset.Ioc e0 e1, (0:ℝ) ≤ 1/(a:ℝ) := fun a _ => by positivity
  have hkey := hweighted (Finset.Ioc e0 e1) (fun a => f (Real.log (a:ℝ)/Real.log (N:ℝ))) (fun a => 1/(a:ℝ)) (f ((j:ℝ)/(K:ℝ))) ε hpt hhpos
  have hkey2 : |(∑ a ∈ Finset.Ioc e0 e1, f (Real.log (a:ℝ)/Real.log (N:ℝ)) / (a:ℝ)) - f ((j:ℝ)/(K:ℝ)) * (∑ a ∈ Finset.Ioc e0 e1, (1:ℝ)/(a:ℝ))| ≤ ε * (∑ a ∈ Finset.Ioc e0 e1, (1:ℝ)/(a:ℝ)) := by simpa only [mul_one_div] using hkey
  have hexp_le : (j:ℝ)/(K:ℝ) ≤ ((j:ℝ)+1)/(K:ℝ) := by rw [show ((j:ℝ)+1)/(K:ℝ) = (j:ℝ)/(K:ℝ) + 1/(K:ℝ) from add_div (j:ℝ) 1 (K:ℝ)]; linarith [show (0:ℝ) ≤ 1/(K:ℝ) from by positivity]
  have hmono : e0 ≤ e1 := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (N:ℝ)) hexp_le)
  have hmasseq := (hharmdiff e0 e1 hmono).symm
  rw [hmasseq] at hkey2
  exact hkey2

end Erdos858
