/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 6 (Chojecki 2026).

`general-grid fixed-K,N aggregation bound` (the §5.3 analogue of #109, GENERIC
in the exponent grid `v : ℕ → ℝ`): combining the general per-block bound (#133),
the aggregation theorem (#101), and the discrete partition identity (#103) as
hypotheses, for `G` with a δ-ε modulus, `1 < N`, a nonnegative weight `h`, and
a grid `v` with `v` monotone, block widths `v(j+1) − v(j) ≤ δ` for `j < K`, and
the floor endpoint sequence `e_j = ⌊N^{v j}⌋` monotone:

  `|Σ_{a∈(⌊N^{v 0}⌋,⌊N^{v K}⌋]} G(u_a)·h(a) − Σ_{j<K} G(v j)·(block-j mass)|
     ≤ ε·(total mass)`.

Cleaner than #109: the endpoint VALUES stay symbolic (`⌊N^{v 0}⌋`, `⌊N^{v K}⌋`),
so the geometric grid's `v_0 = s`, `v_K = t` computation is deferred to
instantiation. At the geometric grid `v_j = s·(t/s)^{j/K}` and `h` = the prime
weight, this is the §5.3 counterpart of the §5.4 fixed-K,N error bound — with NO
`1/log N` normalization (the prime masses are already `O(1)`).

Proof: per-block bounds (#133) over `j < K` aggregate via #101; the true sum and
total mass are identified with the block sums via #103 at `e = fun j => ⌊N^{v j}⌋`
(`rw [hpartS, hpartM]` fires cleanly through the lambda-applied block sums, no
`simp`/`push_cast` needed).

Kernel-verified via the proofsearch MCP:
  episode 40eff857-4d24-4241-95cd-52c957509ff3,
  problem_version_id c2cb2b59-e4d1-4a29-8fe5-a69f407c9dab.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7800d72285ebc31524d51990bebc7f0c2f38d3adb3a766f37e292d6a753ba319.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 6 (general-grid fixed-K,N aggregation): from #133 + #101 +
#103 (hypotheses), the true interval sum over `(⌊N^{v 0}⌋, ⌊N^{v K}⌋]` is within
`ε·(total mass)` of the weighted block step-sum, for any monotone grid `v` with
sub-`δ` block widths. Analogue of #109, generic in `v`. -/
theorem erdos858_general_grid_aggregation_bound :
    (∀ (G : ℝ → ℝ) (h : ℕ → ℝ) (N : ℕ) (δ ε v w : ℝ),
        1 < (N:ℝ) → v ≤ w → w - v ≤ δ → (∀ k : ℕ, 0 ≤ h k) →
        (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a)
          - G v * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, h a)|
        ≤ ε * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, h a)) →
      (∀ (K : ℕ) (S w m : ℕ → ℝ) (ε : ℝ),
        (∀ j ∈ Finset.range K, |S j - w j * m j| ≤ ε * m j) →
        |(∑ j ∈ Finset.range K, S j) - (∑ j ∈ Finset.range K, w j * m j)| ≤ ε * (∑ j ∈ Finset.range K, m j)) →
      (∀ (K : ℕ) (e : ℕ → ℕ), Monotone e → ∀ (hh : ℕ → ℝ),
        ∑ j ∈ Finset.range K, ∑ a ∈ Finset.Ioc (e j) (e (j + 1)), hh a = ∑ a ∈ Finset.Ioc (e 0) (e K), hh a) →
      ∀ (G : ℝ → ℝ) (h : ℕ → ℝ) (N K : ℕ) (δ ε : ℝ) (v : ℕ → ℝ),
        1 < (N:ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
        (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K → v (j + 1) - v j ≤ δ) →
        Monotone (fun j => ⌊(N:ℝ) ^ (v j)⌋₊) →
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ) ^ (v 0)⌋₊ ⌊(N:ℝ) ^ (v K)⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a)
          - (∑ j ∈ Finset.range K, G (v j) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ) ^ (v j)⌋₊ ⌊(N:ℝ) ^ (v (j+1))⌋₊, h a))|
        ≤ ε * (∑ a ∈ Finset.Ioc ⌊(N:ℝ) ^ (v 0)⌋₊ ⌊(N:ℝ) ^ (v K)⌋₊, h a) := by
  intro h133 h101 h103 G h N K δ ε v hN hh hmod hvmono hwidth hmono_e
  have hpbAll : ∀ j ∈ Finset.range K, |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(v j)⌋₊ ⌊(N:ℝ)^(v (j+1))⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a) - G (v j) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(v j)⌋₊ ⌊(N:ℝ)^(v (j+1))⌋₊, h a)| ≤ ε * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(v j)⌋₊ ⌊(N:ℝ)^(v (j+1))⌋₊, h a) := fun j hj => h133 G h N δ ε (v j) (v (j+1)) hN (hvmono j) (hwidth j (Finset.mem_range.mp hj)) hh hmod
  have hagg2 := h101 K (fun j => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(v j)⌋₊ ⌊(N:ℝ)^(v (j+1))⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a) (fun j => G (v j)) (fun j => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(v j)⌋₊ ⌊(N:ℝ)^(v (j+1))⌋₊, h a) ε hpbAll
  have hpartS := h103 K (fun j => ⌊(N:ℝ)^(v j)⌋₊) hmono_e (fun a => G (Real.log (a:ℝ) / Real.log (N:ℝ)) * h a)
  have hpartM := h103 K (fun j => ⌊(N:ℝ)^(v j)⌋₊) hmono_e h
  rw [hpartS, hpartM] at hagg2
  exact hagg2

end Erdos858
