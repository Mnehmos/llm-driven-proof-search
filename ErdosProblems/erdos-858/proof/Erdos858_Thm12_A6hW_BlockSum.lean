/-
Erdős Problem #858 — Theorem 1.2 assembly, A6-hW discharge (Chojecki 2026).

`fixed-K harmonic-weighted block sum → step-sum`: the `hW` input of the interval
log-harmonic transfer capstone A6. Instantiating the generic weighted-block-sum
engine (#100) at weights `c_j = f(s+(j/K)(t−s))`, normalized block masses
`g N j = (harmonic⌊N^{v_{j+1}}⌋ − harmonic⌊N^{v_j}⌋)/log N` (`→ (t−s)/K`, from #99
at the arithmetic block endpoints `v_j = s+(j/K)(t−s)`), and limits `L_j = (t−s)/K`,
then for every `K`,

  `(Σ_{j<K} f(v_j)·(harmonic⌊N^{v_{j+1}}⌋ − harmonic⌊N^{v_j}⌋))/log N
     → Σ_{j<K} f(v_j)·((t−s)/K)`.

Proof: apply #100; the `W`-form `(Σ …)/log N` equals `Σ (…/log N)` (`Finset.sum_div`
+ `mul_div_assoc`, via `simp only`), transported by `Tendsto.congr'`; `0 < K` comes
free from `j ∈ range K`.

Kernel-verified via the proofsearch MCP:
  episode 26f6a22d-2024-4400-9c08-aa3c5878290d,
  problem_version_id 7c7007e9-96a9-4413-a306-566c0dc768a3.
Outcome: kernel_verified / root_kernel_verified (2nd submission; the `W`-form is a
`fun N => …` applied redex — `simp only [Finset.sum_div, mul_div_assoc]` beta-reduces
and normalizes both sides where a bare `rw [Finset.sum_div]` could not find the pattern).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 6711aec59a67fab579d51691f3fb4a520442075760ebbd4268e90bae1d4a3e9a.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6-hW discharge: `(Σ_{j<K} f(v_j)·(harmonic block mass))/log N →
Σ_{j<K} f(v_j)·((t−s)/K)` from #100 + the #99 arithmetic-block masses. `simp only
[Finset.sum_div, mul_div_assoc]` bridges the `(Σ)/log N` vs `Σ(/log N)` form. -/
theorem erdos858_thm12_a6_hW :
    ∀ (f : ℝ → ℝ) (s t : ℝ),
      (∀ (K : ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (L : ℕ → ℝ),
         (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (L j))) →
         Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * L j))) →
      (∀ (K : ℕ), 0 < K → ∀ j : ℕ, j < K →
         Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1) / (K:ℝ)) * (t - s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ) / (K:ℝ)) * (t - s))⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds ((t - s) / (K:ℝ)))) →
      ∀ K : ℕ, Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((t-s)/(K:ℝ)))) := by
  intro f s t h100 hmass K
  have key := h100 K (fun j => f (s + ((j:ℝ)/(K:ℝ))*(t-s))) (fun N j => ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ)) / Real.log (N:ℝ)) (fun _ => (t-s)/(K:ℝ)) (fun j hj => hmass K ((Nat.zero_le j).trans_lt (Finset.mem_range.mp hj)) j (Finset.mem_range.mp hj))
  refine key.congr' (Filter.Eventually.of_forall (fun N => ?_))
  simp only [Finset.sum_div, mul_div_assoc]

end Erdos858
