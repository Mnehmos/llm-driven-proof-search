/-
Erdős Problem #858 — Theorem 1.2 assembly, A6-hR discharge (Chojecki 2026).

`interval Riemann step-sum → integral`: the `hR` input of the interval log-harmonic
transfer capstone A6. Given #97's conclusion at the linear pullback
`g(x) = f(s + x(t−s))·(t−s)`, i.e. `(1/K)·Σ_{j<K} g(j/K) → L`, the arithmetic-block
step-sum `Σ_{j<K} f(s+(j/K)(t−s))·((t−s)/K)` also tends to `L`. With `L = ∫₀¹ g =
∫_s^t f` (linear change of variables), this is exactly `hR`.

Proof: the pointwise identity `Σ_j f(v_j)·((t−s)/K) = (1/K)·Σ_j (f(v_j)·(t−s))`
(`Finset.mul_sum` + `ring`), transported by `Tendsto.congr'` — the same bridge as
the §5.3 hR (#138).

Kernel-verified via the proofsearch MCP:
  episode 25310c3e-0dc9-47cd-95eb-e2ab67505f75,
  problem_version_id 0d325c52-1261-4f8e-af93-9b3703525473.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash dee0f4d49d571e0a801c91b0a92f19bcca18e162ad637cf4e22db9543424a398.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6-hR discharge: the interval right-Riemann step-sum
`Σ_{j<K} f(s+(j/K)(t−s))·((t−s)/K) → L`, from #97's conclusion at the pullback
`g(x)=f(s+x(t−s))·(t−s)`. `Finset.mul_sum`+`ring`+`Tendsto.congr'` (mirror of #138). -/
theorem erdos858_thm12_a6_hR :
    ∀ (f : ℝ → ℝ) (s t L : ℝ),
      Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (t-s))) Filter.atTop (nhds L) →
      Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((t-s)/(K:ℝ))) Filter.atTop (nhds L) := by
  intro f s t L h97
  have hEq : ∀ K : ℕ, (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (t-s)) = ∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((t-s)/(K:ℝ)) := fun K => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  exact h97.congr' (Filter.Eventually.of_forall hEq)

end Erdos858
