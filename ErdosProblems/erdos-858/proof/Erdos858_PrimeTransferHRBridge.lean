/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 8 (Chojecki 2026).

`hR bridge` (geometric R_K → integral): given the durable Riemann-sum limit
(#97's conclusion) for the pulled-back integrand `φ(x) = log(t/s)·G(s·(t/s)^x)`,
i.e. `(1/K)·Σ_{j<K} φ(j/K) → L`, the geometric Riemann-Stieltjes step-sum

  `R_K = Σ_{j<K} G(s·(t/s)^{j/K})·(log(t/s)/K)`

also converges to `L`. Proof: the pointwise identity `R_K = (1/K)·Σ_{j<K} φ(j/K)`
(since `G(v_j)·(log(t/s)/K) = (1/K)·log(t/s)·G(v_j) = (1/K)·φ(j/K)`) via
`Finset.mul_sum` + `ring`, transported along `Tendsto.congr'`.

With `L = ∫₀¹ φ` (the durable #97 target), this is the `R_K → L` input of the
§5.3 diagonal squeeze, and by the geometric change of variables
`L = ∫_s^t G(v)/v dv` — the §5.3 prime-harmonic Riemann-sum limit.

Kernel-verified via the proofsearch MCP:
  episode e12a9946-58d1-434b-8c56-c4545fed0912,
  problem_version_id 5c293a6b-168d-4475-840c-deed31c985ae.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7b1b977d41a60a84a9b2e7023e743fd668be1b12bda03e90bc56748bf2112863.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 8 (hR bridge): from #97's limit at `φ = log(t/s)·G(s·(t/s)^·)`,
`Σ_{j<K} G(s·(t/s)^{j/K})·(log(t/s)/K) → L`. Same `Finset.mul_sum`+`ring` bridge
as #111/#112. -/
theorem erdos858_prime_transfer_hR_bridge :
    ∀ (G : ℝ → ℝ) (s t L : ℝ),
      Filter.Tendsto (fun K : ℕ => (1 / (K:ℝ)) * ∑ j ∈ Finset.range K, (Real.log (t/s) * G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))))) Filter.atTop (nhds L) →
      Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ))) Filter.atTop (nhds L) := by
  intro G s t L h97
  have hEq : ∀ K : ℕ, (1 / (K:ℝ)) * ∑ j ∈ Finset.range K, (Real.log (t/s) * G (s * (t/s) ^ ((j:ℝ)/(K:ℝ)))) = ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ)) := fun K => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  exact h97.congr' (Filter.Eventually.of_forall hEq)

end Erdos858
