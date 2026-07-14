/-
Erdős Problem #858 — §5.4 Riemann-sum ladder rung C (Chojecki 2026).

`left_uniform_sum_error`: the fixed-K error bound. Given the uniform partition
identity `∫₀¹ f = Σ_j ∫_{j/K}^{(j+1)/K} f` (rung A, hypothesis) and per-block
rectangle bounds `|∫_{j/K}^{(j+1)/K} f − (1/K)·f(j/K)| ≤ ε/K` (rung B applied with
the block variation, hypothesis), the left-endpoint Riemann sum
`R_K(f) = (1/K) Σ_j f(j/K)` approximates the integral within `ε`:
  `|∫₀¹ f − R_K(f)| ≤ ε`.

Proof: rewrite `∫₀¹ f` by the partition identity, distribute `(1/K)·Σ`, combine into
one `Σ` of per-block errors, then `Finset.abs_sum_le_sum_abs` + `Finset.sum_le_sum`
gives `≤ Σ (ε/K) = K·(ε/K) = ε`. Elementary, no PNT.

Rungs A (#93, partition identity), B (#94, block rectangle error), C (#95, this) are
the analytic core of the durable Riemann-sum theorem; rung D assembles them with
uniform continuity into the convergence `R_K(f) → ∫₀¹ f`.

Kernel-verified via the proofsearch MCP:
  episode ec1baf88-9cee-436d-94cf-526a2fa66d33,
  problem_version_id bd456a50-e338-4c18-a2ae-e4865c5ebadb.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 75d53da9e50d1f4c489667e6c7b9dfe4e99ce89bf4a31e62fa28ef3d1e552656.
-/
import Mathlib

namespace Erdos858

/-- Ladder rung C (fixed-K sum error): given the partition identity (rung A) and
per-block rectangle bounds `≤ ε/K` (rung B), the left-endpoint Riemann sum
`R_K(f) = (1/K) Σ_j f(j/K)` satisfies `|∫₀¹ f − R_K(f)| ≤ ε`. -/
theorem erdos858_left_uniform_sum_error :
    ∀ (f : ℝ → ℝ) (K : ℕ) (ε : ℝ), 0 < K →
      (∫ x in (0:ℝ)..1, f x) = (∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) →
      (∀ j ∈ Finset.range K, |(∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K)| ≤ ε/K) →
      |(∫ x in (0:ℝ)..1, f x) - (1/K) * ∑ j ∈ Finset.range K, f ((j:ℝ)/K)| ≤ ε := by
  intro f K ε hK hpart hblock
  have hKR : (K:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  rw [hpart, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range K, ((∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K))|
      ≤ ∑ j ∈ Finset.range K, |(∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, ε/K := Finset.sum_le_sum hblock
    _ = ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

end Erdos858
