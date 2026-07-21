/-
Erdős Problem #858 — §5.4 log-harmonic transfer, discharge atom 1 (Chojecki 2026).

`hW-bridge` (weighted block-sum limit from mass limits): given the fixed-K
weighted-sum limit engine (#100's conclusion at fixed `K`) and the per-block
mass limits (`m_j(N)/log N → 1/K` for each `j < K`), the normalized weighted
block sum converges:

  `(Σ_{j<K} f(j/K)·m_j(N)) / log N  →  Σ_{j<K} f(j/K)·(1/K)`.

This discharges the `hW` hypothesis of the concrete log-harmonic Riemann
theorem (#111). Internal content: the sum/division rearrangement
`(Σ_j c_j·m_j)/L = Σ_j c_j·(m_j/L)` via `Finset.sum_div` + `mul_div_assoc`,
transported along `Tendsto.congr'` + `Filter.Eventually.of_forall`.

Kernel-verified via the proofsearch MCP:
  episode 7b7fa818-ee8f-4c50-bcc3-860b968dffde,
  problem_version_id cfb1d302-a670-45bc-a8e8-0735b4782760.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0ae56f5ffc49d3737417621f9bd854d86272c8b08d14256d5a648fbaf6a4f6b2.
-/
import Mathlib

namespace Erdos858

/-- Discharge atom 1 (hW-bridge): from #100's fixed-K engine + per-block mass
limits, `(Σ_{j<K} f(j/K)·m_j(N))/log N → Σ_{j<K} f(j/K)·(1/K)`. Feeds #111. -/
theorem erdos858_hW_bridge :
    ∀ (f : ℝ → ℝ) (K : ℕ),
      (∀ (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (Lf : ℕ → ℝ),
        (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (Lf j))) →
        Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * Lf j))) →
      (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (1 / (K:ℝ)))) →
      Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (1 / (K:ℝ)))) := by
  intro f K h100 hmass
  have h := h100 (fun j => f ((j:ℝ) / (K:ℝ))) (fun N j => ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) / Real.log (N:ℝ)) (fun _ => 1 / (K:ℝ)) hmass
  have heq : ∀ N : ℕ, (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) / Real.log (N:ℝ))) = (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ) := fun N => by rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => (mul_div_assoc _ _ _).symm)
  exact h.congr' (Filter.Eventually.of_forall heq)

end Erdos858
