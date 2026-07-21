/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 per-block harmonic mass (Chojecki 2026).

`arithmetic-block harmonic mass → (t−s)/K`: instantiating the interval harmonic
mass limit (#99: `(harmonic⌊N^x⌋ − harmonic⌊N^y⌋)/log N → x − y`) at the arithmetic
block endpoints `v_j = s + (j/K)(t−s)`, each block's normalized harmonic mass tends
to the constant block width:

  `(harmonic⌊N^{v_{j+1}}⌋ − harmonic⌊N^{v_j}⌋)/log N → v_{j+1} − v_j = (t−s)/K`.

This supplies the per-block mass hypothesis of the A6-hW discharge (feeding the
interval log-harmonic transfer). Analogue of the §5.3 geometric per-block mass
#139 (there `→ log(t/s)/K` for the `dv/v` measure; here `→ (t−s)/K` for Lebesgue).

Proof: apply #99 at `(v_{j+1}, v_j)`, rewrite the width `v_{j+1} − v_j = (t−s)/K`
(`field_simp` + `ring`, `K ≠ 0`).

Kernel-verified via the proofsearch MCP:
  episode 410a894c-7704-4d38-a390-5d4aeddf2315,
  problem_version_id 510cbbf8-9827-489d-b120-1914ae692e97.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a6cbbd6e37440a92b2d662f2bfb3191d6929001792bb72e36567ab5babeb605b.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 per-block harmonic mass: from #99 (interval harmonic mass), each
arithmetic block `v_j=s+(j/K)(t−s)` has `(harmonic⌊N^{v_{j+1}}⌋−harmonic⌊N^{v_j}⌋)/log N
→ (t−s)/K`. `#99 at (v_{j+1},v_j)` + width `= (t−s)/K` (`field_simp`+`ring`). -/
theorem erdos858_thm12_a6_block_mass :
    ∀ (s t : ℝ),
      (∀ (x y : ℝ), Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ)^x⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^y⌋₊ : ℝ))/Real.log (N:ℝ)) Filter.atTop (nhds (x - y))) →
      ∀ (K : ℕ), 0 < K → ∀ j : ℕ, j < K →
        Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ)^(s+(((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^(s+((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))/Real.log (N:ℝ)) Filter.atTop (nhds ((t-s)/(K:ℝ))) := by
  intro s t h99 K hK j hjK
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hK)
  have hval : (s+(((j:ℝ)+1)/(K:ℝ))*(t-s)) - (s+((j:ℝ)/(K:ℝ))*(t-s)) = (t-s)/(K:ℝ) := by field_simp; ring
  have hlim := h99 (s+(((j:ℝ)+1)/(K:ℝ))*(t-s)) (s+((j:ℝ)/(K:ℝ))*(t-s))
  rw [hval] at hlim
  exact hlim

end Erdos858
