/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 9 (Chojecki 2026).

`geometric per-block prime mass limit`: given the prime interval mass limit
(#129 discharged at primes: for `0 < v ≤ w`, `Σ_{a∈(⌊N^v⌋,⌊N^w⌋]} [a prime]/a
→ log w − log v`) as a hypothesis, for `0 < s ≤ t`, `K > 0`, `j < K`, the
`j`-th geometric block's prime mass converges to the constant block width:

  `Σ_{a∈(⌊N^{v_j}⌋,⌊N^{v_{j+1}}⌋]} [a prime]/a  →  log(t/s)/K`,

`v_j = s·(t/s)^{j/K}`. Proof: instantiate the interval mass limit at
`(v_j, v_{j+1})`, then `log(v_{j+1}) − log(v_j) = [(j+1)/K − j/K]·log(t/s) =
log(t/s)/K` via `Real.log_mul` + `Real.log_rpow` + `ring` (the log-equispacing
of the geometric grid — `ring` closes the field coefficient arithmetic once the
logs are expanded).

This is the per-block mass-limit family feeding the §5.3 `hW` (via #100), the
geometric analogue of #113.

Kernel-verified via the proofsearch MCP:
  episode 5154cb12-450f-4324-9ddf-5a6999c9593a,
  problem_version_id 81f28c8c-504a-42de-b376-f0d57b278861.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0b04f3c8f78548d76b2b3d7f52f630c6bec96c790b42613816ec533c60a26ec8.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 9 (geometric per-block mass limit): from the prime
interval mass limit (#129 at primes), each geometric block's prime mass
`→ log(t/s)/K`. The log-equispacing `log(v_{j+1}) − log(v_j) = log(t/s)/K`
via `log_mul`+`log_rpow`+`ring`. Analogue of #113. -/
theorem erdos858_geometric_block_mass_limit :
    (∀ (v w : ℝ), 0 < v → v ≤ w →
        Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) Filter.atTop (nhds (Real.log w - Real.log v))) →
      ∀ (s t : ℝ) (K : ℕ), 0 < s → s ≤ t → 0 < K → ∀ j : ℕ, j < K →
        Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) Filter.atTop (nhds (Real.log (t/s) / (K:ℝ))) := by
  intro hprimemass s t K hs hst hK j hjK
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hts : (1:ℝ) ≤ t/s := (one_le_div hs).mpr hst
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hinv : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
  have hrp1 : (0:ℝ) < (t/s) ^ ((j:ℝ)/(K:ℝ)) := Real.rpow_pos_of_pos hbase _
  have hrp2 : (0:ℝ) < (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) := Real.rpow_pos_of_pos hbase _
  have hvj_pos : (0:ℝ) < s * (t/s) ^ ((j:ℝ)/(K:ℝ)) := mul_pos hs hrp1
  have hvj_le : s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hts (by rw [add_div]; linarith)) hs.le
  have hlim := hprimemass (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) (s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ))) hvj_pos hvj_le
  have hval : Real.log (s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ))) - Real.log (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) = Real.log (t/s) / (K:ℝ) := by rw [Real.log_mul hs.ne' hrp2.ne', Real.log_mul hs.ne' hrp1.ne', Real.log_rpow hbase, Real.log_rpow hbase]; ring
  rw [hval] at hlim
  exact hlim

end Erdos858
