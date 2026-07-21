/-
Erdős Problem #858 — §5.4 log-harmonic transfer, discharge atom 2 (Chojecki 2026).

`block-mass limit family`: given the normalized-endpoint limit family
(`harmonic⌊N^{j/K}⌋/log N → j/K` for every `j ≤ K` — discharged by #115), each
block's normalized mass converges to the block width:

  for every `j < K`,  `(harmonic⌊N^{(j+1)/K}⌋ − harmonic⌊N^{j/K}⌋)/log N → 1/K`.

This discharges the mass-limit hypothesis of the hW-bridge (#112). Proof:
subtract the endpoint limits at `j+1` and `j` (`push_cast` bridges the
`↑(j+1)` vs `↑j+1` cast forms), evaluate the limit value
(`(j+1)/K − j/K = 1/K` via `div_sub_div_same` + `ring_nf`), and transport the
function form along `a/L − b/L = (a−b)/L` (`div_sub_div_same` again, per-N).

Design note: the hypothesis family deliberately covers `j = 0` too (where the
statement is trivially true), so no case split is needed here — design
hypotheses to be uniform even when their eventual discharge splits into cases.

Kernel-verified via the proofsearch MCP:
  episode 8e322dc5-b0d5-4d02-b605-0904d178630f,
  problem_version_id 79bcd11f-5774-437c-9f14-759aa694074b.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 96a544e633985a380db6c3d2c5cb15ec7508ade5cfdb83cc0f9e1b756ff8c798.
-/
import Mathlib

namespace Erdos858

/-- Discharge atom 2 (block-mass limits): from the `j ≤ K` endpoint family
(#115), each block's normalized mass `→ 1/K`. Feeds the hW-bridge (#112). -/
theorem erdos858_block_mass_limits :
    ∀ (K : ℕ),
      (∀ j : ℕ, j ≤ K → Filter.Tendsto (fun N : ℕ => (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds ((j:ℝ) / (K:ℝ)))) →
      ∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (1 / (K:ℝ))) := by
  intro K hend j hj
  have hjK : j < K := Finset.mem_range.mp hj
  have ht := hend (j+1) (by omega)
  push_cast at ht
  have hs := hend j (by omega)
  have hsub := ht.sub hs
  have hval : ((j:ℝ) + 1) / (K:ℝ) - (j:ℝ) / (K:ℝ) = 1 / (K:ℝ) := by rw [div_sub_div_same]; ring_nf
  rw [hval] at hsub
  exact hsub.congr' (Filter.Eventually.of_forall (fun N => by rw [div_sub_div_same]))

end Erdos858
