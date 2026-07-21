/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, hW discharge (Chojecki 2026).

`hW discharge` (fixed-K block-sum limit at the prime-transfer quantities):
instantiate the generic fixed-K weighted-block-sum engine (#100,
`erdos858_weighted_block_sum`) at
  - weights `c j = G(s·(t/s)^{j/K})`  (constant in `N`);
  - block masses `g N j = Σ_{a∈(⌊N^{v_j}⌋,⌊N^{v_{j+1}}⌋]} [a prime]/a`;
  - limits `L j = log(t/s)/K`  (supplied by the geometric per-block prime mass
    limit #139, pre-applied form `hgbm`);
to conclude the `hW` hypothesis of the §5.3 capstone #141: for every `K`,

  `Σ_{j<K} G(v_j)·(prime block mass)  →  Σ_{j<K} G(v_j)·(log(t/s)/K)`   (as N→∞).

Proof: `exact h100 K c g L (per-block)`. The per-block hypothesis is `hgbm K hK j`
for `j ∈ range K`; the needed `0 < K` comes free from `j < K` via
`(Nat.zero_le j).trans_lt (Finset.mem_range.mp hj)`. The `K = 0` case is vacuous
(empty range, both sides `0`, `hgbm` never consulted).

This closes the `hW` gap of the §5.3 assembly: hW is genuinely dischargeable from
the verified engine (#100) + the verified geometric mass limits (#139), which in
turn rest on the interval-Mertens capstone #129. Prime analogue of the §5.4 hW
step (inside #111).

Kernel-verified via the proofsearch MCP:
  episode f40e2b16-a530-4132-b220-1188cee4cc69,
  problem_version_id 3fa3d0c4-88c5-4051-9496-5e9cb155de01.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 37471b01d201000c696b67c317f702c07da2e09f13ae007445b3d8cdb22e1434.
-/
import Mathlib

namespace Erdos858

/-- §5.3 hW discharge: from the generic weighted-block-sum engine (#100) and the
geometric per-block prime mass limit (#139, pre-applied `hgbm`), the fixed-K prime
block step-sum `Σ_{j<K} G(v_j)·(block mass) → Σ_{j<K} G(v_j)·(log(t/s)/K)` — the
`hW` hypothesis of the §5.3 capstone #141. `exact h100 K c g L (fun j hj => hgbm …)`. -/
theorem erdos858_prime_transfer_hW_discharge :
    ∀ (G : ℝ → ℝ) (s t : ℝ),
      (∀ (K : ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (L : ℕ → ℝ),
         (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (L j))) →
         Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * L j))) →
      (∀ (K : ℕ), 0 < K → ∀ j : ℕ, j < K →
          Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) Filter.atTop (nhds (Real.log (t/s) / (K:ℝ)))) →
      ∀ K : ℕ, Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) Filter.atTop (nhds (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ)))) := by
  intro G s t h100 hgbm K
  exact h100 K (fun j => G (s * (t/s) ^ ((j:ℝ)/(K:ℝ)))) (fun N j => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) (fun _ => Real.log (t/s) / (K:ℝ)) (fun j hj => hgbm K ((Nat.zero_le j).trans_lt (Finset.mem_range.mp hj)) j (Finset.mem_range.mp hj))

end Erdos858
