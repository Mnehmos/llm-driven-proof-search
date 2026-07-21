/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, herr discharge / FINAL (Chojecki 2026).

`herr discharge` (final, via #140 mass-normalization): feeding the aggregation
wrapper's `hAgg` output (#145b) and the prime interval mass limit #129
(`mass_N → log t − log s`, `≥ 0` since `s ≤ t`) through the mass-normalized herr
atom #140 yields exactly the `herr` hypothesis of the capstone #141:

  `∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A_N − W_KN| ≤ ε`.

This closes the LAST of the three inputs (`hW` = #142, `hR` = #138∘#97-at-φ,
`herr` = this) of the §5.3 prime-harmonic transfer capstone #141 — grounding it
in the same fully kernel-verified discharge-tree standard as the §5.4 transfer
(#111). The complete §5.3 herr sub-tree:

  herr (#146) ← #140 (mass-normalized) + hAgg (#145b) + #129 (mass limit)
    hAgg (#145b) ← #144 (core) + #145a (small-N) + #135 (width) + #143 (mesh-vanish) + G-modulus
      #144 (core) ← #136 (aggregation) + #137 (grid props) + cast bridge

Proof: `hL0 : 0 ≤ log t − log s` via `rw [← Real.log_div …]; Real.log_nonneg
((one_le_div hs).mpr hst)` (`t/s ≥ 1`); then `exact h140` at the concrete
`A_N`/`W_KN`/`mass_N` lambdas with `L = log t − log s` — β-defeq unifies the
concrete `hAgg` against #140's abstract `hAgg` slot.

Kernel-verified via the proofsearch MCP:
  episode b2aca2d6-8ecd-44e0-b338-f255eb51b3e3,
  problem_version_id f6536acd-1de7-4e46-990b-4fa0de2c241b.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 73d675c8ed316e61e80b4a03205eea5353e15d6aec01de1389a5ff14b0de8860.
-/
import Mathlib

namespace Erdos858

/-- §5.3 herr discharge / FINAL: from #140 (mass-normalized herr), the wrapper's
`hAgg` (#145b), and the prime mass limit #129 (`mass_N → log t − log s ≥ 0`), the
`herr` of capstone #141: `∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A_N − W_KN| ≤ ε`. Closes the last of
#141's three inputs. Proof: `hL0` via `log_div`+`log_nonneg`, then `exact h140` at
the concrete lambdas. -/
theorem erdos858_prime_herr_discharge :
    ∀ (G : ℝ → ℝ) (s t : ℝ), 0 < s → s ≤ t →
      (∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
        0 ≤ L → Filter.Tendsto mass Filter.atTop (nhds L) →
        (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
      (∀ η : ℝ, 0 < η → ∀ᶠ K : ℕ in Filter.atTop, ∀ N : ℕ,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
          - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
        ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) →
      Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) Filter.atTop (nhds (Real.log t - Real.log s)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ (N : ℕ) in Filter.atTop,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
          - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
        ≤ ε := by
  intro G s t hs hst h140 hAgg hmasslim
  have hL0 : (0:ℝ) ≤ Real.log t - Real.log s := by rw [← Real.log_div (ne_of_gt (by linarith : (0:ℝ) < t)) (ne_of_gt hs)]; exact Real.log_nonneg ((one_le_div hs).mpr hst)
  exact h140 (fun N => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) (fun K N => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) (fun N => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) (Real.log t - Real.log s) hL0 hmasslim hAgg

end Erdos858
