/-
Erdős Problem #858 — §5.4 log-harmonic transfer, discharge atom 4 (Chojecki 2026).

`endpoint-limit family` (all `j ≤ K`, including `j = 0`): given #98's
conclusion (for `x > 0`: log-endpoint limit ⟹ harmonic-endpoint limit) and the
composed log-endpoint family (#91's conclusion for `x > 0`), every `j ≤ K`
satisfies

  `harmonic⌊N^{j/K}⌋ / log N  →  j/K`.

For `j ≥ 1`: instantiate the #98∘#91 chain at `x = j/K > 0` (`div_pos`).
For `j = 0`: directly — `⌊N^0⌋ = 1`, `harmonic 1 = 1`, and `1/log N → 0 = 0/K`
(`tendsto_const_nhds.div_atTop` with `log N → ∞`).

This discharges the endpoint-family hypothesis of the block-mass limits (#113),
completing the full §5.4 discharge chain:
  #111 ← {#112 ← {#100, #113 ← #115 ← {#98, #91}},  #97 ← {#93, #96},
          #110 ← {#109 ← {#108 ← {#104,#105,#106,#107}, #101, #103}, hUC, #114 ← #87}}.
Only the uniform-continuity family `hUC` (per concrete `f`) remains external.

Kernel-verified via the proofsearch MCP:
  episode b8ae101c-2669-4f65-a95c-ee2eb9a8b405,
  problem_version_id d7f007ab-2082-416d-911a-605a87cb71e0.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7d0fb866bff46016fd1e0a61c5a2edb49f8d575157c5d91a83b21eaba86d6afb.

**Lean lesson (THIRD pipeline scoping variant, confirmed by submission 1's
failure)**: multi-line `·`-BULLET bodies mis-scope exactly like multi-line
nested-`have` bodies — the bullet's tactics after its first line fail to attach
to the branch goal. RULE (now covering all three variants): every nested tactic
scope — `have` body, `show ... from by` body, bullet body — must be a SINGLE
LINE; anything needing multiple tactics gets hoisted to a top-level single-line
`have` BEFORE the branching point, with `▸`-transport (`hj0 ▸ hzero0`) to move
pre-proven instances into branch goals.
-/
import Mathlib

namespace Erdos858

/-- Discharge atom 4 (endpoint family, `j ≤ K` including `j = 0`): from the
#98∘#91 chain (for `x > 0`) plus the trivial `j = 0` instance,
`harmonic⌊N^{j/K}⌋/log N → j/K` for every `j ≤ K`. Feeds #113. -/
theorem erdos858_endpoint_family :
    ∀ (K : ℕ), 0 < K →
      (∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x) → Filter.Tendsto (fun N : ℕ => (harmonic (⌊(N:ℝ)^x⌋₊) : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds x)) →
      (∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x)) →
      ∀ j : ℕ, j ≤ K → Filter.Tendsto (fun N : ℕ => (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds ((j:ℝ) / (K:ℝ))) := by
  intro K hK h98 h91x j hjK
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have h1q : (harmonic 1 : ℚ) = 1 := by rw [show (1:ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero]; norm_num
  have h1r : (harmonic 1 : ℝ) = 1 := by exact_mod_cast h1q
  have hlogT : Filter.Tendsto (fun N : ℕ => Real.log (N:ℝ)) Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero0 : Filter.Tendsto (fun N : ℕ => (harmonic ⌊(N:ℝ) ^ (((0:ℕ):ℝ) / (K:ℝ))⌋₊ : ℝ) / Real.log (N:ℝ)) Filter.atTop (nhds (((0:ℕ):ℝ) / (K:ℝ))) := by simp only [Nat.cast_zero, zero_div, Real.rpow_zero, Nat.floor_one, h1r]; exact tendsto_const_nhds.div_atTop hlogT
  by_cases hj0 : j = 0
  · exact hj0 ▸ hzero0
  · exact h98 ((j:ℝ)/(K:ℝ)) (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hj0) hKr) (h91x ((j:ℝ)/(K:ℝ)) (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hj0) hKr))

end Erdos858
