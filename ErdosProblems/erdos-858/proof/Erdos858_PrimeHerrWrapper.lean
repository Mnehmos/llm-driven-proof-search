/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, herr atom D (Chojecki 2026).

`herr aggregation wrapper` (∀η, ∀ᶠK, ∀N bound): assembles the eventual transfer
error `∀ η>0, ∀ᶠ K, ∀ N, |A_N − W_KN| ≤ η·mass_N` — exactly the `hAgg` hypothesis
of #140 — from the verified pieces:
  - the aggregation core #144 (pre-applied over `G,s,t` and #136/#137): the
    fixed-`(K,N)` bound for `1 < N` under a `δ`-`η` modulus and block widths `≤ δ`;
  - the small-N triviality #145a: `N ≤ 1 ⟹ 0 ≤ 0`;
  - the geometric block width bound #135;
  - the mesh-vanishing #143 (eventually every mesh factor `≤ δ`);
  - the `G`-modulus family.

Proof: given `η`, take `δ` from the modulus family; `filter_upwards` on
`eventually_gt_atTop 0` and `hmeshvanish δ`; for each large `K` and any `N`, split
on `1 < N` — apply #144 with `hwidth = fun j hj => le_trans (h135 …) hmesh`
(width ≤ mesh factor ≤ δ) — vs `N ≤ 1` (apply #145a). Elementary.

This is the `hAgg` input of the herr; #146 feeds it through #140 to obtain the
`herr` of capstone #141.

Kernel-verified via the proofsearch MCP:
  episode 48ead24d-6aab-4cdb-a373-771dd8fb6d65,
  problem_version_id e7b5ac8e-3787-4be3-808b-19dc1ce61083.
Outcome: kernel_verified / root_kernel_verified (2nd submission; `le_of_not_lt` →
`not_lt.mp`).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash df8046f0017e2904fdd04f3aac8b2a63afb572c2ac1de8c32dc21000ebce66f1.

**Lean lesson**: `le_of_not_lt` is not in this pin — use `not_lt.mp` (`¬ a < b →
b ≤ a`), the `.mp` companion of the already-used `not_lt.mpr`.
-/
import Mathlib

namespace Erdos858

/-- §5.3 herr atom D (aggregation wrapper): from #144 (core), #145a (small-N),
#135 (width), #143 (mesh-vanish), and the `G`-modulus family, the eventual bound
`∀ η>0, ∀ᶠ K, ∀ N, |A_N − W_KN| ≤ η·mass_N` — the `hAgg` input of #140. Proof:
`filter_upwards` + `by_cases 1 < N` (apply #144 or #145a). -/
theorem erdos858_prime_herr_wrapper :
    ∀ (G : ℝ → ℝ) (s t : ℝ), 0 < s → s ≤ t →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ K : ℕ in Filter.atTop, t * ((t/s) ^ ((1:ℝ)/(K:ℝ)) - 1) ≤ δ) →
      (∀ (s' t' : ℝ), 0 < s' → s' ≤ t' → ∀ (K : ℕ), 0 < K → ∀ (j : ℕ), j < K →
        s' * (t'/s') ^ (((j:ℝ)+1)/(K:ℝ)) - s' * (t'/s') ^ ((j:ℝ)/(K:ℝ)) ≤ t' * ((t'/s') ^ ((1:ℝ)/(K:ℝ)) - 1)) →
      (∀ (N K : ℕ) (δ η : ℝ), 1 < (N:ℝ) → 0 < K →
        (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ η) →
        (∀ j : ℕ, j < K → s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) - s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ δ) →
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
          - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
        ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) →
      (∀ (N K : ℕ) (η : ℝ), (N:ℝ) ≤ 1 → 0 < K →
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
          - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
        ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) →
      ∀ η : ℝ, 0 < η → ∀ᶠ K : ℕ in Filter.atTop, ∀ N : ℕ,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
          - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
        ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) := by
  intro G s t hs hst hmodfam hmeshvanish h135 h144 h145a η hη
  obtain ⟨δ, hδ0, hδ⟩ := hmodfam η hη
  filter_upwards [Filter.eventually_gt_atTop 0, hmeshvanish δ hδ0] with K hK hmesh
  intro N
  by_cases hN : 1 < (N:ℝ)
  · exact h144 N K δ η hN hK hδ (fun j hj => le_trans (h135 s t hs hst K hK j hj) hmesh)
  · exact h145a N K η (not_lt.mp hN) hK

end Erdos858
