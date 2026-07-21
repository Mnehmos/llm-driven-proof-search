/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 hR discharge (Chojecki 2026).

`A6 hR discharge`: instantiates the durable equispaced-Riemann-sum theorem (`#97`)
at the affine pullback `g(x) = f((t−s)x+s)·(t−s)`, using the pullback continuity
(`#167`), the partition identity (`#93`), and the block-variation error bound
(`#96`) as inputs, then identifies the limit `∫₀¹g` with the paper's `∫_s^t f` via
the affine change of variables (`#165`) — producing **exactly** the `hR`
hypothesis the A6 interval log-harmonic transfer capstone (`#160`) needs:

  `(1/K)·Σ_{j<K} f(s+(j/K)(t−s))·(t−s)  →  ∫_s^t f`.

Combined with `herr` (already discharged unconditionally by `#174`) and `hW`
(already self-contained, `#162`+`#164`), **all three inputs of the A6 capstone
now exist for any `f` continuous on `[s,t]` — the interval log-harmonic transfer
(paper's Lemma 5.4, general `[s,t]` form) is unconditional**, modulo a final
composition step tying the three into one call of `#160`.

Proof: `#93`/`#96`/`#97`/`#165` composed as black-box hypotheses (elaboration-cost
lesson from `#174`). A one-line `ring` bridge (`horder : s+x(t−s) = (t−s)x+s`)
reconciles the chain's `s+x(t−s)` convention with `#165`'s `(t−s)x+s` convention,
applied via `funext`/`▸` at both the input (continuity) and output (final sum)
ends. `intervalIntegral.integral_mul_const` pulls the constant `(t−s)` factor out
of `∫₀¹ g` before applying `#165`.

Kernel-verified via the proofsearch MCP:
  episode 15208f70-bd0e-480b-9e3f-f0101728eca7,
  problem_version_id 05b96955-8163-4595-90b3-8770c362c390.
Outcome: kernel_verified / root_kernel_verified (2nd submission — 1st hit a type
mismatch: passing `h96 g` directly as `#97`'s 3rd-hyp argument failed because
`h96`'s own signature still asks for `ContinuousOn` explicitly [mirroring `#96`],
while `#97`'s matching slot does NOT re-ask for it [already consumed as `#97`'s
own 2nd argument]; fixed by wrapping in an inline lambda that closes over
`hgcont` at the right argument position, reshaping `h96`'s partial application to
match `#97`'s expected type exactly).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c0f6d866aa2228d8e0d99ac777a5d70e69ea4de2c8a209bd53b87a616d5dc8c9.

**Lean lesson**: when composing two generic theorems where one's hypothesis-
shaped argument slot omits a hypothesis the OTHER theorem's matching form
includes (already discharged elsewhere in the outer theorem's argument list),
bridge via an inline lambda closing over the extra hypothesis — a bare partial
application (`h96 g`) will NOT reshape itself to drop an argument the target
slot doesn't expect.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 hR discharge: `#97` at the affine pullback `g(x)=f((t−s)x+s)(t−s)`,
identified via `#165` with `∫_s^t f` — the arithmetic-block Riemann sum
`(1/K)Σf(s+(j/K)(t−s))(t−s) → ∫_s^t f`, A6's hR hypothesis. -/
theorem erdos858_thm12_a6_hR_discharge :
    ∀ (f : ℝ → ℝ) (s t : ℝ), s ≤ t → ContinuousOn f (Set.Icc s t) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), s' ≤ t' → ContinuousOn f' (Set.Icc s' t') →
        ContinuousOn (fun x => f' (s' + x*(t'-s')) * (t'-s')) (Set.Icc (0:ℝ) 1)) →
      (∀ (f' : ℝ → ℝ) (K : ℕ), 0 < K → ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        (∑ j ∈ Finset.range K, ∫ x in ((j : ℝ)/K)..(((j : ℝ) + 1)/K), f' x) = ∫ x in (0:ℝ)..1, f' x) →
      (∀ (f' : ℝ → ℝ) (K : ℕ) (ε : ℝ), 0 < K → 0 ≤ ε → ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        ((∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
        (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f' x - f' ((j:ℝ)/K)| ≤ ε) →
        |(∫ x in (0:ℝ)..1, f' x) - (1/K) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)| ≤ ε) →
      (∀ f' : ℝ → ℝ, ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        (∀ (K:ℕ), 0 < K → (∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
        (∀ (K:ℕ) (ε':ℝ), 0 < K → 0 ≤ ε' → ((∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
          (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f' x - f' ((j:ℝ)/K)| ≤ ε') →
          |(∫ x in (0:ℝ)..1, f' x) - (1/K) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)| ≤ ε') →
        Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)) Filter.atTop (nhds (∫ x in (0:ℝ)..1, f' x))) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), (t' - s') * (∫ x in (0:ℝ)..1, f' ((t' - s') * x + s')) = ∫ v in s'..t', f' v) →
      Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (t-s))) Filter.atTop (nhds (∫ v in s..t, f v)) := by
  intro f s t hst hf h167 h93 h96 h97 h165
  have hgcont0 : ContinuousOn (fun x => f (s + x*(t-s)) * (t-s)) (Set.Icc (0:ℝ) 1) := h167 f s t hst hf
  have horder : ∀ x : ℝ, s + x*(t-s) = (t-s)*x+s := fun x => by ring
  have hgeq : (fun x:ℝ => f (s + x*(t-s)) * (t-s)) = (fun x:ℝ => f ((t-s)*x+s) * (t-s)) := funext (fun x => by rw [horder x])
  have hgcont : ContinuousOn (fun x => f ((t-s)*x+s) * (t-s)) (Set.Icc (0:ℝ) 1) := hgeq ▸ hgcont0
  have h93g := h93 (fun x => f ((t-s)*x+s) * (t-s))
  have hpart : ∀ (K:ℕ), 0 < K → (∫ x in (0:ℝ)..1, f ((t-s)*x+s) * (t-s)) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f ((t-s)*x+s) * (t-s) := fun K hK => (h93g K hK hgcont).symm
  have h96g : ∀ (K:ℕ) (ε':ℝ), 0 < K → 0 ≤ ε' → ((∫ x in (0:ℝ)..1, f ((t-s)*x+s) * (t-s)) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f ((t-s)*x+s) * (t-s)) → (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f ((t-s)*x+s) * (t-s) - f ((t-s)*((j:ℝ)/K)+s) * (t-s)| ≤ ε') → |(∫ x in (0:ℝ)..1, f ((t-s)*x+s) * (t-s)) - (1/K) * ∑ j ∈ Finset.range K, f ((t-s)*((j:ℝ)/K)+s) * (t-s)| ≤ ε' := fun K ε' hK hε' hpe hv => h96 (fun x => f ((t-s)*x+s) * (t-s)) K ε' hK hε' hgcont hpe hv
  have htendsto := h97 (fun x => f ((t-s)*x+s) * (t-s)) hgcont hpart h96g
  have hintpull : (∫ x in (0:ℝ)..1, f ((t-s)*x+s) * (t-s)) = (t-s) * (∫ x in (0:ℝ)..1, f ((t-s)*x+s)) := by rw [intervalIntegral.integral_mul_const]; ring
  have hfinal_int : (∫ x in (0:ℝ)..1, f ((t-s)*x+s) * (t-s)) = ∫ v in s..t, f v := by rw [hintpull]; exact h165 f s t
  have htendsto2 : Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f ((t-s)*((j:ℝ)/(K:ℝ))+s) * (t-s))) Filter.atTop (nhds (∫ v in s..t, f v)) := hfinal_int ▸ htendsto
  have heq : (fun K:ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f ((t-s)*((j:ℝ)/(K:ℝ))+s) * (t-s))) = (fun K:ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f (s+((j:ℝ)/(K:ℝ))*(t-s)) * (t-s))) := funext (fun K => by congr 1; exact Finset.sum_congr rfl (fun j _ => by rw [horder ((j:ℝ)/(K:ℝ))]))
  exact heq ▸ htendsto2

end Erdos858
