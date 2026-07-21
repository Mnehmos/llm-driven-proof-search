/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 aggregation core (Chojecki 2026).

Arithmetic-grid analogue of the §5.3 geometric aggregation core (#144): instantiate
the general-grid aggregation engine (#136) at the arithmetic grid
`v_j = s+(j/K)(t−s)` and weight `h(a) = 1/a`. For `s≤t`, `1<N`, `K>0`, a `δ`-`η`
modulus for `G`, and block width `(t−s)/K ≤ δ`, the true harmonic sum over
`(⌊N^s⌋,⌊N^t⌋]` is within `η·(total harmonic mass)` of the arithmetic block
step-sum — the aggregation input feeding A6-herr's (#163) hAgg hypothesis.

Proof: `hmono2` (affine monotonicity via the difference identity
`(s+(b/K)(t−s))−(s+(a/K)(t−s)) = ((b−a)/K)(t−s)`, avoiding div-monotone lemma-name
uncertainty) derives `hvmono`/`hwidth'`/`hmono_e`; feed `#136` wrapping the `j+1`
arguments in `simp only [Nat.cast_add, Nat.cast_one]` closures (the cast-bridge
lesson from #144); `simp` the output endpoints via `hv0`/`hvK`.

Kernel-verified via the proofsearch MCP:
  episode 79a5cb21-5c5b-4eca-bf8e-17b9fe021a8d,
  problem_version_id da62384f-a762-44e5-aabf-a56246e9f956.
Outcome: kernel_verified / root_kernel_verified (v2 — v1 failed: an unparenthesized
`have hba : T := by linarith` mid-chain swallowed the rest of the `;`-chain as its
own tactic block, per the banked "bare `:= by tac;` swallows the chain" pitfall;
fixed by wrapping `(by linarith)`).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ed0d3d7c7fbb103489a0f60026b78b0eec052afcfc17056ad3ef16d1fac0d6b7.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 aggregation core: `#136` at the arithmetic grid `v_j=s+(j/K)(t−s)`,
weight `1/a` — the aggregation input of A6-herr. Arithmetic-grid analogue of the
§5.3 geometric aggregation core (#144). -/
theorem erdos858_thm12_a6_aggregation_core :
    ∀ (G : ℝ → ℝ) (s t : ℝ) (N K : ℕ) (δ η : ℝ),
      s ≤ t → 1 < (N:ℝ) → 0 < K →
      (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ η) →
      ((t - s)/(K:ℝ) ≤ δ) →
      (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ' ε' : ℝ) (v : ℕ → ℝ),
          1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ' → |G' x - G' y| ≤ ε') →
          (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ') →
          Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
          |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
            - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
          ≤ ε' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
      |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (1/(a:ℝ)))
        - (∑ j ∈ Finset.range K, G (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ))))|
      ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1/(a:ℝ))) := by
  intro G s t N K δ η hst hN hK hmod hwidth h136
  have hts : (0:ℝ) ≤ t - s := by linarith
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKR
  have hstep2 : ∀ a b : ℕ, (s + ((b:ℝ)/(K:ℝ))*(t-s)) - (s + ((a:ℝ)/(K:ℝ))*(t-s)) = ((b:ℝ)-(a:ℝ))/(K:ℝ)*(t-s) := fun a b => by field_simp; ring
  have hmono2 : ∀ a b : ℕ, a ≤ b → (s + ((a:ℝ)/(K:ℝ))*(t-s)) ≤ (s + ((b:ℝ)/(K:ℝ))*(t-s)) := fun a b hab => by have hab' : (a:ℝ) ≤ (b:ℝ) := (by exact_mod_cast hab); have hba : (0:ℝ) ≤ (b:ℝ)-(a:ℝ) := (by linarith); have hnn := mul_nonneg (div_nonneg hba hKR.le) hts; linarith [hstep2 a b, hnn]
  have hvmono : ∀ j : ℕ, s + ((j:ℝ)/(K:ℝ))*(t-s) ≤ s + (((j:ℝ)+1)/(K:ℝ))*(t-s) := fun j => by have h := hmono2 j (j+1) (Nat.le_succ j); push_cast at h; linarith
  have hwidth' : ∀ j : ℕ, j < K → (s + (((j:ℝ)+1)/(K:ℝ))*(t-s)) - (s + ((j:ℝ)/(K:ℝ))*(t-s)) ≤ δ := fun j _ => by have heq : (s + (((j:ℝ)+1)/(K:ℝ))*(t-s)) - (s + ((j:ℝ)/(K:ℝ))*(t-s)) = (t-s)/(K:ℝ) := (by field_simp; ring); rw [heq]; exact hwidth
  have hv0 : s + (((0:ℕ):ℝ)/(K:ℝ))*(t-s) = s := by simp
  have hvK : s + ((K:ℝ)/(K:ℝ))*(t-s) = t := by rw [div_self hKne]; ring
  have hmono_e : Monotone (fun j : ℕ => ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊) := fun a b hab => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN) (hmono2 a b hab))
  have hh : ∀ k : ℕ, 0 ≤ (1:ℝ)/(k:ℝ) := fun k => div_nonneg (by norm_num) (Nat.cast_nonneg k)
  have hbound := h136 G (fun a => (1:ℝ)/(a:ℝ)) N K δ η (fun j => s + ((j:ℝ)/(K:ℝ))*(t-s)) hN hh hmod (fun j => by simp only [Nat.cast_add, Nat.cast_one]; exact hvmono j) (fun j hj => by simp only [Nat.cast_add, Nat.cast_one]; exact hwidth' j hj) hmono_e
  simp only [Nat.cast_add, Nat.cast_one, hv0, hvK] at hbound
  exact hbound

end Erdos858
