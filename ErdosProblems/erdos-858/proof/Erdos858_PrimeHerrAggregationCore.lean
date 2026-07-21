/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, herr atom B (Chojecki 2026).

`herr aggregation core` (geometric #136 fixed-K,N bound at primes): the fixed
`(K,N)` heart of the §5.3 transfer error. Instantiate the general-grid
aggregation engine (#136, `erdos858_general_grid_aggregation_bound`, taken in its
pre-applied form over its #133/#101/#103 antecedents) at
  - the geometric grid `v_j = s·(t/s)^{j/K}`,
  - the prime weight `h a = if a.Prime then 1/a else 0`,
with the grid's structural properties (monotone, `v_0=s`, `v_K=t`, floor-endpoint
monotone) supplied by #137. For `0 < s ≤ t`, `1 < N`, `0 < K`, a `δ`-`η` modulus
for `G`, and all block widths `≤ δ`, the true prime-harmonic sum over
`(⌊N^s⌋,⌊N^t⌋]` is within `η·(total prime mass)` of the geometric block step-sum:

  `|Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} G(log a/log N)·[a prime]/a − Σ_{j<K} G(v_j)·(prime block mass)|
     ≤ η·(Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} [a prime]/a)`.

The block step-sum matches the canonical `W_KN` of the capstone #141 EXACTLY
(same `((j:ℝ)+1)` upper endpoints).

Proof: `hbound := h136 G (prime wt) N K δ η v hN hh hmod hvmono' hwidth' hmono_e`;
the prime weight is nonneg (`split_ifs <;> positivity`); `hvmono'`/`hwidth'` feed
#137's/`hwidth`'s `(↑j+1)`-form facts into #136's `v (j+1) = ↑(j+1)`-form slots
via `simp only [Nat.cast_add, Nat.cast_one]` (the `↑(j+1) = ↑j+1` cast bridge);
`hmono_e` passes directly (both sides carry `↑j`). Finally
`simp only [Nat.cast_add, Nat.cast_one, hv0, hvK] at hbound` normalizes the output
(upper endpoints `↑(j+1)→↑j+1`, `v_0→s`, `v_K→t`), matching the goal — `exact hbound`.

Kernel-verified via the proofsearch MCP:
  episode ef8c09fb-75ad-43e3-a261-5f277dbf4bee,
  problem_version_id 8c265281-85c8-4782-ba3e-28c7a6acada9.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 59085eeb581e52dce13d92a907541be90ac39d56f2502be5c0376d6508643310.

**Lean lesson**: the `((j+1:ℕ):ℝ)` (from a generic `v (j+1)`) vs `((j:ℝ)+1)`
(from the concrete atoms #135/#137/#139/#141) mismatch — same display, different
term — is bridged BOTH directions by `simp only [Nat.cast_add, Nat.cast_one]`:
inside the arguments fed to #136 (proving `v (j+1) - v j ≤ δ` from the `(↑j+1)`
width), and on #136's output (rewriting the block-sum upper endpoints to match the
canonical `W_KN`). simp's default beta-reduction exposes `Nat.cast (j+1)` under
the `v` lambda for the cast lemmas to fire.
-/
import Mathlib

namespace Erdos858

/-- §5.3 herr atom B (herr aggregation core): #136 at the geometric grid + prime
weight (grid props from #137), for `0<s≤t`, `1<N`, `0<K`, a `δ`-`η` `G`-modulus,
and block widths `≤δ`, gives `|A_N − W_KN| ≤ η·mass_N` — matching the canonical
`W_KN` of #141. Cast bridge `↑(j+1)=↑j+1` via `simp only [Nat.cast_add, Nat.cast_one]`. -/
theorem erdos858_prime_herr_aggregation_core :
    ∀ (G : ℝ → ℝ) (s t : ℝ) (N K : ℕ) (δ η : ℝ),
      0 < s → s ≤ t → 1 < (N:ℝ) → 0 < K →
      (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ η) →
      (∀ j : ℕ, j < K → s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) - s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ δ) →
      (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ' ε' : ℝ) (v : ℕ → ℝ),
          1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ' → |G' x - G' y| ≤ ε') →
          (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ') →
          Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
          |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
            - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
          ≤ ε' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
      (∀ (s' t' : ℝ) (N' K' : ℕ), 0 < s' → s' ≤ t' → 1 < (N':ℝ) → 0 < K' →
          (∀ j : ℕ, s' * (t'/s') ^ ((j:ℝ)/(K':ℝ)) ≤ s' * (t'/s') ^ (((j:ℝ)+1)/(K':ℝ)))
          ∧ s' * (t'/s') ^ (((0:ℕ):ℝ)/(K':ℝ)) = s'
          ∧ s' * (t'/s') ^ (((K':ℕ):ℝ)/(K':ℝ)) = t'
          ∧ Monotone (fun j : ℕ => ⌊(N':ℝ) ^ (s' * (t'/s') ^ ((j:ℝ)/(K':ℝ)))⌋₊)) →
      |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
        - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
      ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) := by
  intro G s t N K δ η hs hst hN hK hmod hwidth h136 h137
  obtain ⟨hvmono, hv0, hvK, hmono_e⟩ := h137 s t N K hs hst hN hK
  have hh : ∀ k : ℕ, 0 ≤ (if k.Prime then (1:ℝ)/(k:ℝ) else 0) := fun k => by split_ifs <;> positivity
  have hbound := h136 G (fun a => if a.Prime then (1:ℝ)/(a:ℝ) else 0) N K δ η (fun j => s * (t/s) ^ ((j:ℝ)/(K:ℝ))) hN hh hmod (fun j => by simp only [Nat.cast_add, Nat.cast_one]; exact hvmono j) (fun j hj => by simp only [Nat.cast_add, Nat.cast_one]; exact hwidth j hj) hmono_e
  simp only [Nat.cast_add, Nat.cast_one, hv0, hvK] at hbound
  exact hbound

end Erdos858
