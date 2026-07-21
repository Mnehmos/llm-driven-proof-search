/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, herr atom C (Chojecki 2026).

`herr small-N triviality` (N ≤ 1 case): for `0 < s ≤ t`, `(N:ℝ) ≤ 1`, `0 < K`,
the transfer error bound `|A_N − W_KN| ≤ η·mass_N` holds trivially, because for
`N ≤ 1` every prime range is empty. Concretely, for `0 ≤ N ≤ 1` and any exponents
`0 < p ≤ q`, `(N:ℝ)^q ≤ (N:ℝ)^p` (`Real.rpow_le_rpow_of_exponent_ge'`, valid for
base `0 ≤ N`, so `N = 0` needs no separate case), hence `⌊N^t⌋ ≤ ⌊N^s⌋` and
`⌊N^{v_{j+1}}⌋ ≤ ⌊N^{v_j}⌋`, making every `Finset.Ioc` empty. So `A_N = 0`,
`W_KN = 0`, `mass_N = 0`, and the bound is `0 ≤ 0`.

This covers the `N ∈ {0,1}` cases that the aggregation core #144 (which needs
`1 < N` for #136/#137) cannot, completing the `∀ N` quantifier of the `herr`
hypothesis of #140 in the wrapper.

Proof: `hendp` = `Real.rpow_le_rpow_of_exponent_ge' hNnn hN hp.le hpq` (pure term);
`hAempty`/`hblockempty` = `Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono …))`
(pure term); `hW0` = `Finset.sum_eq_zero (fun j _ => by rw [hblockempty j,
Finset.sum_empty, mul_zero])`; then `rw [hAempty, hW0]; simp`.

Kernel-verified via the proofsearch MCP:
  episode 01bfd98f-cb71-463c-ae03-3779c8f7529c,
  problem_version_id fb8e65e4-5689-441b-8045-e667ea8d7c6a.
Outcome: kernel_verified / root_kernel_verified (4th submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5acbdff04b3674d2e37e552323f012b04a7de1479d5cf2f57a4cd12aa75d9182.

**Lean lessons**: (1) `Real.rpow_le_rpow_of_exponent_ge'` takes `0 ≤ x` (unlike
`Real.rpow_le_rpow_of_exponent_ge` which needs `0 < x`) — use the primed form to
avoid a `base = 0` case split. (2) The recurring mis-scope bug bit TWICE here:
both a `rcases … · … · …` bullet body AND a `have h := by <intro/apply/exact
sequence>` escaped to the outer goal. Fix BOTH by going pure term-mode (`fun … =>
Finset.Ioc_eq_empty (…)`, `Finset.sum_eq_zero (fun j _ => by …)`), keeping only
single-line inner `by` blocks. Multi-line nested tactic blocks in a submitted
proof term are unreliable; term-mode is the safe default.
-/
import Mathlib

namespace Erdos858

/-- §5.3 herr atom C (small-N triviality): for `0<s≤t`, `(N:ℝ)≤1`, `0<K`, the
transfer bound `|A_N − W_KN| ≤ η·mass_N` holds as `0 ≤ 0` (all prime ranges
empty). Covers `N∈{0,1}`, which the aggregation core #144 (`1<N`) excludes. -/
theorem erdos858_prime_herr_small_N :
    ∀ (G : ℝ → ℝ) (s t : ℝ) (N K : ℕ) (η : ℝ),
      0 < s → s ≤ t → (N:ℝ) ≤ 1 → 0 < K →
      |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0))
        - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))|
      ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) := by
  intro G s t N K η hs hst hN hK
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hts : (1:ℝ) ≤ t/s := (one_le_div hs).mpr hst
  have hendp : ∀ p q : ℝ, 0 < p → p ≤ q → (N:ℝ)^q ≤ (N:ℝ)^p := fun p q hp hpq => Real.rpow_le_rpow_of_exponent_ge' hNnn hN hp.le hpq
  have hvpos : ∀ j : ℕ, 0 < s * (t/s) ^ ((j:ℝ)/(K:ℝ)) := fun j => mul_pos hs (Real.rpow_pos_of_pos hbase _)
  have hAempty : Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ = ∅ := Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono (hendp s t hs hst)))
  have hblockempty : ∀ j : ℕ, Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊ = ∅ := fun j => Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono (hendp (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) (s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ))) (hvpos j) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hts (by rw [add_div]; linarith [div_nonneg (zero_le_one) hKr.le])) hs.le))))
  have hW0 : (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) = 0 := Finset.sum_eq_zero (fun j _ => by rw [hblockempty j, Finset.sum_empty, mul_zero])
  rw [hAempty, hW0]
  simp

end Erdos858
