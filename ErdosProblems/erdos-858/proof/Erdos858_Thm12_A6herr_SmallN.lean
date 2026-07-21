/-
Erdős Problem #858 — Theorem 1.2 assembly, A6-herr small-N case (Chojecki 2026).

Arithmetic-grid analogue of the verified §5.3 geometric small-N triviality (#145a):
for `0<s≤t`, `(N:ℝ)≤1`, `K>0`, the transfer error bound `|A_N−W_KN|≤η·mass_N`
holds trivially at `N∈{0,1}`, since raising a base in `[0,1]` to a larger exponent
only shrinks it, so every `Finset.Ioc` range (the main range and every arithmetic
sub-block `(⌊N^{v_j}⌋,⌊N^{v_{j+1}}⌋]`) is empty — `A_N=0`, `W_KN=0`, `mass_N=0`,
bound is `0≤0`. Completes the `∀N` quantifier of A6-herr's aggregation hypothesis
(the aggregation core #170 only covers `1<N`).

Proof: `hendp` via `Real.rpow_le_rpow_of_exponent_ge'` (`0≤N≤1`); `hAempty`/
`hblockempty` via `Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono hendp))`; grid
monotonicity (`hvpos`/`hvmono`) via the same difference-identity trick as #170
(avoiding div-monotone lemma-name uncertainty); `hW0` via `Finset.sum_eq_zero`;
`rw`+`simp` close.

Kernel-verified via the proofsearch MCP:
  episode eaa98d82-39b4-46ad-90e5-bfe126595af3,
  problem_version_id 114ff6e4-e514-401d-ab5e-c05f7489b492.
Outcome: kernel_verified / root_kernel_verified (v2 — v1 failed on a mistyped
subscript character: `₉` (U+2089, subscript nine) typed instead of `₊` (U+208A,
subscript plus) in one `⌊⌋₊` occurrence, breaking the `Nat.floor` notation parse;
caught and fixed via a scratch-file byte-level grep audit before resubmitting).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f8402056d50eccbbd412dd1a87787ddfeaea54b696924b5d9fe114d590977a6d.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6-herr small-N case: for `0<s≤t`, `(N:ℝ)≤1`, `K>0`, the arithmetic-
grid transfer error bound holds as `0≤0` (all ranges empty). Arithmetic-grid
analogue of the §5.3 small-N triviality (#145a); covers `N∈{0,1}`, which #170
(`1<N`) excludes. -/
theorem erdos858_thm12_a6_herr_smallN :
    ∀ (G : ℝ → ℝ) (s t : ℝ) (N K : ℕ) (η : ℝ),
      0 < s → s ≤ t → (N:ℝ) ≤ 1 → 0 < K →
      |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (1/(a:ℝ)))
        - (∑ j ∈ Finset.range K, G (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ))))|
      ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1/(a:ℝ))) := by
  intro G s t N K η hs hst hN hK
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hendp : ∀ p q : ℝ, 0 < p → p ≤ q → (N:ℝ)^q ≤ (N:ℝ)^p := fun p q hp hpq => Real.rpow_le_rpow_of_exponent_ge' hNnn hN hp.le hpq
  have hAempty : Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ = ∅ := Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono (hendp s t hs hst)))
  have hvpos : ∀ j : ℕ, 0 < s + ((j:ℝ)/(K:ℝ))*(t-s) := fun j => by have hts : (0:ℝ) ≤ t - s := (by linarith); have hjk : (0:ℝ) ≤ (j:ℝ)/(K:ℝ) := (by positivity); nlinarith [mul_nonneg hjk hts]
  have hvmono : ∀ j : ℕ, s + ((j:ℝ)/(K:ℝ))*(t-s) ≤ s + (((j:ℝ)+1)/(K:ℝ))*(t-s) := fun j => by have hts : (0:ℝ) ≤ t - s := (by linarith); have hKr : (0:ℝ) < (K:ℝ) := (by exact_mod_cast hK); have heq : (s + (((j:ℝ)+1)/(K:ℝ))*(t-s)) - (s + ((j:ℝ)/(K:ℝ))*(t-s)) = (t-s)/(K:ℝ) := (by field_simp; ring); linarith [div_nonneg hts hKr.le, heq]
  have hblockempty : ∀ j : ℕ, Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ = ∅ := fun j => Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_mono (hendp (s + ((j:ℝ)/(K:ℝ))*(t-s)) (s + (((j:ℝ)+1)/(K:ℝ))*(t-s)) (hvpos j) (hvmono j))))
  have hW0 : (∑ j ∈ Finset.range K, G (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ)))) = 0 := Finset.sum_eq_zero (fun j _ => by rw [hblockempty j, Finset.sum_empty, mul_zero])
  rw [hAempty, hW0]
  simp

end Erdos858
