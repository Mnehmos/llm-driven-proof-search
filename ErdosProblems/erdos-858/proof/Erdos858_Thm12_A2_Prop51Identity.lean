/-
Erdős Problem #858 — Theorem 1.2 assembly, atom A2 (Prop 5.1 frontier identity, Chojecki 2026).

`Proposition 5.1 (exact frontier identity above N^{1/4})`: for `N^{1/4} ≤ K ≤ √N`,

  `S_N(K) = (H_N − H_{⌊√N⌋}) + Σ_{K<a≤⌊√N⌋} (1 − R_N(a))/a`.

This is the direct feeder of the Theorem 1.2 capstone (`M(N) = S_N(K*) = harm + tail`
with `harm = H_N − H_{√N}` (→ ½log N, atom A1) and `tail = Σ(1−R_N)/a`
(→ (∫_{α₂}^{1/2}(1−Φ))·log N, atom A6)).

Assembled (conditional on the frontier facts, each from verified atoms) from:
  (i)   `S_N(K) = H_N − H_K − Σ_{K<a≤N} C_N(a)`   (Prop 3.2 + parent-counting
        `Σ_a C_N(a) = H_N − 1`);
  (ii)  `C_N(a) = R_N(a)/a`  for `a > N^{1/4}`   (Lemma 4.5, `R_N = a·C_N`);
  (iii) `R_N(a) = 0`, so `C_N(a) = 0`, for `a > √N`   (the prime range `a<p≤N/a`
        is empty when `a² > N`);
  (iv)  `H_{√N} − H_K = Σ_{K<a≤√N} 1/a`   (harmonic difference).

Proof: `Σ_{K<a≤N} C_N = Σ_{K<a≤√N} R_N/a` (split at `√N` via
`Finset.sum_Ioc_consecutive`, the `a>√N` part vanishes by (iii); `sum_congr` by (ii)),
`H_N − H_K = (H_N−H_{√N}) + Σ 1/a` (by (iv)), and `Σ 1/a − Σ R_N/a = Σ(1−R_N)/a`
(`Finset.sum_sub_distrib` + `sub_div`); `ring`.

Kernel-verified via the proofsearch MCP:
  episode 02795a1c-2173-4388-a155-cf395f6bad33,
  problem_version_id 653466d4-40a8-4e84-b5d7-8f26c33b76db.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1d4d62a355c9ff8aae75a516f8b6ae219924fb30801ba23a7ee2ad979203c2fb.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 atom A2 (Prop 5.1 exact frontier identity): `S_N(K) = (H_N−H_{⌊√N⌋})
+ Σ_{K<a≤⌊√N⌋}(1−R_N(a))/a` for `N^{1/4}≤K≤√N`, from the Prop 3.2+parent-counting
form, `C_N=R_N/a` above `N^{1/4}`, `R_N=0` above `√N`, and the harmonic difference.
The `M = harm + tail` frontier identity feeding the Theorem 1.2 capstone. -/
theorem erdos858_thm12_prop51_identity :
    ∀ (SN CN RN H : ℕ → ℝ) (K N sqrtN : ℕ),
      K ≤ sqrtN → sqrtN ≤ N →
      SN K = H N - H K - ∑ a ∈ Finset.Ioc K N, CN a →
      (∀ a ∈ Finset.Ioc K sqrtN, CN a = RN a / (a:ℝ)) →
      (∀ a ∈ Finset.Ioc sqrtN N, CN a = 0) →
      H sqrtN - H K = ∑ a ∈ Finset.Ioc K sqrtN, 1/(a:ℝ) →
      SN K = (H N - H sqrtN) + ∑ a ∈ Finset.Ioc K sqrtN, (1 - RN a)/(a:ℝ) := by
  intro SN CN RN H K N sqrtN hKs hsN hSK hCR hC0 hHdiff
  have hsplit : (∑ a ∈ Finset.Ioc K N, CN a) = ∑ a ∈ Finset.Ioc K sqrtN, RN a / (a:ℝ) := by rw [← Finset.sum_Ioc_consecutive CN hKs hsN, Finset.sum_eq_zero hC0, add_zero]; exact Finset.sum_congr rfl hCR
  rw [hSK, hsplit]
  have hH : H N - H K = (H N - H sqrtN) + ∑ a ∈ Finset.Ioc K sqrtN, 1/(a:ℝ) := by rw [← hHdiff]; ring
  rw [hH]
  have hsum : (∑ a ∈ Finset.Ioc K sqrtN, (1 - RN a)/(a:ℝ)) = (∑ a ∈ Finset.Ioc K sqrtN, 1/(a:ℝ)) - (∑ a ∈ Finset.Ioc K sqrtN, RN a/(a:ℝ)) := by rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => sub_div 1 (RN a) (a:ℝ))
  rw [hsum]; ring

end Erdos858
