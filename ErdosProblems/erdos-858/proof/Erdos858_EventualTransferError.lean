/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete instantiation atom 3 (Chojecki 2026).

`eventual transfer error` (the herr hypothesis of the diagonal squeeze): from
  (i)   the fixed-K,N transfer bound (#109's conclusion at a fixed `f`),
  (ii)  a uniform-continuity modulus family for `f` (`∀ ε>0 ∃ δ>0`, global modulus),
  (iii) the eventual harmonic-vs-log bound `harmonic N − harmonic 1 ≤ 2·log N`
        (a consequence of `harmonic N / log N → 1`, #87),
derive: for every `ε > 0`, eventually in `K`, eventually in `N`,

  `|(Σ_{1<a≤N} f(u_a)/a)/log N − (Σ_{j<K} f(j/K)·m_j)/log N| ≤ ε`

— exactly the `herr` hypothesis shape of the diagonal two-limit squeeze (#102).

Proof: pick `δ` for `ε/2` from (ii); pick `M > 1/δ` (`exists_nat_gt`) so that all
`K ≥ max 1 M` satisfy `1/K ≤ δ` (the #97 K-selection pattern via `div_lt_iff₀` /
`div_le_iff₀`); then for `N ≥ 2` (so `log N > 0`) apply (i) at `ε/2`, normalize
by `log N` (`div_sub_div_same`, `abs_div`, `abs_of_pos`, `div_le_iff₀`), and
bound `(harmonic N − harmonic 1) ≤ 2·log N` by (iii), giving `(ε/2)·2·log N =
ε·log N`. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode c4f306f3-ae6b-4e4e-a290-ba3fa592cda9,
  problem_version_id f051245e-a3d1-4073-906b-032fc5698452.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5ffdc6ffadf5248b2108e2a67ebea6037ebb9bca5431aa3b37987180e0a75822.

Lean notes: `div_sub_div_same` (`a/c − b/c = (a−b)/c`) and `abs_div` both exist
in this pin; `2 ≤ N` is definitionally `1 < N` in ℕ (`Nat.lt` is succ-le), so it
can be assigned directly with no cast lemma.
-/
import Mathlib

namespace Erdos858

/-- Concrete instantiation atom 3 (eventual transfer error / herr): from the
fixed-K,N bound (#109), a uniform-continuity family, and the eventual
`harmonic N − harmonic 1 ≤ 2 log N` bound (from #87), for every `ε > 0`,
eventually in `K` and then in `N`, the normalized transfer error is `≤ ε` —
exactly the `herr` hypothesis of the diagonal squeeze (#102). -/
theorem erdos858_eventual_transfer_error :
    ∀ (f : ℝ → ℝ),
      (∀ (N K : ℕ) (δ ε : ℝ),
        1 < (N:ℝ) → 0 < K → (1:ℝ) / (K:ℝ) ≤ δ →
        (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
        |(∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ))
          - (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)))|
        ≤ ε * ((harmonic N : ℝ) - (harmonic 1 : ℝ))) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
      (∀ᶠ N : ℕ in Filter.atTop, (harmonic N : ℝ) - (harmonic 1 : ℝ) ≤ 2 * Real.log (N:ℝ)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, ∀ᶠ N : ℕ in Filter.atTop,
        |(∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε := by
  intro f h109 hUC hharm2 ε hε
  obtain ⟨δ, hδpos, hmod⟩ := hUC (ε/2) (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (1/δ)
  refine Filter.eventually_atTop.mpr ⟨max 1 M, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := le_of_max_le_left hK
  have hK0 : 0 < K := hK1
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK0
  have hMK : (1/δ : ℝ) < (K:ℝ) := lt_of_lt_of_le hM (by exact_mod_cast le_of_max_le_right hK)
  have h1 : 1 < (K:ℝ) * δ := by rw [← div_lt_iff₀ hδpos]; exact hMK
  have hKd : (1:ℝ)/(K:ℝ) ≤ δ := by rw [div_le_iff₀ hKr]; linarith [mul_comm (K:ℝ) δ]
  filter_upwards [hharm2, Filter.eventually_ge_atTop 2] with N hharm hN2
  have hN1n : 1 < N := hN2
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN1n
  have hlogpos : (0:ℝ) < Real.log (N:ℝ) := Real.log_pos hN1
  have hX := h109 N K δ (ε/2) hN1 hK0 hKd hmod
  rw [div_sub_div_same, abs_div, abs_of_pos hlogpos, div_le_iff₀ hlogpos]
  have hmul : ε/2 * ((harmonic N : ℝ) - (harmonic 1 : ℝ)) ≤ ε/2 * (2 * Real.log (N:ℝ)) := mul_le_mul_of_nonneg_left hharm (by linarith)
  linarith [hX, hmul]

end Erdos858
