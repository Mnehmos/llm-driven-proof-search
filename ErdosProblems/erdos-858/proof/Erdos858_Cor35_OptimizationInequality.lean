/-
  Erdős problem #858 — Chojecki 2026, Corollary 3.5 optimization inequality.

  Paper ref:            Cor 3.5 optimization inequality
  Atom:                 cor35_optimization_inequality
  problem_version_id:   4bf1cc17-5c23-4129-92b8-bad8248a352d
  episode_id:           b4ea3f69-67b6-4212-9a73-e95d63417c73
  outcome:              kernel_verified (root_proved, 1 submission)
  root_statement_hash:  67dcdcfdbd786eb2c826c9e652607ca1e2e64b0e9008a02e73648b56fc6dfa9b
  toolchain:            leanprover/lean4:v4.32.0-rc1
                        mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56

  Math:
    In the sign theorem's consequence, the continuation set [1,K] is optimal.
    For the frontier increments q with q(a) ≥ 0 on [1,K] and q(a) ≤ 0 for a > K,
    any subset D ⊆ [1,M] satisfies  Σ_{a∈D} q(a) ≤ Σ_{a∈[1,K]} q(a).
    Proof: split D by (· ≤ K). The (> K) part is a sum of nonpositive terms, so
    it is ≤ 0. The (≤ K) part is a subset of [1,K] (using D ⊆ [1,M], a ≤ K, a ≥ 1)
    and the missing terms are nonnegative, giving
    Σ_{a∈D, a≤K} q(a) ≤ Σ_{a∈[1,K]} q(a). Combine with linarith.
    (Uses only 0 ≤ q on [1,K], not strict positivity.) This is the initial-segment
    optimization at the heart of Corollary 3.5 (M(N) = S_N(K)).
-/
import Mathlib

namespace Erdos858

theorem cor35_optimization_inequality :
    ∀ (q : ℕ → ℚ) (K M : ℕ) (D : Finset ℕ), D ⊆ Finset.Icc 1 M → K ≤ M →
      (∀ a : ℕ, 1 ≤ a → a ≤ K → 0 ≤ q a) → (∀ a : ℕ, K < a → q a ≤ 0) →
      ∑ a ∈ D, q a ≤ ∑ a ∈ Finset.Icc 1 K, q a := by
  intro q K M D hDsub hKM hpos hnonpos
  rw [← Finset.sum_filter_add_sum_filter_not D (fun a => a ≤ K)]
  have h2 : ∑ a ∈ D.filter (fun a => ¬ a ≤ K), q a ≤ 0 := by
    apply Finset.sum_nonpos
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact hnonpos a (by omega)
  have h1 : ∑ a ∈ D.filter (fun a => a ≤ K), q a ≤ ∑ a ∈ Finset.Icc 1 K, q a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      obtain ⟨haD, haK⟩ := ha
      have hM : a ∈ Finset.Icc 1 M := hDsub haD
      simp only [Finset.mem_Icc] at hM
      omega
    · intro a ha _
      simp only [Finset.mem_Icc] at ha
      exact hpos a ha.1 ha.2
  linarith

end Erdos858
