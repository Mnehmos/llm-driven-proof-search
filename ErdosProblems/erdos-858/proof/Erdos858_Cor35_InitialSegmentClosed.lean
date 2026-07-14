/-
  Erdős problem #858 — Chojecki 2026, Corollary 3.5 / §3.

  Atom: cor35_initial_segment_closed
  Paper ref: Cor 3.5 — the initial segment [1,K] is downward-closed (a
    continuation set) under the parent map π; its boundary ∂[1,K] is the
    frontier A_N(K) used in the max-closure argument for Cor 3.5.

  problem_version_id: cca78d4c-087a-4ac0-a030-526bca3cbb90
  episode_id:         1a5a0ea6-9e90-418b-979f-1d90d0433903
  outcome:            kernel_verified
  toolchain:          leanprover/lean4:v4.32.0-rc1
                      mathlib @ 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: a80fa70468e07dec18f7a56ee61eedcbe477197e07df1a8b438b383170087bfb

  Math: For any non-root n ∈ [1,K], the parent π(n) also lies in [1,K].
  Since n ≤ K ≤ N, the parent-smaller axiom gives 1 ≤ π(n) < n, hence
  1 ≤ π(n) and π(n) < n ≤ K ⇒ π(n) ≤ K, i.e. π(n) ∈ [1,K]. This is the
  downward-closure that makes D = [1,K] a valid continuation set. Once the
  Finset.Icc membership is unfolded (simp only [Finset.mem_Icc]) the claim
  is pure linear arithmetic (omega) fed by the parent axiom.
-/
import Mathlib

namespace Erdos858

theorem cor35_initial_segment_closed :
    ∀ (π : ℕ → ℕ) (N K : ℕ),
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      K ≤ N → ∀ n ∈ Finset.Icc 1 K, 2 ≤ n → π n ∈ Finset.Icc 1 K := by
  intro π N K hax hKN n hn hn2
  simp only [Finset.mem_Icc] at hn ⊢
  obtain ⟨hn1, hnK⟩ := hn
  have hnN : n ≤ N := by omega
  obtain ⟨hpi1, hpilt⟩ := hax n hn2 hnN
  omega

end Erdos858
