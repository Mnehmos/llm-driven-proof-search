/-
Erdős problem #858 — Chojecki 2026, Proposition 4.6 (upper-layer monotonicity),
semiprime-pair (Q_N) half. Companion to the verified P_N monotonicity half.

Statement (Q_N monotonicity). For 0 < a ≤ b and any N, the semiprime-pair
partial sum over the a-domain dominates the one over the b-domain:

    Q_N(a) = Σ_{a<p≤q, a·(p·q)≤N} 1/(p·q)   satisfies   Q_N(a) ≥ Q_N(b).

Here the sum ranges over prime pairs (p, q) with a < p ≤ q and a·(p·q) ≤ N.
The paper shows a ↦ R_N(a) = P_N(a) + Q_N(a) is nonincreasing; this is the Q_N
part.

Math. The b-pair-domain is a SUBSET of the a-pair-domain: if b < p then, since
a ≤ b, also a < p; and a·(p·q) ≤ b·(p·q) ≤ N. Every summand 1/(p·q) is
nonnegative, so restricting to the smaller (b-)domain can only decrease the sum
(Finset.sum_le_sum_of_subset_of_nonneg).

Provenance.
  problem_version_id : ec7ec70f-7dfc-44d9-8422-cc39c94ab21c
  episode_id         : 3e8bbf28-cb9d-4b43-9f78-436ecae574a3
  root_statement_hash: c5b0f7370d8d6d8ddcf3e33d943ce80f26e72e60f34c60bf33f6b622ba3cbe0c
  outcome            : kernel_verified (root_proved, first submission)
  toolchain          : leanprover/lean4:v4.32.0-rc1
                       mathlib @ 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
-/

import Mathlib

namespace Erdos858

theorem prop46_QN_monotone :
    ∀ N a b : ℕ, 0 < a → a ≤ b →
      (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
          (1:ℚ)/((pq.1 : ℚ) * (pq.2 : ℚ)))
      ≥ (∑ pq ∈ ((Finset.Icc (b+1) N) ×ˢ (Finset.Icc (b+1) N)).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ b * (pq.1 * pq.2) ≤ N),
          (1:ℚ)/((pq.1 : ℚ) * (pq.2 : ℚ))) := by
  intro N a b ha hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro pq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq ⊢
    obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hpp, hqp, hle, hble⟩ := hpq
    refine ⟨⟨⟨by omega, hp2⟩, by omega, hq2⟩, hpp, hqp, hle, ?_⟩
    calc a * (pq.1 * pq.2) ≤ b * (pq.1 * pq.2) := by gcongr
      _ ≤ N := hble
  · intro pq _ _
    positivity

end Erdos858
