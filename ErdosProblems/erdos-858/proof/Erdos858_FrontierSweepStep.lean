/-
Erdős Problem #858 — Proposition 3.2 (frontier sweep), single-step increment.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 3.2.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 0291888b-5f81-4e5e-88df-827808e576a6,
problem_version_id 2012d242-3366-4a02-ae55-cc8744387cc6.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7f25ceb6…

The crux of the frontier sweep: raising the cutoff from K to K+1 changes the
frontier reciprocal sum by exactly q_N(K+1) = C_N(K+1) - 1/(K+1). Here
S_N(K) = Σ_{n≤N : π n ≤ K < n} 1/n and C_N(a) = Σ_{n≤N : π n = a} 1/n, and π is
an abstract parent map with π 1 = 0 and (2 ≤ n ≤ N ⇒ 1 ≤ π n < n).

Proof: the frontier decomposes as A_N(K+1) = (A_N(K) \ {K+1}) ⊍ {children of
K+1}. Raising the cutoff drops the single vertex K+1 (its parent is ≤ K, so it
sat on the K-frontier) and adds exactly the vertices whose parent is K+1 (each
such n satisfies K+1 = π n < n by the parent-smaller axiom). Summing reciprocals
over this disjoint decomposition (Finset.sum_union + Finset.add_sum_erase) gives
the increment.
-/
import Mathlib

namespace Erdos858

/-- Proposition 3.2, single step: `S_N(K+1) = S_N(K) + (C_N(K+1) - 1/(K+1))`. -/
theorem frontier_sweep_step :
    ∀ (π : ℕ → ℕ) (N K : ℕ), π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) → K + 1 ≤ N →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K + 1 ∧ K + 1 < n), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ))
          + ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = K + 1), (1:ℚ)/(n:ℚ))
              - (1:ℚ)/((K:ℚ) + 1)) := by
  intro π N K hπ1 hax hK1
  have hstep : (Finset.Icc 1 N).filter (fun n => π n ≤ K + 1 ∧ K + 1 < n)
      = ((Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n)).erase (K + 1)
        ∪ (Finset.Icc 1 N).filter (fun m => π m = K + 1) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, hN'⟩, hπn, hlt⟩
      by_cases h : π n ≤ K
      · exact Or.inl ⟨by omega, ⟨h1, hN'⟩, by omega, by omega⟩
      · exact Or.inr ⟨⟨h1, hN'⟩, by omega⟩
    · rintro (⟨hne, ⟨h1, hN'⟩, hπn, hlt⟩ | ⟨⟨h1, hN'⟩, hπeq⟩)
      · exact ⟨⟨h1, hN'⟩, by omega, by omega⟩
      · have hn2 : 2 ≤ n := by
          rcases eq_or_lt_of_le h1 with h | h
          · rw [← h, hπ1] at hπeq; omega
          · omega
        have hlt2 := (hax n hn2 hN').2
        exact ⟨⟨h1, hN'⟩, by omega, by omega⟩
  have hdisj : Disjoint (((Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n)).erase (K + 1))
      ((Finset.Icc 1 N).filter (fun m => π m = K + 1)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_erase, Finset.mem_filter] at hn hn'
    obtain ⟨-, -, hnK, -⟩ := hn
    obtain ⟨-, hn'eq⟩ := hn'
    omega
  have hmem : (K + 1) ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, hK1⟩, ?_, by omega⟩
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0; show π 1 ≤ 0; exact le_of_eq hπ1
    · have := (hax (K + 1) (by omega) hK1).2; omega
  have hkey : (∑ n ∈ ((Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n)).erase (K + 1), (1:ℚ)/(n:ℚ))
      = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K + 1 : ℕ):ℚ) := by
    have h := Finset.add_sum_erase ((Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n)) (fun n => (1:ℚ)/(n:ℚ)) hmem
    linear_combination h
  rw [hstep, Finset.sum_union hdisj, hkey]
  push_cast
  ring

end Erdos858
