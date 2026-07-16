import Mathlib

/-!
# Erdős #647 — candidate Finset to siftedSum bridge

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  3821e6ae-7ce0-40eb-913e-1a39e33e62b7
  episode_id          4ba7cc7e-7d4c-4b67-a1ee-867e9fa5c47e
  root_statement_hash 6ef9f3e6e341975a7d4c186f0ffb78323d4ec10d6f9aac587e930b6c5e93fa8d
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    3e4163e3-4d26-4232-b0cb-1febd3cc6b4b (kernel_pass)
  result_artifact_hash e9730ee11f17da14939fd9a78695a27c838fdd52c9ac6933f3570d8429b013ba

This isolates the final set-theoretic candidate transport.  Once a bounded
candidate parameter set is known to satisfy the repaired modulus's coprimality
condition, its cardinality is bounded by the exact survivor count represented
by `siftedSum`.
-/

theorem erdos647_candidate_finset_le_siftedSum :
    ∀ (s : BoundingSieve) (X : ℕ) (C : Finset ℕ),
      C ⊆ Finset.Icc 1 X →
      (∀ N ∈ C, Nat.Coprime s.prodPrimes
        ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1))) →
      s.siftedSum =
        (((Finset.Icc 1 X).filter (fun N =>
          Nat.Coprime s.prodPrimes
            ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
              (840*N-1)*(1260*N-1)*(2520*N-1)))).card : ℝ) →
      (C.card : ℝ) ≤ s.siftedSum := by
  intro s X C hCX hcop hsift
  have hsub : C ⊆ (Finset.Icc 1 X).filter (fun N =>
      Nat.Coprime s.prodPrimes
        ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1))) := by
    intro N hNC
    simp only [Finset.mem_filter]
    exact ⟨hCX hNC, hcop N hNC⟩
  rw [hsift]
  exact_mod_cast Finset.card_le_card hsub
