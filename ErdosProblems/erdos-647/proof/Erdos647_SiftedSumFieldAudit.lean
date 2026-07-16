import Mathlib

/-!
# Erdős #647 — exposed-instance siftedSum field audit

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  dd9707c4-da49-47f6-8c3f-223bd9fef756
  episode_id          1452648d-cac9-41ec-bd0c-b1def718b639
  root_statement_hash f689cbc5c7b187fc2cb95959c7d4df139121d5b1a07a9f97076a46d88ed5550d
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    a8fedf0e-2501-408f-950c-801d2e1f6426 (kernel_pass)
  result_artifact_hash a3f186b6199fad88904ce5892e5d766fa06c48ae99adc6f2dfd9bbf42c8610f1

This identifies the abstract sieve survivor mass with the exact number of
parameters in `[1, X]` whose seven-form product is coprime to the active-prime
product.  It is the field-level interface used by the candidate-count bridge.
-/

theorem erdos647_siftedSum_field_audit :
    ∀ (s : BoundingSieve) (X : ℕ),
      s.support = (Finset.Icc 1 X).image
        (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1)) →
      s.weights = (fun _ : ℕ => (1:ℝ)) →
      s.siftedSum =
        (((Finset.Icc 1 X).filter (fun N =>
          Nat.Coprime s.prodPrimes
            ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
              (840*N-1)*(1260*N-1)*(2520*N-1)))).card : ℝ) := by
  intro s X hs hw
  unfold BoundingSieve.siftedSum
  rw [hs, hw]
  have hmono : ∀ N1 N2 : ℕ, 1 ≤ N1 → N1 < N2 →
      (210*N1-1)*(315*N1-1)*(420*N1-1)*(630*N1-1)*
        (840*N1-1)*(1260*N1-1)*(2520*N1-1) <
      (210*N2-1)*(315*N2-1)*(420*N2-1)*(630*N2-1)*
        (840*N2-1)*(1260*N2-1)*(2520*N2-1) := by
    intro N1 N2 h1 h2
    gcongr <;> omega
  have hinj : Set.InjOn
      (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
        (840*N-1)*(1260*N-1)*(2520*N-1)) (Finset.Icc 1 X) := by
    intro N1 hN1 N2 hN2 heq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hN1 hN2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd heq (Nat.ne_of_lt (hmono N1 N2 hN1.1 hlt))
    · exact absurd heq.symm (Nat.ne_of_lt (hmono N2 N1 hN2.1 hgt))
  rw [Finset.sum_image
    (fun N1 hN1 N2 hN2 heq => hinj hN1 hN2 heq)]
  rw [Finset.sum_boole]
