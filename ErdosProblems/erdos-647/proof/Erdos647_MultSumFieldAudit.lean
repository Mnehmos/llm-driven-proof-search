import Mathlib

/-!
# Erdős #647 — exposed-instance multSum field audit

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  640009dd-0b98-48b7-930a-c83c6e19c8ae
  episode_id          3c2ce9c0-6e0b-4bd8-9b52-8e6464a32d64
  root_statement_hash 148469e0b0aca0bb147eb1330a3aba34913fe9c77b37739e82a47b855614c317
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    e925fd49-acde-4b36-a5eb-3f3eeefc8b3c (kernel_pass)
  result_artifact_hash d86f70adf5a25ac640ba04976abc4b4392f36c74e1bf48491def25801521f227
-/

theorem erdos647_multSum_field_audit :
    ∀ (s : BoundingSieve) (X d : ℕ),
      s.support = (Finset.Icc 1 X).image
        (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1)) →
      s.weights = (fun _ : ℕ => (1:ℝ)) →
      s.multSum d =
        (((Finset.Icc 1 X).filter (fun N =>
          d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
            (840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ) := by
  intro s X d hs hw
  unfold BoundingSieve.multSum
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
