import Mathlib

/-!
# Erdős #647 — exposed-instance remainder field audit

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  874897f7-1348-4cd2-ab74-bbc93ebb2920
  episode_id          e95b56da-6d95-43eb-85c5-ea2ae9c128be
  root_statement_hash c9b20538c0f9232f614f82198dc1b59db12236ac66eb0f1c74b89bdb66e2640b
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    43dc123a-92c9-40a0-b0b3-884eb54e5cca (kernel_pass)
  result_artifact_hash 484e86785a6ee8ceb20f1eaeae97755ec9dc8a6661fd44266a827afcebc7b8c0
-/

theorem erdos647_rem_field_audit :
    ∀ (s : BoundingSieve) (X d : ℕ),
      s.support = (Finset.Icc 1 X).image
        (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1)) →
      s.weights = (fun _ : ℕ => (1:ℝ)) →
      s.totalMass = X →
      s.nu d =
        (((Finset.range d).filter (fun r =>
          ∀ p ∈ Nat.primeFactors d,
            r%p ∈ (Finset.range p).filter (fun t =>
              (210*t)%p=1 ∨ (315*t)%p=1 ∨ (420*t)%p=1 ∨
              (630*t)%p=1 ∨ (840*t)%p=1 ∨ (1260*t)%p=1 ∨
              (2520*t)%p=1))).card : ℝ) / d →
      s.rem d =
        (((Finset.Icc 1 X).filter (fun N =>
          d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
            (840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ) -
        (((Finset.range d).filter (fun r =>
          ∀ p ∈ Nat.primeFactors d,
            r%p ∈ (Finset.range p).filter (fun t =>
              (210*t)%p=1 ∨ (315*t)%p=1 ∨ (420*t)%p=1 ∨
              (630*t)%p=1 ∨ (840*t)%p=1 ∨ (1260*t)%p=1 ∨
              (2520*t)%p=1))).card : ℝ) / d * X := by
  intro s X d hs hw hmass hnu
  have hmult : s.multSum d =
      (((Finset.Icc 1 X).filter (fun N =>
        d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ) := by
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
  unfold BoundingSieve.rem
  rw [hmult, hnu, hmass]
