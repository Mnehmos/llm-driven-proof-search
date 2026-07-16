import Mathlib

/-!
# Erdős #647 — generic two-parameter truncated Selberg assembly

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  372fc2d3-227e-4104-ac93-6657f6fd8538
  episode_id          47248be9-ad01-4c85-a333-1bade2673bfc
  root_statement_hash 2670a2ea7507bf270826b978d761107e40e07564ff85cf843e340f47893d532c
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              101c6a95-9ca2-4802-b3eb-34cc80711dd6
  result_artifact_hash 9d69bad956afeb84661ba92509512d85d77a1d8f0b2a2c88f02a87c026c8c514

This is assembly stage 2: once the truncated main-sum identity,
half-denominator invariant, and polynomial error are instantiated, the
two-parameter sieve inequality follows directly from Mathlib's API.
-/

theorem erdos647_two_parameter_sieve_assembly :
    ∀ (s : SelbergSieve) (w : ℕ → ℝ) (R : ℕ) (L LR : ℝ),
      w 1 = 1 →
      s.mainSum (BoundingSieve.lambdaSquared w) = 1 / LR →
      0 ≤ s.totalMass →
      0 < L →
      L / 2 ≤ LR →
      s.errSum (BoundingSieve.lambdaSquared w) ≤ (((R*R+1:ℕ):ℝ)^8) →
      s.siftedSum ≤ 2 * s.totalMass / L + (((R*R+1:ℕ):ℝ)^8) := by
  intro s w R L LR hw1 hmain hmass hL hhalf herr
  have hupper : BoundingSieve.IsUpperMoebius
      (BoundingSieve.lambdaSquared w) :=
    BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hsifted :=
    s.siftedSum_le_mainSum_errSum_of_upperMoebius
      (BoundingSieve.lambdaSquared w) hupper
  have hhalfpos : 0 < L / 2 := by linarith
  have hrecip : 1 / LR ≤ 2 / L := by
    calc
      1 / LR ≤ 1 / (L/2) := one_div_le_one_div_of_le hhalfpos hhalf
      _ = 2 / L := by field_simp
  rw [hmain] at hsifted
  calc
    s.siftedSum ≤ s.totalMass * (1 / LR) +
        s.errSum (BoundingSieve.lambdaSquared w) := hsifted
    _ ≤ s.totalMass * (2 / L) + (((R*R+1:ℕ):ℝ)^8) :=
      add_le_add (mul_le_mul_of_nonneg_left hrecip hmass) herr
    _ = 2 * s.totalMass / L + (((R*R+1:ℕ):ℝ)^8) := by ring
