import Mathlib

/-!
# Erdős #647 — candidate-count two-parameter assembly

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  04896a5d-4423-44dc-ac03-424f8fba0689
  episode_id          e45bd140-c9b8-469a-980b-2414cb1dd3c3
  root_statement_hash 185531de8d717c7c4dde91ffb618ab216796fec1b0e322ebb0b4342514cf6b34
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    6a7074c3-b11e-44c6-bdbd-05a4a7559d9d (kernel_pass)
  result_artifact_hash fef861deb70ce13660b59f40b3e1f00cf9105a351c946db2539d38acccd103da

This is the exact seam between the repaired candidate bridge and the generic
two-parameter sieve theorem.  It substitutes the concrete mass `X` and
retains the explicit additive `z` loss from the exceptional parameter band.
-/

theorem erdos647_candidate_two_parameter_assembly :
    ∀ (s : SelbergSieve) (C : Finset ℕ) (X z R : ℕ) (L : ℝ),
      s.totalMass = X →
      (C.card : ℝ) ≤ s.siftedSum + z →
      s.siftedSum ≤ 2 * s.totalMass / L +
        (((R * R + 1 : ℕ) : ℝ) ^ 8) →
      (C.card : ℝ) ≤ 2 * X / L +
        (((R * R + 1 : ℕ) : ℝ) ^ 8) + z := by
  intro s C X z R L hmass hcard hsifted
  rw [hmass] at hsifted
  linarith
