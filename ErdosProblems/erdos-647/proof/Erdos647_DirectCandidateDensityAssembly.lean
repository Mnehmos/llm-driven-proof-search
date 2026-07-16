import Mathlib

/-!
# Erdős #647 — direct generic candidate-density assembly

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  9ad9f4e4-11d4-4f40-89f9-39c3c990b7fa
  episode_id          58cd0973-3eb4-46d0-8bd1-22e514bbf6ae
  root_statement_hash c15e88b4e9d19c53b514d0df428e04566b8c1fe43cd2faa685fb35f4b2999f30
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    b0a418b5-6dba-461f-8b79-6b125f002af4 (kernel_pass)
  result_artifact_hash 0ca9c2d0967f8183a9077fcf6426a18142d01e8e16c99d711f6042cd82ec6f1f

This theorem folds the candidate bridge directly into the truncated Selberg
assembly.  A concrete instance now needs only to provide its exact mass, the
candidate-to-survivor inequality, and the already verified main-sum,
half-denominator, and polynomial-error hypotheses.
-/

theorem erdos647_direct_candidate_density_assembly :
    ∀ (s : SelbergSieve) (C : Finset ℕ) (w : ℕ → ℝ)
        (X z R : ℕ) (L LR : ℝ),
      s.totalMass = X →
      (C.card : ℝ) ≤ s.siftedSum + z →
      w 1 = 1 →
      s.mainSum (BoundingSieve.lambdaSquared w) = 1 / LR →
      0 < L →
      L / 2 ≤ LR →
      s.errSum (BoundingSieve.lambdaSquared w) ≤
        (((R * R + 1 : ℕ) : ℝ) ^ 8) →
      (C.card : ℝ) ≤ 2 * X / L +
        (((R * R + 1 : ℕ) : ℝ) ^ 8) + z := by
  intro s C w X z R L LR hmass hcard hw1 hmain hL hhalf herr
  have hmassnonneg : 0 ≤ s.totalMass := by
    rw [hmass]
    positivity
  have hupper : BoundingSieve.IsUpperMoebius
      (BoundingSieve.lambdaSquared w) :=
    BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hsifted :=
    s.siftedSum_le_mainSum_errSum_of_upperMoebius
      (BoundingSieve.lambdaSquared w) hupper
  have hhalfpos : 0 < L / 2 := by linarith
  have hrecip : 1 / LR ≤ 2 / L := by
    calc
      1 / LR ≤ 1 / (L / 2) :=
        one_div_le_one_div_of_le hhalfpos hhalf
      _ = 2 / L := by field_simp
  rw [hmain] at hsifted
  have hsiftedBound :
      s.siftedSum ≤
        2 * s.totalMass / L + (((R * R + 1 : ℕ) : ℝ) ^ 8) := by
    calc
      s.siftedSum ≤
          s.totalMass * (1 / LR) +
            s.errSum (BoundingSieve.lambdaSquared w) := hsifted
      _ ≤ s.totalMass * (2 / L) +
            (((R * R + 1 : ℕ) : ℝ) ^ 8) :=
        add_le_add (mul_le_mul_of_nonneg_left hrecip hmassnonneg) herr
      _ = 2 * s.totalMass / L +
            (((R * R + 1 : ℕ) : ℝ) ^ 8) := by ring
  rw [hmass] at hsiftedBound
  linarith
