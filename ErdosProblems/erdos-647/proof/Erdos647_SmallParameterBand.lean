import Mathlib

/-!
# Erdős #647 — explicit small-parameter band

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  cc5eabec-9ba7-4b38-9f8a-482998d707af
  episode_id          13abb6bb-6091-4647-b46f-8ed0417beb04
  root_statement_hash fd551191af356f6d475dc719c877be08696d4ecfc78b1d135a8166288456fd5f
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    195a2616-6b27-4fab-a9db-69dfaff3c122 (kernel_pass)
  result_artifact_hash d671f636b48478d2715038d3767579bd22b8604a5f2009570a69d26c8560fe8b

The repaired-modulus candidate theorem applies when `z < 157N`.  Its
complement inside `[1,X]` has at most `z` parameters, so this range loss is
negligible compared with the already-controlled polynomial sieve error.
-/

theorem erdos647_small_parameter_band_card :
    ∀ (X z : ℕ),
      ((Finset.Icc 1 X).filter (fun N => 157*N ≤ z)).card ≤ z := by
  intro X z
  have hsub : (Finset.Icc 1 X).filter (fun N => 157*N ≤ z) ⊆
      Finset.Icc 1 z := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc] at hN ⊢
    omega
  calc
    ((Finset.Icc 1 X).filter (fun N => 157*N ≤ z)).card
        ≤ (Finset.Icc 1 z).card := Finset.card_le_card hsub
    _ = z := by rw [Nat.card_Icc]; omega
