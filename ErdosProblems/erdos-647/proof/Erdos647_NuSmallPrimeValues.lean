import Mathlib

/-!
# Erdős #647 — concrete density at the deleted small primes

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  7851c193-5d39-4302-a93f-a474a2ffa6c8
  episode_id          e11b21e8-95f3-4358-92d2-96b3263c864c
  root_statement_hash 057a47bc28d86c645c29c77546fc05686d12c7126314e000dd8a8ccee52832f2
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    65dabb0d-3893-49eb-ba06-7a21ceaf73d7 (kernel_pass)
  result_artifact_hash 5940c4cd30c1360b80a58d2d6701e20ad940db0b1a36a2c168adf74ceb327e64

Removing `2` from the active prime product costs exactly `1/2` in the
concrete `nu` sum.  The already excluded primes `3,5,7` have density zero.
-/

theorem erdos647_nu_small_prime_values :
    (ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
          (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
          (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) 2 = 1/2 ∧
      (ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
          (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
          (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) 3 = 0 ∧
      (ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
          (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
          (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) 5 = 0 ∧
      (ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
          (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
          (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) 7 = 0 := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hcard2 : ((Finset.range 2).filter (fun r =>
      (210*r)%2=1 ∨ (315*r)%2=1 ∨ (420*r)%2=1 ∨
      (630*r)%2=1 ∨ (840*r)%2=1 ∨ (1260*r)%2=1 ∨
      (2520*r)%2=1)).card = 1 := by native_decide
  have hcard3 : ((Finset.range 3).filter (fun r =>
      (210*r)%3=1 ∨ (315*r)%3=1 ∨ (420*r)%3=1 ∨
      (630*r)%3=1 ∨ (840*r)%3=1 ∨ (1260*r)%3=1 ∨
      (2520*r)%3=1)).card = 0 := by native_decide
  have hcard5 : ((Finset.range 5).filter (fun r =>
      (210*r)%5=1 ∨ (315*r)%5=1 ∨ (420*r)%5=1 ∨
      (630*r)%5=1 ∨ (840*r)%5=1 ∨ (1260*r)%5=1 ∨
      (2520*r)%5=1)).card = 0 := by native_decide
  have hcard7 : ((Finset.range 7).filter (fun r =>
      (210*r)%7=1 ∨ (315*r)%7=1 ∨ (420*r)%7=1 ∨
      (630*r)%7=1 ∨ (840*r)%7=1 ∨ (1260*r)%7=1 ∨
      (2520*r)%7=1)).card = 0 := by native_decide
  constructor
  · rw [ArithmeticFunction.prodPrimeFactors_apply (by norm_num),
      hp2.primeFactors, Finset.prod_singleton, hcard2]
    norm_num
  constructor
  · rw [ArithmeticFunction.prodPrimeFactors_apply (by norm_num),
      hp3.primeFactors, Finset.prod_singleton, hcard3]
    norm_num
  constructor
  · rw [ArithmeticFunction.prodPrimeFactors_apply (by norm_num),
      hp5.primeFactors, Finset.prod_singleton, hcard5]
    norm_num
  · rw [ArithmeticFunction.prodPrimeFactors_apply (by norm_num),
      hp7.primeFactors, Finset.prod_singleton, hcard7]
    norm_num
