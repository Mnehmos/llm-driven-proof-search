import Mathlib

/-!
# Erdős #647 — polynomial bound for a hard-truncated Selberg error sum

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  684cb8cf-bf0c-44e2-abec-7d0b7a0f5f28
  episode_id          312120f0-82e4-49d8-a0a5-022822683064
  root_statement_hash 3c1e46fbc7804d2f063b72a31cebded17bd0e910f97c26551b7b6ecb13f62287
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

If lambdaSquared is supported on d≤R², bounded by 16^ω(d), and the remainder
is bounded by 7^ω(d), then errSum≤(R²+1)^8. The key elementary estimate is
112^ω(d)≤128^ω(d)≤d^7 for squarefree d, since 2^ω(d)≤d.
-/

theorem erdos647_errSum_truncated_polynomial :
    ∀ (s : SelbergSieve) (w : ℕ → ℝ) (R : ℕ),
      (∀ d, R*R < d → BoundingSieve.lambdaSquared w d = 0) →
      (∀ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| ≤ (16:ℝ) ^ d.primeFactors.card) →
      (∀ d ∈ s.prodPrimes.divisors,
        |s.rem d| ≤ (7:ℝ) ^ d.primeFactors.card) →
      s.errSum (BoundingSieve.lambdaSquared w) ≤ (((R*R+1:ℕ):ℝ)^8) := by
  intro s w R hs hlambda hrem
  set A : ℕ := R*R+1 with hA_def
  have hterm : ∀ d ∈ s.prodPrimes.divisors,
      |BoundingSieve.lambdaSquared w d| * |s.rem d| ≤
        if d < A then (A:ℝ)^7 else 0 := by
    intro d hd
    by_cases hdA : d < A
    · simp only [hdA, if_true]
      have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
      have hdsqfree : Squarefree d :=
        Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree
      have htwo : 2 ^ d.primeFactors.card ≤ d := by
        calc
          2 ^ d.primeFactors.card = ∏ p ∈ d.primeFactors, 2 := by simp
          _ ≤ ∏ p ∈ d.primeFactors, p := by
            apply Finset.prod_le_prod'
            intro p hp
            exact (Nat.prime_of_mem_primeFactors hp).two_le
          _ = d := Nat.prod_primeFactors_of_squarefree hdsqfree
      have htwoR : (2:ℝ) ^ d.primeFactors.card ≤ (d:ℝ) := by
        exact_mod_cast htwo
      have h112 : (112:ℝ) ^ d.primeFactors.card ≤ (d:ℝ)^7 := by
        calc
          (112:ℝ) ^ d.primeFactors.card ≤
              (128:ℝ) ^ d.primeFactors.card :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) _
          _ = ((2:ℝ) ^ d.primeFactors.card)^7 := by
            rw [show (128:ℝ) = 2^7 by norm_num, ← pow_mul, mul_comm, pow_mul]
          _ ≤ (d:ℝ)^7 :=
            pow_le_pow_left₀ (by positivity) htwoR 7
      have hdAle : (d:ℝ) ≤ (A:ℝ) := by
        exact_mod_cast (Nat.le_of_lt hdA)
      calc
        |BoundingSieve.lambdaSquared w d| * |s.rem d| ≤
            (16:ℝ)^d.primeFactors.card * (7:ℝ)^d.primeFactors.card :=
          mul_le_mul (hlambda d hd) (hrem d hd) (abs_nonneg _)
            (pow_nonneg (by norm_num) _)
        _ = (112:ℝ)^d.primeFactors.card := by rw [← mul_pow]; norm_num
        _ ≤ (d:ℝ)^7 := h112
        _ ≤ (A:ℝ)^7 := pow_le_pow_left₀ (by positivity) hdAle 7
    · simp only [hdA, if_false]
      have hRd : R*R < d := by omega
      rw [hs d hRd, abs_zero, zero_mul]
  have hsubset : s.prodPrimes.divisors.filter (fun d => d < A) ⊆ Finset.range A := by
    intro d hd
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2
  have hcardNat : (s.prodPrimes.divisors.filter (fun d => d < A)).card ≤ A := by
    simpa using Finset.card_le_card hsubset
  have hcardR : ((s.prodPrimes.divisors.filter (fun d => d < A)).card : ℝ) ≤ (A:ℝ) := by
    exact_mod_cast hcardNat
  unfold BoundingSieve.errSum
  calc
    (∑ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| * |s.rem d|) ≤
        ∑ d ∈ s.prodPrimes.divisors, if d < A then (A:ℝ)^7 else 0 :=
      Finset.sum_le_sum hterm
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d < A), (A:ℝ)^7 := by
      rw [Finset.sum_filter]
    _ = ((s.prodPrimes.divisors.filter (fun d => d < A)).card : ℝ) * (A:ℝ)^7 := by
      simp
    _ ≤ (A:ℝ) * (A:ℝ)^7 :=
      mul_le_mul_of_nonneg_right hcardR (pow_nonneg (by positivity) 7)
    _ = (A:ℝ)^8 := by ring
    _ = (((R*R+1:ℕ):ℝ)^8) := by rw [hA_def]
