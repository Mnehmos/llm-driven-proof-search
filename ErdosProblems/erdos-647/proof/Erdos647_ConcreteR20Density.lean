import Erdos647_ConcreteAnalyticFields
import Erdos647_ConcreteCandidateDensity
import Erdos647_ConcreteLogMoment
import Erdos647_ErrSumTruncatedPolynomial
import Erdos647_LambdaSquaredCardBound
import Erdos647_LambdaSquaredSupportSq
import Erdos647_SelbergLTruncatedGeHalf
import Erdos647_SelbergOptimalWeightTruncatedBound

/-!
# Erdős #647 — fully instantiated `R = (2z)^20` density inequality

This theorem contains no remaining candidate-side, coefficient, moment, or
remainder hypotheses.  Its only parameter condition is `2 ≤ z`; the concrete
promoted sieve and its truncated optimal weight are constructed internally.
-/

namespace Erdos647

theorem exists_concrete_R20_candidate_density
    (X z : ℕ) (hz : 2 ≤ z) :
    ∃ t : SelbergSieve,
      t.prodPrimes =
        ∏ p ∈ (Finset.range (z + 1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p ∧
      t.nu = ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
          (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
          (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
          (2520 * r) % q = 1)).card : ℝ) / q) ∧
      ((boundedCandidates X).card : ℝ) ≤
        60 + 2 * ((X / 2520 : ℕ) : ℝ) /
          (∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l) +
        (((((2 * z) ^ 20) * ((2 * z) ^ 20) + 1 : ℕ) : ℝ) ^ 8) + z := by
  let R : ℕ := (2 * z) ^ 20
  have hRgt : 1 < R := by
    dsimp [R]
    exact one_lt_pow' (by omega) (by norm_num)
  have hR : 1 ≤ R := Nat.le_of_lt hRgt
  obtain ⟨t, hsupport, hprod, hweights, hmass, hnu, hlevel, hcard⟩ :=
    exists_promoted_sieve_for_candidates X z R hR
  have hcoeff := concrete_selberg_coeff_bound t z hprod hnu
  have hrem := concrete_remainder_bound t X z
    hsupport hprod hweights hmass hnu
  obtain ⟨w, hw1, hwsupport, hwbound, hmain⟩ :=
    erdos647_selberg_optimal_weight_truncated_bound t R hR
  have hlambdaSupport :=
    erdos647_lambdaSquared_support_sq w R hwsupport
  have hlambda :=
    erdos647_lambdaSquared_card_bound t w hwbound hcoeff
  have herr := erdos647_errSum_truncated_polynomial
    t w R hlambdaSupport hlambda hrem
  let L : ℝ := ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l
  let LR : ℝ :=
    ∑ l ∈ t.prodPrimes.divisors.filter (fun l => l ≤ R), t.selbergTerms l
  have hLpos : 0 < L := by
    dsimp [L]
    apply Finset.sum_pos
    · intro l hl
      exact t.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
    · refine ⟨1, ?_⟩
      simp only [Nat.one_mem_divisors]
      exact t.prodPrimes_squarefree.ne_zero
  have hmoment :
      (∑ p ∈ t.prodPrimes.primeFactors, t.nu p * Real.log p) ≤
        Real.log ((R : ℕ) : ℝ) / 2 := by
    simpa [R] using erdos647_concrete_log_moment_R20 t z hz hprod hnu
  have hhalf : L / 2 ≤ LR := by
    simpa [L, LR] using
      erdos647_selberg_L_truncated_ge_half t R hRgt hmoment
  have hdensity := boundedCandidates_density_from_promoted
    t X z R w L LR hmass hcard hw1
      (by simpa [LR] using hmain) hLpos hhalf herr
  refine ⟨t, hprod, hnu, ?_⟩
  simpa [R, L] using hdensity

end Erdos647
