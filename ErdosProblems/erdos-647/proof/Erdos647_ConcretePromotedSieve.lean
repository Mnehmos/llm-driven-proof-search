import Erdos647_BoundingSieveExcludeTwo
import Erdos647_BoundingSieveExposed
import Erdos647_BoundingToSelberg
import Erdos647_ConcreteCandidateBridge

/-!
# Erdős #647 — concrete repaired and promoted sieve

This is the nameable concrete instance requested by the final assembly plan.
It first constructs the seven-form `BoundingSieve`, removes the active prime
`2`, attaches the exact large-candidate count inequality, and then promotes
the same underlying structure to a `SelbergSieve` at an arbitrary positive
level `R`.
-/

namespace Erdos647

/-- A repaired seven-form `BoundingSieve` whose survivor mass controls every
large Erdős #647 candidate up to `X`. -/
theorem exists_repaired_boundingSieve_for_candidates (X z : ℕ) :
    ∃ s : BoundingSieve,
      s.support = (Finset.Icc 1 (X / 2520)).image
        (fun N => (210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
          (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
          (2520 * N - 1)) ∧
      s.prodPrimes =
        ∏ p ∈ (Finset.range (z + 1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p ∧
      s.weights = (fun _ : ℕ => (1 : ℝ)) ∧
      s.totalMass = ((X / 2520 : ℕ) : ℝ) ∧
      s.nu = ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
          (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
          (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
          (2520 * r) % q = 1)).card : ℝ) / q) ∧
      ((largeCandidates X).card : ℝ) ≤ s.siftedSum + z := by
  obtain ⟨s, hsupport, hprod, hweights, hmass, hnu⟩ :=
    erdos647_boundingSieve_exposed (X / 2520) z
  obtain ⟨s', hsupport', hprod', hweights', hmass', hnu'⟩ :=
    erdos647_boundingSieve_exclude_two s (X / 2520) z hprod hnu
  refine ⟨s', hsupport', hprod', hweights', hmass', hnu', ?_⟩
  exact largeCandidates_card_le_siftedSum_add_z
    s' X z hprod' hsupport' hweights'

/-- The same concrete sieve promoted to Mathlib's analytic `SelbergSieve`
interface without changing any candidate-side field. -/
theorem exists_promoted_sieve_for_candidates (X z R : ℕ) (hR : 1 ≤ R) :
    ∃ t : SelbergSieve,
      t.support = (Finset.Icc 1 (X / 2520)).image
        (fun N => (210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
          (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
          (2520 * N - 1)) ∧
      t.prodPrimes =
        ∏ p ∈ (Finset.range (z + 1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p ∧
      t.weights = (fun _ : ℕ => (1 : ℝ)) ∧
      t.totalMass = ((X / 2520 : ℕ) : ℝ) ∧
      t.nu = ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
          (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
          (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
          (2520 * r) % q = 1)).card : ℝ) / q) ∧
      t.level = R ∧
      ((largeCandidates X).card : ℝ) ≤ t.siftedSum + z := by
  obtain ⟨s, hsupport, hprod, hweights, hmass, hnu, hcard⟩ :=
    exists_repaired_boundingSieve_for_candidates X z
  obtain ⟨t, ht, hlevel⟩ :=
    erdos647_boundingSieve_to_selbergSieve s R hR
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, hlevel, ?_⟩
  · rw [show t.support = s.support by rw [← ht]]
    exact hsupport
  · rw [show t.prodPrimes = s.prodPrimes by rw [← ht]]
    exact hprod
  · rw [show t.weights = s.weights by rw [← ht]]
    exact hweights
  · rw [show t.totalMass = s.totalMass by rw [← ht]]
    exact hmass
  · rw [show t.nu = s.nu by rw [← ht]]
    exact hnu
  · rw [show t.siftedSum = s.siftedSum by rw [← ht]]
    exact hcard

end Erdos647
