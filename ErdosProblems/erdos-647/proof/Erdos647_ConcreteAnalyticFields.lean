import Erdos647_ConcretePromotedSieve
import Erdos647_NuFieldAudit
import Erdos647_RemBoundSquarefree
import Erdos647_RemBoundOne
import Erdos647_RemFieldAudit
import Erdos647_RemBoundFieldAssembly
import Erdos647_RootUnionCountLe
import Erdos647_SelbergCoeffBound

/-!
# Erdős #647 — concrete analytic field bounds

These are the two pointwise adapters needed by the truncated Selberg package.
They transport the exposed seven-form product and density fields into the
uniform coefficient bound and the `7 ^ ω(d)` remainder bound.
-/

namespace Erdos647

theorem concrete_selberg_coeff_bound
    (t : SelbergSieve) (z : ℕ)
    (hprod : t.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hnu : t.nu = ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
        (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
        (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
        (2520 * r) % q = 1)).card : ℝ) / q)) :
    ∀ p ∈ t.prodPrimes.primeFactors,
      1 + (1 - t.nu p)⁻¹ ≤ 4 := by
  let A := (Finset.range (z + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7)
  have hpf : t.prodPrimes.primeFactors = A := by
    rw [hprod]
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  intro p hp
  rw [hpf] at hp
  have hpA := (Finset.mem_filter.mp hp).2
  rw [hnu]
  exact erdos647_selberg_coeff_bound p hpA.1
    hpA.2.2.1 hpA.2.2.2.1 hpA.2.2.2.2

theorem concrete_remainder_bound
    (t : SelbergSieve) (X z : ℕ)
    (hsupport : t.support = (Finset.Icc 1 (X / 2520)).image
      (fun N => (210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
        (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
        (2520 * N - 1)))
    (hprod : t.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hweights : t.weights = (fun _ : ℕ => (1 : ℝ)))
    (hmass : t.totalMass = ((X / 2520 : ℕ) : ℝ))
    (hnu : t.nu = ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
        (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
        (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
        (2520 * r) % q = 1)).card : ℝ) / q)) :
    ∀ d ∈ t.prodPrimes.divisors,
      |t.rem d| ≤ (7 : ℝ) ^ d.primeFactors.card := by
  let A := (Finset.range (z + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7)
  have hpf : t.prodPrimes.primeFactors = A := by
    rw [hprod]
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  intro d hd
  have hdvd : d ∣ t.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hsqfree : Squarefree d :=
    Squarefree.squarefree_of_dvd hdvd t.prodPrimes_squarefree
  have hadm : ∀ p ∈ d.primeFactors, p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 := by
    intro p hp
    have hp' := Nat.primeFactors_mono hdvd t.prodPrimes_squarefree.ne_zero hp
    rw [hpf] at hp'
    have hpA := (Finset.mem_filter.mp hp').2
    exact ⟨hpA.2.2.1, hpA.2.2.2.1, hpA.2.2.2.2⟩
  have hnu_d : t.nu d =
      (((Finset.range d).filter (fun r =>
        ∀ p ∈ Nat.primeFactors d,
          r % p ∈ (Finset.range p).filter (fun q =>
            (210 * q) % p = 1 ∨ (315 * q) % p = 1 ∨
            (420 * q) % p = 1 ∨ (630 * q) % p = 1 ∨
            (840 * q) % p = 1 ∨ (1260 * q) % p = 1 ∨
            (2520 * q) % p = 1))).card : ℝ) / d := by
    exact erdos647_nu_field_audit t.toBoundingSieve d hnu hsqfree
  have hraw :
      |(((Finset.Icc 1 (X / 2520)).filter (fun N =>
        d ∣ (210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
          (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
          (2520 * N - 1))).card : ℝ) -
        (((Finset.range d).filter (fun r =>
          ∀ p ∈ Nat.primeFactors d,
            r % p ∈ (Finset.range p).filter (fun q =>
              (210 * q) % p = 1 ∨ (315 * q) % p = 1 ∨
              (420 * q) % p = 1 ∨ (630 * q) % p = 1 ∨
              (840 * q) % p = 1 ∨ (1260 * q) % p = 1 ∨
              (2520 * q) % p = 1))).card : ℝ) / d *
          ((X / 2520 : ℕ) : ℝ)| ≤
        (((Finset.range d).filter (fun r =>
          ∀ p ∈ Nat.primeFactors d,
            r % p ∈ (Finset.range p).filter (fun q =>
              (210 * q) % p = 1 ∨ (315 * q) % p = 1 ∨
              (420 * q) % p = 1 ∨ (630 * q) % p = 1 ∨
              (840 * q) % p = 1 ∨ (1260 * q) % p = 1 ∨
              (2520 * q) % p = 1))).card : ℝ) := by
    by_cases hd1 : d = 1
    · subst d
      norm_num
    · have hgt : 1 < d := by
        have hdpos : 0 < d := hsqfree.ne_zero.bot_lt
        omega
      exact erdos647_rem_bound_squarefree d (X / 2520) hsqfree
        (Nat.nonempty_primeFactors.mpr hgt)
  have hroot :
      (((Finset.range d).filter (fun r =>
        ∀ p ∈ Nat.primeFactors d,
          r % p ∈ (Finset.range p).filter (fun q =>
            (210 * q) % p = 1 ∨ (315 * q) % p = 1 ∨
            (420 * q) % p = 1 ∨ (630 * q) % p = 1 ∨
            (840 * q) % p = 1 ∨ (1260 * q) % p = 1 ∨
            (2520 * q) % p = 1))).card : ℝ) ≤
        (7 : ℝ) ^ d.primeFactors.card := by
    exact_mod_cast erdos647_rootUnionCount_le d hsqfree hadm
  exact erdos647_rem_bound_field_assembly t.toBoundingSieve
    (X / 2520) d hsupport hweights hmass hnu_d hraw hroot

end Erdos647
