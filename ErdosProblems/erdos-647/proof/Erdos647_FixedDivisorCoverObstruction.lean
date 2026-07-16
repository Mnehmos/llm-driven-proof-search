import Mathlib

/-!
# Erdős #647 — obstruction to finite fixed-divisor residue covers

This snapshot records a route-pruning result discovered during the uniform
failed-shift cover search.  It applies only to **fixed forced-divisor cells**:
a cell chooses a shift `k` and writes its forced divisor as `g*q`, where
`g ∣ A` and the residue condition has period `q`.  It does not rule out
adaptive divisors, variable affine cofactors, or nonlocal arguments using the
prime-chain families.

For one cell, the zero residue `q ∣ N` makes `g*q ∣ A*N`.  If the same divisor
also divides `A*N-k`, it divides `k`, so its divisor count is at most `k` and
cannot witness a failed shift.  For finitely many cells, the product of their
periods is a simultaneous zero residue and therefore escapes every cell.

Proof-search provenance (2026-07-15, America/Phoenix):

* single-cell preverification job
  `24b6ad47-f53e-4e8a-9cd3-a80f4220691f` (`kernel_pass`), problem
  `04da2717-8f99-42f3-88c2-0419b8c623da`, episode
  `f4024c90-035f-41a7-9cc2-33f696804e22` (`kernel_verified`), root hash
  `97912856df9b6342d7cceb3f79c0041e3defddd897daff7afb99e66bcc3f6bdc`;
* finite-family preverification job
  `8d003b8c-77a0-466e-8ed9-8f6ca650463d` (`kernel_pass`), problem
  `c8d6c67f-ddf5-42d0-b0ef-615461265969`, episode
  `4dd5a525-81d0-49c7-a2e5-2609d87c3ddb` (`kernel_verified`), root hash
  `e616f21d435d5055d162b92a2bdcf181c8cdfb77b5254ad40fc67389d50bd1f5`.
* the exact local-prime-chain escape condition below was independently
  preverified in job `d1e681ba-ac16-4775-a22f-49c687ce3477`
  (`kernel_pass`).

Search and formal assembly: OpenAI Codex, under Mnehmos orchestration.
-/

namespace Erdos647

/-- A fixed forced divisor cannot certify failure on the zero residue of its
natural period. -/
theorem sigma_zero_fixed_divisor_le_shift_on_zero_residue :
    ∀ (A N k g q : ℕ),
      g ∣ A → q ∣ N → 0 < k → k ≤ A * N → 0 < g * q →
      g * q ∣ A * N - k →
      ArithmeticFunction.sigma 0 (g * q) ≤ k := by
  intro A N k g q hgA hqN hk hkAN hd hdiv
  obtain ⟨a, ha⟩ := hgA
  obtain ⟨b, hb⟩ := hqN
  have hdAN : g * q ∣ A * N := by
    refine ⟨a * b, ?_⟩
    rw [ha, hb]
    ring
  have hdk : g * q ∣ k := by
    have hsub : A * N - (A * N - k) = k := by omega
    rw [← hsub]
    exact Nat.dvd_sub hdAN hdiv
  rw [ArithmeticFunction.sigma_zero_apply]
  exact le_trans (Nat.card_divisors_le_self (g * q))
    (Nat.le_of_dvd hk hdk)

/-- Every positive fixed divisor `d` has natural period
`d / gcd(A,d)`, so the preceding theorem applies without requiring callers
to supply the decomposition `d = g*q`. -/
theorem sigma_zero_fixed_divisor_le_shift_on_natural_period :
    ∀ (A N k d : ℕ), 0 < d → 0 < k → k ≤ A * N →
      d / Nat.gcd A d ∣ N → d ∣ A * N - k →
      ArithmeticFunction.sigma 0 d ≤ k := by
  intro A N k d hd hk hkAN hperiod hdiv
  let g := Nat.gcd A d
  let q := d / g
  have hgA : g ∣ A := Nat.gcd_dvd_left A d
  have hgd : g ∣ d := Nat.gcd_dvd_right A d
  have hdeq : g * q = d := Nat.mul_div_cancel' hgd
  have hqN : q ∣ N := hperiod
  have hdiv' : g * q ∣ A * N - k := by simpa [hdeq] using hdiv
  have h := sigma_zero_fixed_divisor_le_shift_on_zero_residue
    A N k g q hgA hqN hk hkAN (by simpa [hdeq] using hd) hdiv'
  simpa [hdeq] using h

/-- Every finite family of fixed forced-divisor cells has a common-period
escape.  The witness is the product of the cells' positive periods. -/
theorem finite_fixed_divisor_certificates_have_common_escape :
    ∀ (A : ℕ) (ι : Type) [Fintype ι] (k g q : ι → ℕ),
      (∀ i, 0 < q i) →
      ∃ N : ℕ, 0 < N ∧ ∀ i,
        g i ∣ A → 0 < k i → k i ≤ A * N → 0 < g i * q i →
        g i * q i ∣ A * N - k i →
        ArithmeticFunction.sigma 0 (g i * q i) ≤ k i := by
  intro A ι _ k g q hq
  classical
  refine ⟨∏ i, q i, Finset.prod_pos (fun i _ => hq i), ?_⟩
  intro i hgi hki hkiAN hdi hdiv
  have hqi : q i ∣ ∏ j, q j :=
    Finset.dvd_prod_of_mem q (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := hgi
  obtain ⟨b, hb⟩ := hqi
  have hdAN : g i * q i ∣ A * (∏ j, q j) := by
    refine ⟨a * b, ?_⟩
    rw [ha, hb]
    ring
  have hdk : g i * q i ∣ k i := by
    have hsub : A * (∏ j, q j) - (A * (∏ j, q j) - k i) = k i := by
      omega
    rw [← hsub]
    exact Nat.dvd_sub hdAN hdiv
  rw [ArithmeticFunction.sigma_zero_apply]
  exact le_trans (Nat.card_divisors_le_self (g i * q i))
    (Nat.le_of_dvd hki hdk)

/-- Coordinate-free version: for arbitrary positive fixed divisors, the
product of their natural periods is a simultaneous escape. -/
theorem finite_arbitrary_fixed_divisors_have_common_natural_period_escape :
    ∀ (A : ℕ) (ι : Type) [Fintype ι] (k d : ι → ℕ),
      (∀ i, 0 < d i) →
      ∃ N : ℕ, 0 < N ∧ ∀ i,
        0 < k i → k i ≤ A * N → d i ∣ A * N - k i →
        ArithmeticFunction.sigma 0 (d i) ≤ k i := by
  intro A ι _ k d hd
  classical
  let q : ι → ℕ := fun i => d i / Nat.gcd A (d i)
  have hqpos : ∀ i, 0 < q i := by
    intro i
    apply Nat.div_pos
    · exact Nat.le_of_dvd (hd i) (Nat.gcd_dvd_right A (d i))
    · exact Nat.gcd_pos_of_pos_right A (hd i)
  refine ⟨∏ i, q i, Finset.prod_pos (fun i _ => hqpos i), ?_⟩
  intro i hki hkiAN hdiv
  apply sigma_zero_fixed_divisor_le_shift_on_natural_period
    A (∏ j, q j) (k i) (d i) (hd i) hki hkiAN
  · exact Finset.dvd_prod_of_mem q (Finset.mem_univ i)
  · exact hdiv

/-- The common-zero construction is not removed by local coprimality tests on
the seven forms: every positive `a*N-1` is automatically coprime to `N`.
Thus putting finitely many active primes into the common multiple makes all
forms `a*N-1` congruent to `-1` at those primes. -/
theorem common_zero_is_coprime_to_minus_one_forms :
    ∀ N a : ℕ, 0 < N → 0 < a → Nat.Coprime N (a * N - 1) := by
  intro N a hN ha
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd N (a * N - 1)
  have hgN : g ∣ N := Nat.gcd_dvd_left N (a * N - 1)
  have hgAN : g ∣ a * N := dvd_trans hgN (dvd_mul_left N a)
  have hgform : g ∣ a * N - 1 := Nat.gcd_dvd_right N (a * N - 1)
  have hsub : a * N - (a * N - 1) = 1 := by
    have : 0 < a * N := Nat.mul_pos ha hN
    omega
  have hg1 : g ∣ 1 := by
    rw [← hsub]
    exact Nat.dvd_sub hgAN hgform
  exact Nat.eq_one_of_dvd_one hg1

/-- Exact counterexample condition for adding a finite local sieve modulus:
the escaping common multiple may be required to contain any prescribed
positive `M`, while remaining locally coprime to every form `a*N-1`. -/
theorem finite_fixed_cells_escape_with_prescribed_local_modulus :
    ∀ (A M : ℕ) (ι : Type) [Fintype ι] (k g q : ι → ℕ),
      0 < M → (∀ i, 0 < q i) →
      ∃ N : ℕ, 0 < N ∧ M ∣ N ∧
        (∀ i, g i ∣ A → 0 < k i → k i ≤ A * N → 0 < g i * q i →
          g i * q i ∣ A * N - k i →
          ArithmeticFunction.sigma 0 (g i * q i) ≤ k i) ∧
        ∀ a : ℕ, 0 < a → Nat.Coprime N (a * N - 1) := by
  intro A M ι _ k g q hM hq
  classical
  let P := ∏ i, q i
  have hP : 0 < P := Finset.prod_pos (fun i _ => hq i)
  refine ⟨M * P, Nat.mul_pos hM hP, ⟨P, rfl⟩, ?_, ?_⟩
  · intro i hgi hki hkiAN hdi hdiv
    have hqiP : q i ∣ P := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    have hqiN : q i ∣ M * P := dvd_trans hqiP (dvd_mul_left P M)
    exact sigma_zero_fixed_divisor_le_shift_on_zero_residue
      A (M * P) (k i) (g i) (q i) hgi hqiN hki hkiAN hdi hdiv
  · intro a ha
    exact common_zero_is_coprime_to_minus_one_forms (M * P) a
      (Nat.mul_pos hM hP) ha

end Erdos647
