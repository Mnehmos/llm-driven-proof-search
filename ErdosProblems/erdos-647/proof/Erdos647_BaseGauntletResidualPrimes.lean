import Mathlib

/-!
# Erdős #647 — primality of the three low-budget base-gauntlet residuals

The sharp base-gauntlet theorem leaves residual cofactors `q5`, `q9`, and
`q10` with at most three divisors.  A number greater than one with at most
three divisors is prime or a prime square.  The square alternative is
incompatible with the defining affine congruences:

* `504N - 1` is `7 mod 8`, whereas `5^a q²` is never `7 mod 8`;
* `280N - 1` is `7 mod 8`, whereas `3^a q²` is never `7 mod 8`;
* `252N - 1` is `3 mod 4`, whereas `5^a q²` is never `3 mod 4`.

Thus the three residual cofactors are prime for every adic exponent.  This is
a structural narrowing toward the global failed-shift theorem, not the final
closure of the Formal Conjectures declaration.

Tracked proof-search verification (2026-07-16):

* preverification job: `a4acfaa9-626a-4213-8282-1ff012083562`
* problem version: `66d61f93-6140-4b9d-8bfd-775dda411fdd`
* episode: `4faf6a2e-8528-4abd-a17d-9b30fc0ab98a`
* root statement hash:
  `88ffd222363ba563847a7147bc23ccc8f25e531f663452f453da4bf98c123332`
* outcome: `kernel_verified`; replay: `matched(1)`
-/

namespace Erdos647

theorem base_gauntlet_three_residuals_prime :
    ∀ N a5 q5 a9 q9 a10 q10 : ℕ,
      1 ≤ N →
      504 * N - 1 = 5 ^ a5 * q5 →
      280 * N - 1 = 3 ^ a9 * q9 →
      252 * N - 1 = 5 ^ a10 * q10 →
      1 < q5 → 1 < q9 → 1 < q10 →
      ArithmeticFunction.sigma 0 q5 ≤ 3 →
      ArithmeticFunction.sigma 0 q9 ≤ 3 →
      ArithmeticFunction.sigma 0 q10 ≤ 3 →
      Nat.Prime q5 ∧ Nat.Prime q9 ∧ Nat.Prime q10 := by
  intro N a5 q5 a9 q9 a10 q10 hN h5eq h9eq h10eq
    hq5gt hq9gt hq10gt hq5small hq9small hq10small
  have hprime_of_nonsquare : ∀ x : ℕ, 2 ≤ x →
      ArithmeticFunction.sigma 0 x ≤ 3 →
      (∀ b : ℕ, x ≠ b ^ 2) → Nat.Prime x := by
    intro x hx hsigma hnsq
    by_contra hprime
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq hx).mp hprime
    by_cases heq : a = b
    · apply hnsq a
      simpa [heq, pow_two] using hab.symm
    have hx0 : x ≠ 0 := by omega
    have hx1 : x ≠ 1 := by omega
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, one_mul] at hab
      omega
    have hb1 : b ≠ 1 := by
      intro h
      rw [h, mul_one] at hab
      omega
    have hsub : ({1, a, b, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨⟨b, hab.symm⟩, hx0⟩
      · exact ⟨⟨a, by simpa [mul_comm] using hab.symm⟩, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hcard : ({1, a, b, x} : Finset ℕ).card = 4 := by
      have h1not : 1 ∉ ({a, b, x} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hx1⟩
      have hanot : a ∉ ({b, x} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨heq, ne_of_lt ha⟩
      have hbnot : b ∉ ({x} : Finset ℕ) := by
        simpa only [Finset.mem_singleton] using ne_of_lt hb
      rw [Finset.card_insert_of_notMem h1not,
        Finset.card_insert_of_notMem hanot,
        Finset.card_insert_of_notMem hbnot,
        Finset.card_singleton]
    have hfour : 4 ≤ x.divisors.card := by
      rw [← hcard]
      exact Finset.card_le_card hsub
    rw [ArithmeticFunction.sigma_zero_apply] at hsigma
    omega
  have hpow5mod8 : ∀ a : ℕ, 5 ^ a % 8 = 1 ∨ 5 ^ a % 8 = 5 := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rcases ih with ih | ih
      · right
        rw [pow_succ, Nat.mul_mod, ih]
      · left
        rw [pow_succ, Nat.mul_mod, ih]
  have hpow3mod8 : ∀ a : ℕ, 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rcases ih with ih | ih
      · right
        rw [pow_succ, Nat.mul_mod, ih]
      · left
        rw [pow_succ, Nat.mul_mod, ih]
  have hpow5mod4 : ∀ a : ℕ, 5 ^ a % 4 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have hq5nsq : ∀ b : ℕ, q5 ≠ b ^ 2 := by
    intro b hb
    have hleft : (504 * N - 1) % 8 = 7 := by omega
    have hprod := Nat.mul_mod (5 ^ a5) q5 8
    rw [← h5eq, hleft, hb] at hprod
    have hsq := Nat.mul_mod b b 8
    rw [← pow_two] at hsq
    have hbmod : b % 8 < 8 := Nat.mod_lt b (by norm_num)
    rcases hpow5mod8 a5 with hp | hp <;> rw [hp] at hprod
    all_goals interval_cases h : b % 8 <;> omega
  have hq9nsq : ∀ b : ℕ, q9 ≠ b ^ 2 := by
    intro b hb
    have hleft : (280 * N - 1) % 8 = 7 := by omega
    have hprod := Nat.mul_mod (3 ^ a9) q9 8
    rw [← h9eq, hleft, hb] at hprod
    have hsq := Nat.mul_mod b b 8
    rw [← pow_two] at hsq
    have hbmod : b % 8 < 8 := Nat.mod_lt b (by norm_num)
    rcases hpow3mod8 a9 with hp | hp <;> rw [hp] at hprod
    all_goals interval_cases h : b % 8 <;> omega
  have hq10nsq : ∀ b : ℕ, q10 ≠ b ^ 2 := by
    intro b hb
    have hleft : (252 * N - 1) % 4 = 3 := by omega
    have hprod := Nat.mul_mod (5 ^ a10) q10 4
    rw [← h10eq, hleft, hb, hpow5mod4 a10] at hprod
    have hsq := Nat.mul_mod b b 4
    rw [← pow_two] at hsq
    have hbmod : b % 4 < 4 := Nat.mod_lt b (by norm_num)
    interval_cases h : b % 4 <;> omega
  exact ⟨hprime_of_nonsquare q5 (by omega) hq5small hq5nsq,
    hprime_of_nonsquare q9 (by omega) hq9small hq9nsq,
    hprime_of_nonsquare q10 (by omega) hq10small hq10nsq⟩

end Erdos647
