import Mathlib

/-!
# Erdős #647 — residue refinement of the shift-7 residual shape

On the positive 7-adic branch (`N ≡ 5 mod 7`), the original shift-7 budget
forces the residual divisor count down from four to three.  The square branch
is already impossible modulo three, so the residual is prime.  Independently,
the defining affine equation forces every residual to be `2 mod 3`; this pins
the prime factors in the cube and distinct-semiprime branches to exact residue
patterns.

These are finite-state refinements toward a universal failed shift, not a
closure of the Formal Conjectures declaration.

Tracked proof-search verification (2026-07-16):

* `base_gauntlet_q7_prime_on_positive_depth_residue`
  * preverification: `b940d5e8-47bc-411e-935f-2a33677beda0`
  * problem version: `0a0758e6-5534-4b69-9326-a490e2721f1e`
  * episode: `df6ab19d-4ade-4719-a408-02fa6b70c1db`
  * root hash: `6c0cb5dbe06dc760724f9323fd4f1b7ccce2ddb1213900f331d4de90daffa3e9`
* `base_gauntlet_q7_composite_factor_residues`
  * preverification: `65a13e0d-44e5-431c-ae58-b68043b40781`
  * problem version: `c4a2bf8f-2742-4d17-b6d9-2903f7067ebe`
  * episode: `98b5e0d7-2952-4507-b2b4-75530f770ea6`
  * root hash: `6187c559f6e9631d94b5e75e32b0eff5e6818f6da97bf0fb4eaf388ff2b9a4e7`

Both outcomes are `kernel_verified`; both replays are `matched(1)`.
-/

namespace Erdos647

theorem base_gauntlet_q7_prime_on_positive_depth_residue :
    ∀ N a7 q7 : ℕ,
      1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      ¬ 7 ∣ q7 →
      1 < q7 →
      (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 →
      N % 7 = 5 →
      Nat.Prime q7 := by
  intro N a7 q7 hN hq7eq hq7ndvd hq7gt hbudget hN7
  have hmod7 := Nat.mod_add_div N 7
  have ha7pos : 1 ≤ a7 := by
    by_contra ha
    have ha0 : a7 = 0 := by omega
    subst a7
    have hNform : N = 7 * (N / 7) + 5 := by omega
    have hqeq : q7 = 7 * (360 * (N / 7) + 257) := by
      norm_num at hq7eq
      rw [hNform] at hq7eq
      omega
    exact hq7ndvd ⟨360 * (N / 7) + 257, hqeq⟩
  have hq7small : ArithmeticFunction.sigma 0 q7 ≤ 3 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q7)
      (show 3 ≤ a7 + 2 by omega)
    omega
  have hq7nsq : ∀ b : ℕ, q7 ≠ b ^ 2 := by
    intro b hb
    have hpow7mod3 : ∀ a : ℕ, 7 ^ a % 3 = 1 := by
      intro a
      induction a with
      | zero => norm_num
      | succ a ih =>
        rw [pow_succ, Nat.mul_mod, ih]
    have hleft : (360 * N - 1) % 3 = 2 := by omega
    have hprod := Nat.mul_mod (7 ^ a7) q7 3
    rw [← hq7eq, hleft, hb, hpow7mod3 a7] at hprod
    have hsq := Nat.mul_mod b b 3
    rw [← pow_two] at hsq
    have hbmod : b % 3 < 3 := Nat.mod_lt b (by norm_num)
    interval_cases h : b % 3 <;> omega
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
  exact hprime_of_nonsquare q7 (by omega) hq7small hq7nsq

theorem base_gauntlet_q7_composite_factor_residues :
    ∀ N a7 q7 : ℕ,
      1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      (((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
          ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q ∧
            ((p % 3 = 1 ∧ q % 3 = 2) ∨ (p % 3 = 2 ∧ q % 3 = 1))) ↔
        ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
          ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q)) := by
  intro N a7 q7 hN hq7eq
  have hpow7mod3 : ∀ a : ℕ, 7 ^ a % 3 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have hqmod : q7 % 3 = 2 := by
    have hleft : (360 * N - 1) % 3 = 2 := by omega
    have hprod := Nat.mul_mod (7 ^ a7) q7 3
    rw [← hq7eq, hleft, hpow7mod3 a7] at hprod
    omega
  constructor
  · rintro (⟨p, hp, hpq, hpmod⟩ | ⟨p, q, hp, hq, hpq, hprod, hmods⟩)
    · exact Or.inl ⟨p, hp, hpq⟩
    · exact Or.inr ⟨p, q, hp, hq, hpq, hprod⟩
  · rintro (⟨p, hp, hpq⟩ | ⟨p, q, hp, hq, hpq, hprod⟩)
    · left
      have hpmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hp3 := Nat.pow_mod p 3 3
      rw [hpq] at hqmod
      interval_cases h : p % 3
      · norm_num [h] at hp3
        omega
      · norm_num [h] at hp3
        omega
      · exact ⟨p, hp, hpq, h⟩
    · right
      refine ⟨p, q, hp, hq, hpq, hprod, ?_⟩
      have hpmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hqmodlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
      have hpqmod := Nat.mul_mod p q 3
      rw [hprod] at hqmod
      interval_cases hpmod : p % 3 <;>
        interval_cases hqmod' : q % 3 <;>
        norm_num [hpmod, hqmod'] at hpqmod hqmod ⊢ <;> omega

end Erdos647
