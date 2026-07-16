import Mathlib

/-!
# Erdős #647 — eliminating the square branch at shift 1

For a large candidate, the divisor-count classification gives that `n - 1`
is prime or a prime square.  Once `2520 ∣ n`, the square branch is impossible:
an odd square is `1 mod 8`, while `n - 1` is `7 mod 8`.

Tracked proof-search verification:

* problem `ec29c1bd-1b37-4e1e-ae50-e43554a09746`
* episode `74ae7201-fabb-468e-bd1d-83c2da3bb8ef`
* outcome `kernel_verified` on the first tracked attempt
* job `e100e36a-e764-4304-9c3d-1d92037e12fd`
* asynchronous outcome `kernel_pass`
* result artifact `66cd9359d8f00e82e4a0754f69f4faa81c2ccc0f99f04092d6225c2c64b2f22b`
-/

theorem erdos647_shift_one_prime_of_dvd_2520 :
    ∀ n : ℕ, 84 < n → 2520 ∣ n →
      (Nat.Prime (n - 1) ∨
        ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2) →
      Nat.Prime (n - 1) := by
  intro n hn hdvd hclass
  rcases hclass with hp | ⟨p, hp, hp2⟩
  · exact hp
  · exfalso
    obtain ⟨q, hq⟩ := hdvd
    rcases hp.eq_two_or_odd' with htwo | hodd
    · rw [htwo] at hp2
      norm_num at hp2
      omega
    · obtain ⟨r, hr⟩ := hodd
      obtain ⟨t, ht⟩ := Nat.even_mul_succ_self r
      have hsq : p ^ 2 = 8 * t + 1 := by
        rw [hr]
        nlinarith [ht]
      omega
