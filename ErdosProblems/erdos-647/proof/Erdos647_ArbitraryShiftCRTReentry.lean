import Mathlib

/-!
# Erdős #647 — arbitrary-shift CRT re-entry

The earlier CRT re-entry theorem was indexed by a consecutive prefix.  The
exact base survivor state naturally supplies primes at shifts `5,7,9,10`.
This theorem removes that mismatch: any finite injective family of prime
divisors at arbitrary positive shifts can be multiplied and re-entered through
the remainder modulo their product.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Arbitrary-shift CRT re-entry bound in the exact Formal Conjectures
candidate language. -/
theorem erdos647_arbitrary_shift_crt_reentry_bound :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      Function.Injective P →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      (∏ i : Fin r, P i) < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2 ^ r ≤ n % (∏ i : Fin r, P i) + 2 := by
  classical
  intro n r shift P hr hinj hP hQn hcand
  let Q : ℕ := ∏ i : Fin r, P i
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun i _ => (hP i).1.pos
  have hPiQ : ∀ i : Fin r, P i ∣ Q := by
    intro i
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P (Finset.mem_univ i)
  have hQnotdvd : ¬ Q ∣ n := by
    intro hQdvd
    let i : Fin r := ⟨0, hr⟩
    have hPin : P i ∣ n := (hPiQ i).trans hQdvd
    have hPshift : P i ∣ shift i := by
      have h := Nat.dvd_sub hPin (hP i).2.2.2.2
      have hrecover : n - shift i + shift i = n :=
        Nat.sub_add_cancel (hP i).2.2.2.1.le
      have heq : n - (n - shift i) = shift i := by omega
      rwa [heq] at h
    have hPle : P i ≤ shift i := Nat.le_of_dvd (hP i).2.1 hPshift
    exact (not_lt_of_ge hPle) (hP i).2.2.1
  have hrne : n % Q ≠ 0 := by
    intro hz
    exact hQnotdvd (Nat.dvd_iff_mod_eq_zero.mpr hz)
  have hrpos : 0 < n % Q := Nat.pos_of_ne_zero hrne
  have hrltQ : n % Q < Q := Nat.mod_lt n hQpos
  have hrltN : n % Q < n := lt_trans hrltQ hQn
  have hQhost : Q ∣ n - n % Q := by
    refine ⟨n / Q, ?_⟩
    have hdecomp := Nat.mod_add_div n Q
    omega
  have hhostpos : 0 < n - n % Q := by omega
  let S : Finset ℕ := Finset.univ.image P
  have hScard : S.card = r := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hS : ∀ p ∈ S, p.Prime ∧ p ∣ n - n % Q := by
    intro p hp
    dsimp [S] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact ⟨(hP i).1, (hPiQ i).trans hQhost⟩
  have htau : 2 ^ r ≤ ArithmeticFunction.sigma 0 (n - n % Q) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hhostpos.ne']
    have hsubset : S ⊆ (n - n % Q).primeFactors := by
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2,
        hhostpos.ne'⟩
    have hcard : S.card ≤ (n - n % Q).primeFactors.card :=
      Finset.card_le_card hsubset
    have hpow : 2 ^ (n - n % Q).primeFactors.card ≤
        ∏ p ∈ (n - n % Q).primeFactors,
          ((n - n % Q).factorization p + 1) := by
      apply Finset.pow_card_le_prod
      intro p hp
      have hp' : p ∈ (n - n % Q).factorization.support := by simpa using hp
      have hfac : (n - n % Q).factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp hp'
      omega
    rw [← hScard]
    exact (pow_le_pow_right' (by norm_num) hcard).trans hpow
  let f : Fin n → ℕ := fun x =>
    (x : ℕ) + ArithmeticFunction.sigma 0 x
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨2 * n, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [f]
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    omega
  let m : Fin n := ⟨n - n % Q, by omega⟩
  have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) hcand
  dsimp [f, m] at hm
  have hbudget : ArithmeticFunction.sigma 0 (n - n % Q) ≤ n % Q + 2 := by
    omega
  exact htau.trans hbudget

end Erdos647
