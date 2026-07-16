import Mathlib

/-!
# Erdős #647 — primorial escape for an exact Formal Conjectures candidate

`primorial W` is Mathlib's product of all primes at most `W`.  If an exact
Formal Conjectures candidate lies beyond that product, a positive shift no
larger than the product has a prime divisor strictly larger than `W`.  The
candidate hypothesis simultaneously supplies the divisor-budget bound at the
same shift.

This is a finite-prime-catalog escape theorem, not a contradiction: the
primorial threshold grows with `W`.

The strongest declaration was independently kernel-verified through the
tracked proof-search pipeline on 2026-07-16:

* `erdos647_formal_candidate_escapes_primorial`
  * preverification `5c8cc799-a181-4342-9332-3a431d448420`
  * problem `646b4846-4b44-4b79-aa40-1ef523f09fe4`
  * episode `31ba0909-6d0a-4a7d-a1fd-5db9b5987479`
  * root hash `64ffdfc202847fa6e56f202d507f1d68e8f2b6aba01b0a401dab69c4728598ce`
-/

theorem erdos647_formal_candidate_escapes_primorial :
    ∀ n W : ℕ,
      primorial W + 1 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ k p : ℕ,
        0 < k ∧ k ≤ primorial W ∧ k < n ∧ 1 < n - k ∧
        Nat.Prime p ∧ W < p ∧ p ∣ n - k ∧
        ArithmeticFunction.sigma 0 (n - k) ≤ primorial W + 2 := by
  intro n W hprim H
  have hMpos : 0 < primorial W := primorial_pos W
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
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
    let m : Fin n := ⟨n - k, by omega⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  let r := (n - 1) % primorial W
  obtain ⟨k, hkpos, hkM, hkn, hd⟩ :
      ∃ k, 0 < k ∧ k ≤ primorial W ∧ k < n ∧
        primorial W ∣ (n - k - 1) := by
    by_cases hr : r = 0
    · refine ⟨primorial W, hMpos, le_rfl, by omega, ?_⟩
      have hd : primorial W ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr
      have heq : n - primorial W - 1 = (n - 1) - primorial W := by
        omega
      rw [heq]
      exact Nat.dvd_sub hd (dvd_refl (primorial W))
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hrlt : r < primorial W := Nat.mod_lt _ hMpos
      refine ⟨r, hrpos, hrlt.le, by omega, ?_⟩
      have hdecomp :
          n - 1 = primorial W * ((n - 1) / primorial W) + r := by
        simpa [r, Nat.add_comm] using
          (Nat.mod_add_div (n - 1) (primorial W)).symm
      refine ⟨(n - 1) / primorial W, ?_⟩
      omega
  have hmgt : 1 < n - k := by omega
  obtain ⟨q, hq⟩ := hd
  have hmrepr : n - k = 1 + primorial W * q := by omega
  have hcop : Nat.Coprime (primorial W) (n - k) := by
    rw [hmrepr]
    exact
      (Nat.coprime_add_mul_left_right (primorial W) 1 q).2
        (Nat.coprime_one_right (primorial W))
  obtain ⟨p, hpprime, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : n - k ≠ 1)
  have hpnot : ¬ p ∣ primorial W := by
    intro hpM
    have hMp : Nat.Coprime (primorial W) p :=
      hcop.coprime_dvd_right hpdvd
    have hpone : p = 1 :=
      Nat.eq_one_of_dvd_coprimes hMp hpM (dvd_refl p)
    exact hpprime.ne_one hpone
  have hpW : W < p := by
    exact lt_of_not_ge fun hp_le =>
      hpnot (hpprime.dvd_primorial_iff.2 hp_le)
  have hτ := hbudget k hkpos hkn
  refine ⟨k, p, hkpos, hkM, hkn, hmgt, hpprime, hpW, hpdvd, ?_⟩
  omega
