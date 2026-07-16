import Mathlib

/-!
# Erdős #647 — finite prime-catalog escape

For any positive catalog product `M` with `M + 1 < n`, a positive shift
`k ≤ M` can be chosen so that `n-k ≡ 1 (mod M)`.  Thus `n-k` is
coprime to `M`; when it is greater than one it has a prime factor not
dividing `M`.

The final theorem specializes `M` to the product of an arbitrary finite set
of primes and starts from the exact `Fin n` supremum predicate used by Formal
Conjectures.  It proves that every hypothetical candidate larger than the
catalog product escapes that catalog at a bounded positive shift.  This is a
genuine novelty/accumulation interface, but not yet a contradiction: the
catalog product can grow with the newly produced primes.

Three strongest declarations were independently kernel-verified through the
tracked proof-search pipeline on 2026-07-16:

* `erdos647_candidate_produces_prime_outside_catalog`
  * preverification `5a0a143a-961a-4393-b276-2682936ea07c`
  * problem `01623431-7ca4-4b01-a4e6-3c5ea3fd9f15`
  * episode `bd5d7e2a-1de2-4f7c-bd31-c3a8ccf53bee`
  * root hash `70869e35d1dad4e9fc8f0b4c45ce521fb4d99fd4ea6bca7b2edc484b04ad1ac9`
* `erdos647_formal_candidate_produces_prime_outside_catalog`
  * preverification `3cf4c89e-99f0-4ae2-9b1f-2b0265ab9e3c`
  * problem `652bd4ca-8e55-4ba3-8980-0238a75c8645`
  * episode `2a9302f6-16ed-4951-b774-bc9ce773b891`
  * root hash `f530cc7fe079564343a8b5e44ac3dc21eb438b669b6155d6e8ff9e93bb42ef39`
* `erdos647_formal_candidate_escapes_finite_prime_catalog`
  * preverification `fc20df50-fdbf-4a3d-b836-f6dee39a40fc`
  * problem `20ca3fff-6c15-4524-923d-04127f8834db`
  * episode `d37cd80e-d06c-4364-8623-01b413fa7ce7`
  * root hash `a5880b21ecc4dcf6dab75b792738cfe96430ba17c27cd8eeac7939104e058db3`
-/

theorem erdos647_exists_mod_one_shift (n M : ℕ) (hM : 0 < M) (hMn : M < n) :
    ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ M ∣ (n - k - 1) := by
  let r := (n - 1) % M
  by_cases hr : r = 0
  · refine ⟨M, hM, le_rfl, hMn, ?_⟩
    have hd : M ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr
    have heq : n - M - 1 = (n - 1) - M := by omega
    rw [heq]
    exact Nat.dvd_sub hd (dvd_refl M)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrlt : r < M := Nat.mod_lt _ hM
    refine ⟨r, hrpos, hrlt.le, lt_trans hrlt hMn, ?_⟩
    have hdecomp : n - 1 = M * ((n - 1) / M) + r := by
      simpa [r, Nat.add_comm] using (Nat.mod_add_div (n - 1) M).symm
    refine ⟨(n - 1) / M, ?_⟩
    omega

theorem erdos647_exists_coprime_catalog_shift (n M : ℕ) (hM : 0 < M)
    (hMn : M + 1 < n) :
    ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ Nat.Coprime M (n - k) ∧ 1 < n - k := by
  obtain ⟨k, hkpos, hkM, hkn, hd⟩ :=
    (show ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ M ∣ (n - k - 1) from
      by
        let r := (n - 1) % M
        by_cases hr : r = 0
        · refine ⟨M, hM, le_rfl, by omega, ?_⟩
          have hd : M ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr
          have heq : n - M - 1 = (n - 1) - M := by omega
          rw [heq]
          exact Nat.dvd_sub hd (dvd_refl M)
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hrlt : r < M := Nat.mod_lt _ hM
          refine ⟨r, hrpos, hrlt.le, by omega, ?_⟩
          have hdecomp : n - 1 = M * ((n - 1) / M) + r := by
            simpa [r, Nat.add_comm] using (Nat.mod_add_div (n - 1) M).symm
          refine ⟨(n - 1) / M, ?_⟩
          omega)
  have hmgt : 1 < n - k := by omega
  obtain ⟨q, hq⟩ := hd
  have hmrepr : n - k = 1 + M * q := by omega
  have hcop : Nat.Coprime M (n - k) := by
    rw [hmrepr]
    exact (Nat.coprime_add_mul_left_right M 1 q).2 (Nat.coprime_one_right M)
  exact ⟨k, hkpos, hkM, hkn, hcop, hmgt⟩

theorem erdos647_exists_novel_prime_shift :
    ∀ n M : ℕ, 0 < M → M + 1 < n →
      ∃ k p : ℕ,
        0 < k ∧ k ≤ M ∧ k < n ∧ 1 < n - k ∧
        Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M := by
  intro n M hM hMn
  obtain ⟨k, hkpos, hkM, hkn, hcop, hmgt⟩ :=
    erdos647_exists_coprime_catalog_shift n M hM hMn
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n - k ≠ 1)
  have hpnot : ¬ p ∣ M := by
    intro hpM
    have hMp : Nat.Coprime M p := hcop.coprime_dvd_right hpdvd
    have hpone : p = 1 := Nat.eq_one_of_dvd_coprimes hMp hpM (dvd_refl p)
    exact hpprime.ne_one hpone
  exact ⟨k, p, hkpos, hkM, hkn, hmgt, hpprime, hpdvd, hpnot⟩

theorem erdos647_candidate_produces_prime_outside_catalog :
    ∀ n M : ℕ,
      0 < M →
      M + 1 < n →
      (∀ k : ℕ, 0 < k → k < n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      ∃ k p : ℕ,
        0 < k ∧ k ≤ M ∧ k < n ∧
        Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
        ArithmeticFunction.sigma 0 (n - k) ≤ M + 2 := by
  intro n M hM hMn hbudget
  let r := (n - 1) % M
  obtain ⟨k, hkpos, hkM, hkn, hd⟩ :
      ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ M ∣ (n - k - 1) := by
    by_cases hr : r = 0
    · refine ⟨M, hM, le_rfl, by omega, ?_⟩
      have hd : M ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr
      have heq : n - M - 1 = (n - 1) - M := by omega
      rw [heq]
      exact Nat.dvd_sub hd (dvd_refl M)
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hrlt : r < M := Nat.mod_lt _ hM
      refine ⟨r, hrpos, hrlt.le, by omega, ?_⟩
      have hdecomp : n - 1 = M * ((n - 1) / M) + r := by
        simpa [r, Nat.add_comm] using (Nat.mod_add_div (n - 1) M).symm
      refine ⟨(n - 1) / M, ?_⟩
      omega
  have hmgt : 1 < n - k := by omega
  obtain ⟨q, hq⟩ := hd
  have hmrepr : n - k = 1 + M * q := by omega
  have hcop : Nat.Coprime M (n - k) := by
    rw [hmrepr]
    exact (Nat.coprime_add_mul_left_right M 1 q).2 (Nat.coprime_one_right M)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n - k ≠ 1)
  have hpnot : ¬ p ∣ M := by
    intro hpM
    have hMp : Nat.Coprime M p := hcop.coprime_dvd_right hpdvd
    have hpone : p = 1 := Nat.eq_one_of_dvd_coprimes hMp hpM (dvd_refl p)
    exact hpprime.ne_one hpone
  have hτ := hbudget k hkpos hkn
  refine ⟨k, p, hkpos, hkM, hkn, hpprime, hpdvd, hpnot, ?_⟩
  omega

theorem erdos647_formal_candidate_produces_prime_outside_catalog :
    ∀ n M : ℕ,
      0 < M →
      M + 1 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ k p : ℕ,
        0 < k ∧ k ≤ M ∧ k < n ∧
        Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
        ArithmeticFunction.sigma 0 (n - k) ≤ M + 2 := by
  intro n M hM hMn H
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
  exact erdos647_candidate_produces_prime_outside_catalog n M hM hMn hbudget

theorem erdos647_formal_candidate_escapes_finite_prime_catalog :
    ∀ (n : ℕ) (S : Finset ℕ),
      (∀ p ∈ S, Nat.Prime p) →
      (∏ p ∈ S, p) + 1 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ k p : ℕ,
        0 < k ∧ k ≤ ∏ q ∈ S, q ∧ k < n ∧
        Nat.Prime p ∧ p ∣ n - k ∧ p ∉ S ∧
        ArithmeticFunction.sigma 0 (n - k) ≤ (∏ q ∈ S, q) + 2 := by
  intro n S hprime hprod H
  have hMpos : 0 < ∏ q ∈ S, q := by
    apply Finset.prod_pos
    intro p hp
    exact (hprime p hp).pos
  obtain ⟨k, p, hkpos, hkM, hkn, hpprime, hpdvd, hpnot, hτ⟩ :=
    erdos647_formal_candidate_produces_prime_outside_catalog
      n (∏ q ∈ S, q) hMpos hprod H
  have hpnotS : p ∉ S := by
    intro hpS
    exact hpnot (by simpa using Finset.dvd_prod_of_mem id hpS)
  exact ⟨k, p, hkpos, hkM, hkn, hpprime, hpdvd, hpnotS, hτ⟩
