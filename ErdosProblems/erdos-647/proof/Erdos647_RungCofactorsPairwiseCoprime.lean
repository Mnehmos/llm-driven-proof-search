import Mathlib

/-!
# Erdős #647 — pairwise coprimality of the four divisible-rung cofactors

For a remaining candidate written as `n = 2520N`, the shifts
`5, 7, 9, 10` factor as

* `n - 5  = 5  * (504N - 1)`,
* `n - 7  = 7  * (360N - 1)`,
* `n - 9  = 9  * (280N - 1)`,
* `n - 10 = 10 * (252N - 1)`.

This module proves that the four displayed cofactors are pairwise coprime.
Each edge is certified by an explicit positive Bézout identity of the form
`uA = vC + 1`.  Thus no prime factor can be reused by any two of these four
low-divisor rungs.  This is a structural incompatibility theorem, not yet the
global failed-shift theorem required to close the main Formal Conjectures
declaration.

The six-edge root was independently kernel-verified through the tracked
proof-search pipeline on 2026-07-16:

* preverification job: `0b42b302-cda4-4746-bbb9-ecadba82dd56`
* problem version: `6d108ae2-23ca-4766-9122-665a27ba65a3`
* episode: `4a5b8d82-e89c-4893-8599-b6279c502a96`
* root statement hash:
  `f96395d0ec4f87c2f33741e1642943aee82a55665a13e07a22e2f6925d8c85ee`
* outcome: `kernel_verified`; replay `matched(1)`

The rung-5/rung-10 adic-depth incompatibility was separately tracked:

* preverification job: `65bf0b73-dcb8-497d-8c52-56cfb8189c56`
* problem version: `c6a98f6f-e2f7-4762-9b45-936f168135ea`
* episode: `48d2efa3-0198-4efd-927d-15a870c55cdf`
* root statement hash:
  `006c85849b78a3d5ede09612336d7907a94d5a0d0422926a93f7a22f55410050`
* outcome: `kernel_verified`; replay `matched(1)`
-/

/-- A positive Bézout relation in subtraction-free natural-number form forces
coprimality. -/
theorem erdos647_coprime_of_mul_eq_mul_add_one :
    ∀ A C u v : ℕ, u * A = v * C + 1 → Nat.Coprime A C := by
  intro A C u v hrel
  apply Nat.coprime_of_dvd'
  intro p hp hpA hpC
  have hpUA : p ∣ u * A := Dvd.dvd.mul_left hpA u
  have hpVC : p ∣ v * C := Dvd.dvd.mul_left hpC v
  have hpVC1 : p ∣ v * C + 1 := hrel ▸ hpUA
  exact (Nat.dvd_add_right hpVC).mp hpVC1

/-- The reduced cofactors at shifts `5, 7, 9, 10` are pairwise coprime. -/
theorem erdos647_rung_cofactors_pairwise_coprime :
    ∀ N : ℕ, 1 ≤ N →
      Nat.Coprime (504 * N - 1) (360 * N - 1) ∧
      Nat.Coprime (504 * N - 1) (280 * N - 1) ∧
      Nat.Coprime (504 * N - 1) (252 * N - 1) ∧
      Nat.Coprime (360 * N - 1) (280 * N - 1) ∧
      Nat.Coprime (360 * N - 1) (252 * N - 1) ∧
      Nat.Coprime (280 * N - 1) (252 * N - 1) := by
  intro N hN
  let M := N - 1
  have hNM : N = M + 1 := by dsimp [M]; omega
  have h504 : 504 * N - 1 = 504 * M + 503 := by dsimp [M]; omega
  have h360 : 360 * N - 1 = 360 * M + 359 := by dsimp [M]; omega
  have h280 : 280 * N - 1 = 280 * M + 279 := by dsimp [M]; omega
  have h252 : 252 * N - 1 = 252 * M + 251 := by dsimp [M]; omega
  have h57 : 900 * N * (504 * N - 1) =
      (1260 * N + 1) * (360 * N - 1) + 1 := by
    rw [h504, h360, hNM]
    ring
  have h59 : 350 * N * (504 * N - 1) =
      (630 * N + 1) * (280 * N - 1) + 1 := by
    rw [h504, h280, hNM]
    ring
  have h510 : 1 * (504 * N - 1) =
      2 * (252 * N - 1) + 1 := by omega
  have h79 : 980 * N * (360 * N - 1) =
      (1260 * N + 1) * (280 * N - 1) + 1 := by
    rw [h360, h280, hNM]
    ring
  have h710 : 588 * N * (360 * N - 1) =
      (840 * N + 1) * (252 * N - 1) + 1 := by
    rw [h360, h252, hNM]
    ring
  have h910 : 9 * (280 * N - 1) =
      10 * (252 * N - 1) + 1 := by omega
  exact ⟨
    erdos647_coprime_of_mul_eq_mul_add_one _ _ (900 * N) (1260 * N + 1) h57,
    erdos647_coprime_of_mul_eq_mul_add_one _ _ (350 * N) (630 * N + 1) h59,
    erdos647_coprime_of_mul_eq_mul_add_one _ _ 1 2 h510,
    erdos647_coprime_of_mul_eq_mul_add_one _ _ (980 * N) (1260 * N + 1) h79,
    erdos647_coprime_of_mul_eq_mul_add_one _ _ (588 * N) (840 * N + 1) h710,
    erdos647_coprime_of_mul_eq_mul_add_one _ _ 9 10 h910⟩

/-- Prime factors selected from the four rung cofactors are pairwise distinct. -/
theorem erdos647_rung_prime_factors_pairwise_distinct :
    ∀ N p5 p7 p9 p10 : ℕ,
      1 ≤ N →
      p5.Prime → p5 ∣ 504 * N - 1 →
      p7.Prime → p7 ∣ 360 * N - 1 →
      p9.Prime → p9 ∣ 280 * N - 1 →
      p10.Prime → p10 ∣ 252 * N - 1 →
      p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
      p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 := by
  intro N p5 p7 p9 p10 hN hp5 hp5dvd hp7 hp7dvd hp9 hp9dvd hp10 hp10dvd
  obtain ⟨h57, h59, h510, h79, h710, h910⟩ :=
    erdos647_rung_cofactors_pairwise_coprime N hN
  have distinct_of_coprime : ∀ {A C p q : ℕ},
      Nat.Coprime A C → p.Prime → p ∣ A → q.Prime → q ∣ C → p ≠ q := by
    intro A C p q hcop hp hpA hq hqC hpq
    subst q
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpA hqC)
  exact ⟨
    distinct_of_coprime h57 hp5 hp5dvd hp7 hp7dvd,
    distinct_of_coprime h59 hp5 hp5dvd hp9 hp9dvd,
    distinct_of_coprime h510 hp5 hp5dvd hp10 hp10dvd,
    distinct_of_coprime h79 hp7 hp7dvd hp9 hp9dvd,
    distinct_of_coprime h710 hp7 hp7dvd hp10 hp10dvd,
    distinct_of_coprime h910 hp9 hp9dvd hp10 hp10dvd⟩

/-- Every positive parameter produces four distinct primes, one dividing each
of the four shifted values at rungs `5, 7, 9, 10`. -/
theorem erdos647_four_rungs_supply_distinct_primes :
    ∀ N : ℕ, 1 ≤ N →
      ∃ p5 p7 p9 p10 : ℕ,
        p5.Prime ∧ p5 ∣ 2520 * N - 5 ∧
        p7.Prime ∧ p7 ∣ 2520 * N - 7 ∧
        p9.Prime ∧ p9 ∣ 2520 * N - 9 ∧
        p10.Prime ∧ p10 ∣ 2520 * N - 10 ∧
        p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
        p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 := by
  intro N hN
  have h5ne : 504 * N - 1 ≠ 1 := by omega
  have h7ne : 360 * N - 1 ≠ 1 := by omega
  have h9ne : 280 * N - 1 ≠ 1 := by omega
  have h10ne : 252 * N - 1 ≠ 1 := by omega
  obtain ⟨p5, hp5, hp5co⟩ := Nat.exists_prime_and_dvd h5ne
  obtain ⟨p7, hp7, hp7co⟩ := Nat.exists_prime_and_dvd h7ne
  obtain ⟨p9, hp9, hp9co⟩ := Nat.exists_prime_and_dvd h9ne
  obtain ⟨p10, hp10, hp10co⟩ := Nat.exists_prime_and_dvd h10ne
  have h5factor : 2520 * N - 5 = 5 * (504 * N - 1) := by omega
  have h7factor : 2520 * N - 7 = 7 * (360 * N - 1) := by omega
  have h9factor : 2520 * N - 9 = 9 * (280 * N - 1) := by omega
  have h10factor : 2520 * N - 10 = 10 * (252 * N - 1) := by omega
  have hp5shift : p5 ∣ 2520 * N - 5 := h5factor ▸ Dvd.dvd.mul_left hp5co 5
  have hp7shift : p7 ∣ 2520 * N - 7 := h7factor ▸ Dvd.dvd.mul_left hp7co 7
  have hp9shift : p9 ∣ 2520 * N - 9 := h9factor ▸ Dvd.dvd.mul_left hp9co 9
  have hp10shift : p10 ∣ 2520 * N - 10 :=
    h10factor ▸ Dvd.dvd.mul_left hp10co 10
  have hdistinct := erdos647_rung_prime_factors_pairwise_distinct
    N p5 p7 p9 p10 hN hp5 hp5co hp7 hp7co hp9 hp9co hp10 hp10co
  exact ⟨p5, p7, p9, p10, hp5, hp5shift, hp7, hp7shift,
    hp9, hp9shift, hp10, hp10shift, hdistinct⟩

/-- The 5-adic escape depths at rungs `5` and `10` cannot both be positive. -/
theorem erdos647_rung5_rung10_adic_depth_incompatible :
    ∀ N a5 a10 : ℕ, 1 ≤ N →
      5 ^ a5 ∣ 504 * N - 1 →
      5 ^ a10 ∣ 252 * N - 1 →
      a5 = 0 ∨ a10 = 0 := by
  intro N a5 a10 hN hpow5 hpow10
  by_contra hboth
  push Not at hboth
  have h5pow5 : 5 ∣ 5 ^ a5 := dvd_pow_self 5 hboth.1
  have h5pow10 : 5 ∣ 5 ^ a10 := dvd_pow_self 5 hboth.2
  have h5A : 5 ∣ 504 * N - 1 := h5pow5.trans hpow5
  have h5C : 5 ∣ 252 * N - 1 := h5pow10.trans hpow10
  have hrel : 504 * N - 1 = 2 * (252 * N - 1) + 1 := by omega
  have h5twice : 5 ∣ 2 * (252 * N - 1) := Dvd.dvd.mul_left h5C 2
  have h5plus : 5 ∣ 2 * (252 * N - 1) + 1 := hrel ▸ h5A
  have h51 : 5 ∣ 1 := (Nat.dvd_add_right h5twice).mp h5plus
  norm_num at h51
