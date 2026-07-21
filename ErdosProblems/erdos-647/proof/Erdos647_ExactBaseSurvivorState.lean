import Mathlib

/-!
# Erdős #647 — exact candidate-facing base survivor state

This standalone assembly takes the original maximum condition for a candidate
written as n = 2520N and returns the complete four-rung finite state currently
known: factorizations, forced residual primes, exact adic residues, and refined
shift-7 prime/cube/semiprime alternatives. It is a reduction toward, not yet a
proof of, the universal failed-shift theorem.

The candidate-facing root was tracked as problem version
`de3ec3ae-de46-4911-b14c-4bdeeee1920d`, episode
`6e56eb5a-3a06-4e0d-9009-e7801b16e59c`, root statement hash
`86651ba3219e8e9ef05b6954a09ef360ae439a1d4234500645c1ddd7600b3cf8`,
with outcome `kernel_verified`. Canonical replay exposed a historical
durability race: an earlier missing-object failure now replays as a pass after
the verified child modules were persisted. The source file, including the two
stronger normalization theorems below, compiles in the pinned Lean project.
-/

namespace Erdos647.ExactBaseState

theorem full_max_implies_shift_budgets :
    ∀ n : ℕ,
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
        ∀ k : ℕ, 0 < k → k < n →
          ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
  intro n H k hk0 hkn
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

/-- The maximum condition is exactly equivalent to all positive shift budgets. -/

theorem erdos647_base_gauntlet_sharp_depth :
    ∀ N : ℕ, 1 ≤ N →
      ArithmeticFunction.sigma 0 (2520 * N - 5) ≤ 7 →
      ArithmeticFunction.sigma 0 (2520 * N - 7) ≤ 9 →
      ArithmeticFunction.sigma 0 (2520 * N - 9) ≤ 11 →
      ArithmeticFunction.sigma 0 (2520 * N - 10) ≤ 12 →
      ∃ a5 q5 a7 q7 a9 q9 a10 q10 : ℕ,
        504 * N - 1 = 5 ^ a5 * q5 ∧ ¬ 5 ∣ q5 ∧ 1 < q5 ∧
        360 * N - 1 = 7 ^ a7 * q7 ∧ ¬ 7 ∣ q7 ∧ 1 < q7 ∧
        280 * N - 1 = 3 ^ a9 * q9 ∧ ¬ 3 ∣ q9 ∧ 1 < q9 ∧
        252 * N - 1 = 5 ^ a10 * q10 ∧ ¬ 5 ∣ q10 ∧ 1 < q10 ∧
        ArithmeticFunction.sigma 0 q5 ≤ 3 ∧
        ArithmeticFunction.sigma 0 q7 ≤ 4 ∧
        ArithmeticFunction.sigma 0 q9 ≤ 3 ∧
        ArithmeticFunction.sigma 0 q10 ≤ 3 ∧
        a5 ≤ 1 ∧ a7 ≤ 2 ∧ a9 ≤ 2 ∧ a10 ≤ 1 ∧
        (a5 = 0 ∨ a10 = 0) ∧
        a5 + a7 + a9 + a10 ≤ 5 := by
  intro N hN h5 h7 h9 h10
  have hpow5mod4 : ∀ a : ℕ, 5 ^ a % 4 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have hpow7mod3 : ∀ a : ℕ, 7 ^ a % 3 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
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
  have hnot5A : ∀ a : ℕ, 504 * N - 1 ≠ 5 ^ a := by
    intro a heq
    have hleft : (504 * N - 1) % 4 = 3 := by omega
    rw [heq, hpow5mod4 a] at hleft
    omega
  have hnot7B : ∀ a : ℕ, 360 * N - 1 ≠ 7 ^ a := by
    intro a heq
    have hleft : (360 * N - 1) % 3 = 2 := by omega
    rw [heq, hpow7mod3 a] at hleft
    omega
  have hnot3C : ∀ a : ℕ, 280 * N - 1 ≠ 3 ^ a := by
    intro a heq
    have hleft : (280 * N - 1) % 8 = 7 := by omega
    rcases hpow3mod8 a with hp | hp
    · rw [heq, hp] at hleft
      omega
    · rw [heq, hp] at hleft
      omega
  have hnot5D : ∀ a : ℕ, 252 * N - 1 ≠ 5 ^ a := by
    intro a heq
    have hleft : (252 * N - 1) % 4 = 3 := by omega
    rw [heq, hpow5mod4 a] at hleft
    omega
  have hadic_split : ∀ a5 a10 : ℕ,
      5 ^ a5 ∣ 504 * N - 1 → 5 ^ a10 ∣ 252 * N - 1 →
      a5 = 0 ∨ a10 = 0 := by
    intro a5 a10 hd5 hd10
    by_contra hboth
    push Not at hboth
    have h5pow5 : 5 ∣ 5 ^ a5 := dvd_pow_self 5 hboth.1
    have h5pow10 : 5 ∣ 5 ^ a10 := dvd_pow_self 5 hboth.2
    have h5A : 5 ∣ 504 * N - 1 := h5pow5.trans hd5
    have h5D : 5 ∣ 252 * N - 1 := h5pow10.trans hd10
    have hrel : 504 * N - 1 = 2 * (252 * N - 1) + 1 := by omega
    have h5twice : 5 ∣ 2 * (252 * N - 1) := Dvd.dvd.mul_left h5D 2
    have h5plus : 5 ∣ 2 * (252 * N - 1) + 1 := hrel ▸ h5A
    have h51 : 5 ∣ 1 := (Nat.dvd_add_right h5twice).mp h5plus
    norm_num at h51
  have hsigma_ge_two : ∀ q : ℕ, 1 < q → 2 ≤ ArithmeticFunction.sigma 0 q := by
    intro q hq
    rw [ArithmeticFunction.sigma_zero_apply]
    have hq0 : q ≠ 0 := by omega
    have hq1 : q ≠ 1 := by omega
    have hsub : ({1, q} : Finset ℕ) ⊆ q.divisors := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with hd | hd
      · subst d
        exact Nat.mem_divisors.mpr ⟨one_dvd q, hq0⟩
      · subst d
        exact Nat.mem_divisors.mpr ⟨dvd_refl q, hq0⟩
    have hc := Finset.card_le_card hsub
    have hcard : ({1, q} : Finset ℕ).card = 2 := by simp [Ne.symm hq1]
    rwa [hcard] at hc

  have hAne : 504 * N - 1 ≠ 0 := by omega
  obtain ⟨a5, q5, hq5ndvd, hAeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hAne 5 (by norm_num)
  have hq5gt : 1 < q5 := by
    have hq5pos : 0 < q5 := by
      by_contra hz
      have hq50 : q5 = 0 := by omega
      rw [hq50, mul_zero] at hAeq
      omega
    have hq5ne1 : q5 ≠ 1 := by
      intro hq51
      apply hnot5A a5
      simpa [hq51] using hAeq
    omega
  have hval5 : 2520 * N - 5 = 5 ^ (a5 + 1) * q5 := by
    have hfac : 2520 * N - 5 = 5 * (504 * N - 1) := by omega
    rw [hfac, hAeq, pow_succ]
    ring
  have hcop5 : Nat.Coprime (5 ^ (a5 + 1)) q5 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq5ndvd)
  have hs5 : ArithmeticFunction.sigma 0 (5 ^ (a5 + 1)) = a5 + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
      Finset.card_range]
  have hbud5 : (a5 + 2) * ArithmeticFunction.sigma 0 q5 ≤ 7 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 5) =
        (a5 + 2) * ArithmeticFunction.sigma 0 q5 := by
      rw [hval5, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop5, hs5]
    rwa [heq] at h5
  have ha5 : a5 ≤ 1 := by
    have hlo := Nat.mul_le_mul_left (a5 + 2) (hsigma_ge_two q5 hq5gt)
    omega
  have hq5small : ArithmeticFunction.sigma 0 q5 ≤ 3 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q5)
      (show 2 ≤ a5 + 2 by omega)
    omega

  have hBne : 360 * N - 1 ≠ 0 := by omega
  obtain ⟨a7, q7, hq7ndvd, hBeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hBne 7 (by norm_num)
  have hq7gt : 1 < q7 := by
    have hq7pos : 0 < q7 := by
      by_contra hz
      have hq70 : q7 = 0 := by omega
      rw [hq70, mul_zero] at hBeq
      omega
    have hq7ne1 : q7 ≠ 1 := by
      intro hq71
      apply hnot7B a7
      simpa [hq71] using hBeq
    omega
  have hval7 : 2520 * N - 7 = 7 ^ (a7 + 1) * q7 := by
    have hfac : 2520 * N - 7 = 7 * (360 * N - 1) := by omega
    rw [hfac, hBeq, pow_succ]
    ring
  have hcop7 : Nat.Coprime (7 ^ (a7 + 1)) q7 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hq7ndvd)
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ (a7 + 1)) = a7 + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map,
      Finset.card_range]
  have hbud7 : (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 7) =
        (a7 + 2) * ArithmeticFunction.sigma 0 q7 := by
      rw [hval7, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop7, hs7]
    rwa [heq] at h7
  have ha7 : a7 ≤ 2 := by
    have hlo := Nat.mul_le_mul_left (a7 + 2) (hsigma_ge_two q7 hq7gt)
    omega
  have hq7small : ArithmeticFunction.sigma 0 q7 ≤ 4 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q7)
      (show 2 ≤ a7 + 2 by omega)
    omega

  have hCne : 280 * N - 1 ≠ 0 := by omega
  obtain ⟨a9, q9, hq9ndvd, hCeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hCne 3 (by norm_num)
  have hq9gt : 1 < q9 := by
    have hq9pos : 0 < q9 := by
      by_contra hz
      have hq90 : q9 = 0 := by omega
      rw [hq90, mul_zero] at hCeq
      omega
    have hq9ne1 : q9 ≠ 1 := by
      intro hq91
      apply hnot3C a9
      simpa [hq91] using hCeq
    omega
  have hval9 : 2520 * N - 9 = 3 ^ (a9 + 2) * q9 := by
    have hfac : 2520 * N - 9 = 9 * (280 * N - 1) := by omega
    rw [hfac, hCeq]
    have hnine : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [hnine, ← mul_assoc, ← pow_add]
    ring_nf
  have hcop9 : Nat.Coprime (3 ^ (a9 + 2)) q9 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr hq9ndvd)
  have hs9 : ArithmeticFunction.sigma 0 (3 ^ (a9 + 2)) = a9 + 3 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 3), Finset.card_map,
      Finset.card_range]
  have hbud9 : (a9 + 3) * ArithmeticFunction.sigma 0 q9 ≤ 11 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 9) =
        (a9 + 3) * ArithmeticFunction.sigma 0 q9 := by
      rw [hval9, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop9, hs9]
    rwa [heq] at h9
  have ha9 : a9 ≤ 2 := by
    have hlo := Nat.mul_le_mul_left (a9 + 3) (hsigma_ge_two q9 hq9gt)
    omega
  have hq9small : ArithmeticFunction.sigma 0 q9 ≤ 3 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q9)
      (show 3 ≤ a9 + 3 by omega)
    omega

  have hDne : 252 * N - 1 ≠ 0 := by omega
  obtain ⟨a10, q10, hq10ndvd, hDeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hDne 5 (by norm_num)
  have hq10gt : 1 < q10 := by
    have hq10pos : 0 < q10 := by
      by_contra hz
      have hq100 : q10 = 0 := by omega
      rw [hq100, mul_zero] at hDeq
      omega
    have hq10ne1 : q10 ≠ 1 := by
      intro hq101
      apply hnot5D a10
      simpa [hq101] using hDeq
    omega
  have hq10odd : ¬ 2 ∣ q10 := by
    intro h2q
    have h2 : (2 : ℕ) ∣ 252 * N - 1 := by
      rw [hDeq]
      exact Dvd.dvd.mul_left h2q (5 ^ a10)
    obtain ⟨w, hw⟩ := h2
    omega
  have hval10 : 2520 * N - 10 = 2 * 5 ^ (a10 + 1) * q10 := by
    have hfac : 2520 * N - 10 = 10 * (252 * N - 1) := by omega
    rw [hfac, hDeq, pow_succ]
    ring
  have hcop10five : Nat.Coprime (5 ^ (a10 + 1)) q10 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq10ndvd)
  have hcop10two : Nat.Coprime 2 q10 :=
    ((by norm_num : Nat.Prime 2).coprime_iff_not_dvd).mpr hq10odd
  have hcop10 : Nat.Coprime (2 * 5 ^ (a10 + 1)) q10 :=
    hcop10two.mul_left hcop10five
  have hcop25 : Nat.Coprime 2 (5 ^ (a10 + 1)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  have hs10five : ArithmeticFunction.sigma 0 (5 ^ (a10 + 1)) = a10 + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
      Finset.card_range]
  have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by
    rw [ArithmeticFunction.sigma_zero_apply]
    change (Nat.divisors (2 ^ 1)).card = 2
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 2), Finset.card_map,
      Finset.card_range]
  have hs25 : ArithmeticFunction.sigma 0 (2 * 5 ^ (a10 + 1)) = 2 * (a10 + 2) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25, hs2, hs10five]
  have hbud10 : 2 * ((a10 + 2) * ArithmeticFunction.sigma 0 q10) ≤ 12 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 10) =
        2 * ((a10 + 2) * ArithmeticFunction.sigma 0 q10) := by
      rw [hval10, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop10, hs25]
      ring
    rwa [heq] at h10
  have ha10 : a10 ≤ 1 := by
    have hlo := Nat.mul_le_mul_left (a10 + 2) (hsigma_ge_two q10 hq10gt)
    omega
  have hq10small : ArithmeticFunction.sigma 0 q10 ≤ 3 := by
    have hinner := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q10)
      (show 2 ≤ a10 + 2 by omega)
    have hlo := Nat.mul_le_mul_left 2 hinner
    omega

  have hsplit : a5 = 0 ∨ a10 = 0 := by
    apply hadic_split a5 a10
    · rw [hAeq]
      exact dvd_mul_right (5 ^ a5) q5
    · rw [hDeq]
      exact dvd_mul_right (5 ^ a10) q10
  refine ⟨a5, q5, a7, q7, a9, q9, a10, q10,
    hAeq, hq5ndvd, hq5gt, hBeq, hq7ndvd, hq7gt,
    hCeq, hq9ndvd, hq9gt, hDeq, hq10ndvd, hq10gt,
    hq5small, hq7small, hq9small, hq10small,
    ha5, ha7, ha9, ha10, hsplit, ?_⟩
  rcases hsplit with h5zero | h10zero
  · omega
  · omega

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

theorem sigma_zero_le_four_classification :
    ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 4 →
      Nat.Prime x ∨
        (∃ p : ℕ, Nat.Prime p ∧ x = p ^ 2) ∨
        (∃ p : ℕ, Nat.Prime p ∧ x = p ^ 3) ∨
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ x = p * q := by
  intro x hx hsigma
  by_cases hxprime : Nat.Prime x
  · exact Or.inl hxprime
  right
  let p := x.minFac
  let c := x / p
  have hxpos : 0 < x := by omega
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have hpprime : Nat.Prime p := Nat.minFac_prime hx1
  have hpdvd : p ∣ x := Nat.minFac_dvd x
  have hxc : x = p * c := by
    dsimp [c]
    exact (Nat.mul_div_cancel' hpdvd).symm
  have hplec : p ≤ c := by
    dsimp [p, c]
    exact Nat.minFac_le_div hxpos hxprime
  by_cases hpc : p = c
  · left
    exact ⟨p, hpprime, by rw [hxc, hpc, pow_two]⟩
  have hpltc : p < c := lt_of_le_of_ne hplec hpc
  have hp2 : 2 ≤ p := hpprime.two_le
  have hc2 : 2 ≤ c := le_trans hp2 hplec
  have hplt : p < x := by
    rw [hxc]
    nlinarith
  have hclt : c < x := by
    rw [hxc]
    nlinarith
  have hcdvd : c ∣ x := by
    rw [hxc]
    exact dvd_mul_left c p
  have hsub : ({1, p, c, x} : Finset ℕ) ⊆ x.divisors := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Nat.mem_divisors]
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨one_dvd _, hx0⟩
    · exact ⟨hpdvd, hx0⟩
    · exact ⟨hcdvd, hx0⟩
    · exact ⟨dvd_rfl, hx0⟩
  have hcard : ({1, p, c, x} : Finset ℕ).card = 4 := by
    have h1not : 1 ∉ ({p, c, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by omega, by omega, by omega⟩
    have hpnot : p ∉ ({c, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpc, ne_of_lt hplt⟩
    have hcnot : c ∉ ({x} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using ne_of_lt hclt
    rw [Finset.card_insert_of_notMem h1not,
      Finset.card_insert_of_notMem hpnot,
      Finset.card_insert_of_notMem hcnot,
      Finset.card_singleton]
  have hdivcard : x.divisors.card ≤ 4 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    exact hsigma
  have hseteq : ({1, p, c, x} : Finset ℕ) = x.divisors := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    exact hdivcard
  by_cases hcprime : Nat.Prime c
  · right
    right
    exact ⟨p, c, hpprime, hcprime, hpc, hxc⟩
  obtain ⟨d, e, hd, he, hde⟩ :=
    (Nat.not_prime_iff_exists_mul_eq hc2).mp hcprime
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d <;> simp_all
    · exact h
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> simp_all
    · exact h
  have hdmem : d ∈ ({1, p, c, x} : Finset ℕ) := by
    rw [hseteq, Nat.mem_divisors]
    exact ⟨(show d ∣ c from ⟨e, hde.symm⟩).trans hcdvd, hx0⟩
  have hemem : e ∈ ({1, p, c, x} : Finset ℕ) := by
    rw [hseteq, Nat.mem_divisors]
    have hedvd : e ∣ c := ⟨d, by simpa [mul_comm] using hde.symm⟩
    exact ⟨hedvd.trans hcdvd, hx0⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem hemem
  have hdp : d = p := by
    rcases hdmem with hd1 | hdp | hdc | hdx
    · omega
    · exact hdp
    · omega
    · omega
  have hep : e = p := by
    rcases hemem with he1 | hep | hec | hex
    · omega
    · exact hep
    · omega
    · omega
  right
  left
  refine ⟨p, hpprime, ?_⟩
  rw [hxc, ← hde, hdp, hep]
  ring

/-- The `q7` residual is `2 mod 3`, so the prime-square branch in the generic
four-divisor classification is impossible. -/

theorem base_gauntlet_q7_shape :
    ∀ N a7 q7 : ℕ, 1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      1 < q7 → ArithmeticFunction.sigma 0 q7 ≤ 4 →
      Nat.Prime q7 ∨
        (∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q := by
  intro N a7 q7 hN hq7eq hq7gt hq7small
  have hpow7mod3 : ∀ a : ℕ, 7 ^ a % 3 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have hq7nsq : ∀ b : ℕ, q7 ≠ b ^ 2 := by
    intro b hb
    have hleft : (360 * N - 1) % 3 = 2 := by omega
    have hprod := Nat.mul_mod (7 ^ a7) q7 3
    rw [← hq7eq, hleft, hb, hpow7mod3 a7] at hprod
    have hsq := Nat.mul_mod b b 3
    rw [← pow_two] at hsq
    have hbmod : b % 3 < 3 := Nat.mod_lt b (by norm_num)
    interval_cases h : b % 3 <;> omega
  rcases sigma_zero_le_four_classification q7 (by omega) hq7small with
    hprime | hsquare | hcube | hsemiprime
  · exact Or.inl hprime
  · obtain ⟨p, hp, hpq⟩ := hsquare
    exact absurd hpq (hq7nsq p)
  · exact Or.inr (Or.inl hcube)
  · exact Or.inr (Or.inr hsemiprime)

/-- The original shift-7 budget couples the 7-adic depth to the residual
shape.  A composite residual has exactly four divisors, so it can occur only
at adic depth zero. -/

theorem base_gauntlet_q7_composite_forces_depth_zero :
    ∀ N a7 q7 : ℕ, 1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      1 < q7 →
      (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 →
      (Nat.Prime q7 ∧ a7 ≤ 2) ∨
        (a7 = 0 ∧
          ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
            ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q)) := by
  intro N a7 q7 hN hq7eq hq7gt hbudget
  have hq7small : ArithmeticFunction.sigma 0 q7 ≤ 4 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q7)
      (show 2 ≤ a7 + 2 by omega)
    omega
  rcases base_gauntlet_q7_shape N a7 q7 hN hq7eq hq7gt hq7small with
    hprime | hcube | hsemiprime
  · left
    have hsigma : ArithmeticFunction.sigma 0 q7 = 2 := by
      rw [show q7 = q7 ^ 1 from (pow_one q7).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hprime]
    rw [hsigma] at hbudget
    exact ⟨hprime, by omega⟩
  · right
    obtain ⟨p, hp, hpq⟩ := hcube
    have hsigma : ArithmeticFunction.sigma 0 q7 = 4 := by
      rw [hpq, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    rw [hsigma] at hbudget
    exact ⟨by omega, Or.inl ⟨p, hp, hpq⟩⟩
  · right
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ := hsemiprime
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hsigmap : ArithmeticFunction.sigma 0 p = 2 := by
      rw [show p = p ^ 1 from (pow_one p).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    have hsigmaq : ArithmeticFunction.sigma 0 q = 2 := by
      rw [show q = q ^ 1 from (pow_one q).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hq]
    have hsigma : ArithmeticFunction.sigma 0 q7 = 4 := by
      rw [hprod, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        hsigmap, hsigmaq]
      norm_num
    rw [hsigma] at hbudget
    exact ⟨by omega, Or.inr ⟨p, q, hp, hq, hpq, hprod⟩⟩

theorem base_gauntlet_five_adic_depth_residues :
    ∀ N a5 q5 a10 q10 : ℕ,
      1 ≤ N →
      504 * N - 1 = 5 ^ a5 * q5 →
      ¬ 5 ∣ q5 →
      a5 ≤ 1 →
      252 * N - 1 = 5 ^ a10 * q10 →
      ¬ 5 ∣ q10 →
      a10 ≤ 1 →
      (a5 = 1 ↔ N % 5 = 4) ∧ (a10 = 1 ↔ N % 5 = 3) := by
  intro N a5 q5 a10 q10 hN h5eq hq5 h5depth h10eq hq10 h10depth
  have hmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  have hdecomp := Nat.mod_add_div N 5
  constructor
  · constructor
    · intro ha5
      subst a5
      interval_cases hres : N % 5 <;> omega
    · intro hres
      interval_cases ha5 : a5
      · have hNform : N = 5 * (N / 5) + 4 := by omega
        have hq5eq : q5 = 5 * (504 * (N / 5) + 403) := by
          norm_num at h5eq
          rw [hNform] at h5eq
          omega
        have hdiv : 5 ∣ q5 := by
          refine ⟨504 * (N / 5) + 403, ?_⟩
          exact hq5eq
        exact absurd hdiv hq5
      · rfl
  · constructor
    · intro ha10
      subst a10
      interval_cases hres : N % 5 <;> omega
    · intro hres
      interval_cases ha10 : a10
      · have hNform : N = 5 * (N / 5) + 3 := by omega
        have hq10eq : q10 = 5 * (252 * (N / 5) + 151) := by
          norm_num at h10eq
          rw [hNform] at h10eq
          omega
        have hdiv : 5 ∣ q10 := by
          refine ⟨252 * (N / 5) + 151, ?_⟩
          exact hq10eq
        exact absurd hdiv hq10
      · rfl

theorem base_gauntlet_higher_adic_depth_residues :
    ∀ N a7 q7 a9 q9 : ℕ,
      1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      ¬ 7 ∣ q7 →
      a7 ≤ 2 →
      280 * N - 1 = 3 ^ a9 * q9 →
      ¬ 3 ∣ q9 →
      a9 ≤ 2 →
      (a7 = 0 ↔ N % 7 ≠ 5) ∧
      (a7 = 1 ↔ N % 7 = 5 ∧ N % 49 ≠ 26) ∧
      (a7 = 2 ↔ N % 49 = 26) ∧
      (a9 = 0 ↔ N % 3 ≠ 1) ∧
      (a9 = 1 ↔ N % 3 = 1 ∧ N % 9 ≠ 1) ∧
      (a9 = 2 ↔ N % 9 = 1) := by
  intro N a7 q7 a9 q9 hN h7eq hq7 h7depth h9eq hq9 h9depth
  have hmod7 := Nat.mod_add_div N 7
  have hmod49 := Nat.mod_add_div N 49
  have hmod3 := Nat.mod_add_div N 3
  have hmod9 := Nat.mod_add_div N 9
  have h7zero : a7 = 0 → N % 7 ≠ 5 := by
    intro ha hres
    subst a7
    have hNform : N = 7 * (N / 7) + 5 := by omega
    have hqeq : q7 = 7 * (360 * (N / 7) + 257) := by
      norm_num at h7eq
      rw [hNform] at h7eq
      omega
    exact hq7 ⟨360 * (N / 7) + 257, hqeq⟩
  have h7one : a7 = 1 → N % 7 = 5 ∧ N % 49 ≠ 26 := by
    intro ha
    subst a7
    constructor
    · have hlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
      interval_cases hres : N % 7 <;> omega
    · intro hres
      have hNform : N = 49 * (N / 49) + 26 := by omega
      have hqeq : q7 = 7 * (360 * (N / 49) + 191) := by
        norm_num at h7eq
        rw [hNform] at h7eq
        omega
      exact hq7 ⟨360 * (N / 49) + 191, hqeq⟩
  have h7two : a7 = 2 → N % 49 = 26 := by
    intro ha
    subst a7
    have hlt : N % 49 < 49 := Nat.mod_lt N (by norm_num)
    interval_cases hres : N % 49 <;> omega
  have h9zero : a9 = 0 → N % 3 ≠ 1 := by
    intro ha hres
    subst a9
    have hNform : N = 3 * (N / 3) + 1 := by omega
    have hqeq : q9 = 3 * (280 * (N / 3) + 93) := by
      norm_num at h9eq
      rw [hNform] at h9eq
      omega
    exact hq9 ⟨280 * (N / 3) + 93, hqeq⟩
  have h9one : a9 = 1 → N % 3 = 1 ∧ N % 9 ≠ 1 := by
    intro ha
    subst a9
    constructor
    · have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
      interval_cases hres : N % 3 <;> omega
    · intro hres
      have hNform : N = 9 * (N / 9) + 1 := by omega
      have hqeq : q9 = 3 * (280 * (N / 9) + 31) := by
        norm_num at h9eq
        rw [hNform] at h9eq
        omega
      exact hq9 ⟨280 * (N / 9) + 31, hqeq⟩
  have h9two : a9 = 2 → N % 9 = 1 := by
    intro ha
    subst a9
    have hlt : N % 9 < 9 := Nat.mod_lt N (by norm_num)
    interval_cases hres : N % 9 <;> omega
  have h49to7 : N % 49 = 26 → N % 7 = 5 := by
    intro hres
    have hNform : N = 49 * (N / 49) + 26 := by omega
    have hlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
    interval_cases h : N % 7 <;> omega
  have h9to3 : N % 9 = 1 → N % 3 = 1 := by
    intro hres
    have hNform : N = 9 * (N / 9) + 1 := by omega
    have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
    interval_cases h : N % 3 <;> omega
  refine ⟨⟨h7zero, ?_⟩, ⟨h7one, ?_⟩, ⟨h7two, ?_⟩,
    ⟨h9zero, ?_⟩, ⟨h9one, ?_⟩, ⟨h9two, ?_⟩⟩
  · intro hres
    interval_cases ha : a7
    · rfl
    · exact absurd (h7one rfl).1 hres
    · exact absurd (h49to7 (h7two rfl)) hres
  · rintro ⟨hres7, hres49⟩
    interval_cases ha : a7
    · exact False.elim ((h7zero rfl) hres7)
    · rfl
    · exact absurd (h7two rfl) hres49
  · intro hres49
    interval_cases ha : a7
    · exact False.elim ((h7zero rfl) (h49to7 hres49))
    · exact absurd hres49 (h7one rfl).2
    · rfl
  · intro hres
    interval_cases ha : a9
    · rfl
    · exact absurd (h9one rfl).1 hres
    · exact absurd (h9to3 (h9two rfl)) hres
  · rintro ⟨hres3, hres9⟩
    interval_cases ha : a9
    · exact False.elim ((h9zero rfl) hres3)
    · rfl
    · exact absurd (h9two rfl) hres9
  · intro hres9
    interval_cases ha : a9
    · exact False.elim ((h9zero rfl) (h9to3 hres9))
    · exact absurd hres9 (h9one rfl).2
    · rfl

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

set_option maxHeartbeats 1000000 in
theorem candidate_exact_base_survivor_state :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ a5 q5 a7 q7 a9 q9 a10 q10 : ℕ,
        504 * N - 1 = 5 ^ a5 * q5 ∧ ¬ 5 ∣ q5 ∧ 1 < q5 ∧
        360 * N - 1 = 7 ^ a7 * q7 ∧ ¬ 7 ∣ q7 ∧ 1 < q7 ∧
        280 * N - 1 = 3 ^ a9 * q9 ∧ ¬ 3 ∣ q9 ∧ 1 < q9 ∧
        252 * N - 1 = 5 ^ a10 * q10 ∧ ¬ 5 ∣ q10 ∧ 1 < q10 ∧
        Nat.Prime q5 ∧ Nat.Prime q9 ∧ Nat.Prime q10 ∧
        (a5 = 1 ↔ N % 5 = 4) ∧
        (a10 = 1 ↔ N % 5 = 3) ∧
        (a7 = 0 ↔ N % 7 ≠ 5) ∧
        (a7 = 1 ↔ N % 7 = 5 ∧ N % 49 ≠ 26) ∧
        (a7 = 2 ↔ N % 49 = 26) ∧
        (a9 = 0 ↔ N % 3 ≠ 1) ∧
        (a9 = 1 ↔ N % 3 = 1 ∧ N % 9 ≠ 1) ∧
        (a9 = 2 ↔ N % 9 = 1) ∧
        ((Nat.Prime q7 ∧ a7 ≤ 2) ∨
          (a7 = 0 ∧
            ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
              ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
                q7 = p * q ∧
                ((p % 3 = 1 ∧ q % 3 = 2) ∨
                  (p % 3 = 2 ∧ q % 3 = 1))))) := by
  intro n N hn84 hnN H
  subst n
  have hN : 1 ≤ N := by omega
  have hfac7 : 2520 * N - 7 = 7 * (360 * N - 1) := by
    clear H
    omega
  have hbudgets := full_max_implies_shift_budgets (2520 * N) H
  have h5 := hbudgets 5 (by omega) (by omega)
  have h7 := hbudgets 7 (by omega) (by omega)
  have h9 := hbudgets 9 (by omega) (by omega)
  have h10 := hbudgets 10 (by omega) (by omega)
  norm_num at h5 h7 h9 h10
  obtain ⟨a5, q5, a7, q7, a9, q9, a10, q10,
      h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
      h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
      hq5small, hq7small, hq9small, hq10small,
      ha5, ha7, ha9, ha10, hsplit, hsum⟩ :=
    erdos647_base_gauntlet_sharp_depth N hN h5 h7 h9 h10
  obtain ⟨hq5prime, hq9prime, hq10prime⟩ :=
    base_gauntlet_three_residuals_prime
      N a5 q5 a9 q9 a10 q10 hN h5eq h9eq h10eq
        hq5gt hq9gt hq10gt hq5small hq9small hq10small
  obtain ⟨ha5res, ha10res⟩ :=
    base_gauntlet_five_adic_depth_residues
      N a5 q5 a10 q10 hN h5eq hq5ndvd ha5
        h10eq hq10ndvd ha10
  obtain ⟨ha70, ha71, ha72, ha90, ha91, ha92⟩ :=
    base_gauntlet_higher_adic_depth_residues
      N a7 q7 a9 q9 hN h7eq hq7ndvd ha7 h9eq hq9ndvd ha9
  have hval7 : 2520 * N - 7 = 7 ^ (a7 + 1) * q7 := by
    rw [hfac7, h7eq, pow_succ]
    ring
  have hcop7 : Nat.Coprime (7 ^ (a7 + 1)) q7 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hq7ndvd)
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ (a7 + 1)) = a7 + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map,
      Finset.card_range]
  have hbud7 : (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 7) =
        (a7 + 2) * ArithmeticFunction.sigma 0 q7 := by
      rw [hval7,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop7,
        hs7]
    rwa [heq] at h7
  have hq7alt := base_gauntlet_q7_composite_forces_depth_zero
    N a7 q7 hN h7eq hq7gt hbud7
  have hq7refined :
      (Nat.Prime q7 ∧ a7 ≤ 2) ∨
        (a7 = 0 ∧
          ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
            ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
              q7 = p * q ∧
              ((p % 3 = 1 ∧ q % 3 = 2) ∨
                (p % 3 = 2 ∧ q % 3 = 1)))) := by
    rcases hq7alt with hprime | hcomposite
    · exact Or.inl hprime
    · exact Or.inr ⟨hcomposite.1,
        (base_gauntlet_q7_composite_factor_residues
          N a7 q7 hN h7eq).2 hcomposite.2⟩
  exact ⟨a5, q5, a7, q7, a9, q9, a10, q10,
    h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
    h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
    hq5prime, hq9prime, hq10prime,
    ha5res, ha10res, ha70, ha71, ha72, ha90, ha91, ha92, hq7refined⟩

set_option maxHeartbeats 1000000 in
/-- The exact survivor state with the finite depth bounds retained explicitly.
This is the branch-normalization interface used to eliminate the four depth
witnesses in the next theorem. -/
theorem candidate_exact_base_survivor_state_with_bounds :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ a5 q5 a7 q7 a9 q9 a10 q10 : ℕ,
        504 * N - 1 = 5 ^ a5 * q5 ∧ ¬ 5 ∣ q5 ∧ 1 < q5 ∧
        360 * N - 1 = 7 ^ a7 * q7 ∧ ¬ 7 ∣ q7 ∧ 1 < q7 ∧
        280 * N - 1 = 3 ^ a9 * q9 ∧ ¬ 3 ∣ q9 ∧ 1 < q9 ∧
        252 * N - 1 = 5 ^ a10 * q10 ∧ ¬ 5 ∣ q10 ∧ 1 < q10 ∧
        Nat.Prime q5 ∧ Nat.Prime q9 ∧ Nat.Prime q10 ∧
        a5 ≤ 1 ∧ a7 ≤ 2 ∧ a9 ≤ 2 ∧ a10 ≤ 1 ∧
        (a5 = 0 ∨ a10 = 0) ∧ a5 + a7 + a9 + a10 ≤ 5 ∧
        (a5 = 1 ↔ N % 5 = 4) ∧
        (a10 = 1 ↔ N % 5 = 3) ∧
        (a7 = 0 ↔ N % 7 ≠ 5) ∧
        (a7 = 1 ↔ N % 7 = 5 ∧ N % 49 ≠ 26) ∧
        (a7 = 2 ↔ N % 49 = 26) ∧
        (a9 = 0 ↔ N % 3 ≠ 1) ∧
        (a9 = 1 ↔ N % 3 = 1 ∧ N % 9 ≠ 1) ∧
        (a9 = 2 ↔ N % 9 = 1) ∧
        ((Nat.Prime q7 ∧ a7 ≤ 2) ∨
          (a7 = 0 ∧
            ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
              ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
                q7 = p * q ∧
                ((p % 3 = 1 ∧ q % 3 = 2) ∨
                  (p % 3 = 2 ∧ q % 3 = 1))))) := by
  intro n N hn84 hnN H
  subst n
  have hN : 1 ≤ N := by omega
  have hfac7 : 2520 * N - 7 = 7 * (360 * N - 1) := by
    clear H
    omega
  have hbudgets := full_max_implies_shift_budgets (2520 * N) H
  have h5 := hbudgets 5 (by omega) (by omega)
  have h7 := hbudgets 7 (by omega) (by omega)
  have h9 := hbudgets 9 (by omega) (by omega)
  have h10 := hbudgets 10 (by omega) (by omega)
  norm_num at h5 h7 h9 h10
  obtain ⟨a5, q5, a7, q7, a9, q9, a10, q10,
      h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
      h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
      hq5small, hq7small, hq9small, hq10small,
      ha5, ha7, ha9, ha10, hsplit, hsum⟩ :=
    erdos647_base_gauntlet_sharp_depth N hN h5 h7 h9 h10
  obtain ⟨hq5prime, hq9prime, hq10prime⟩ :=
    base_gauntlet_three_residuals_prime
      N a5 q5 a9 q9 a10 q10 hN h5eq h9eq h10eq
        hq5gt hq9gt hq10gt hq5small hq9small hq10small
  obtain ⟨ha5res, ha10res⟩ :=
    base_gauntlet_five_adic_depth_residues
      N a5 q5 a10 q10 hN h5eq hq5ndvd ha5
        h10eq hq10ndvd ha10
  obtain ⟨ha70, ha71, ha72, ha90, ha91, ha92⟩ :=
    base_gauntlet_higher_adic_depth_residues
      N a7 q7 a9 q9 hN h7eq hq7ndvd ha7 h9eq hq9ndvd ha9
  have hval7 : 2520 * N - 7 = 7 ^ (a7 + 1) * q7 := by
    rw [hfac7, h7eq, pow_succ]
    ring
  have hcop7 : Nat.Coprime (7 ^ (a7 + 1)) q7 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hq7ndvd)
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ (a7 + 1)) = a7 + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map,
      Finset.card_range]
  have hbud7 : (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 := by
    have heq : ArithmeticFunction.sigma 0 (2520 * N - 7) =
        (a7 + 2) * ArithmeticFunction.sigma 0 q7 := by
      rw [hval7,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop7,
        hs7]
    rwa [heq] at h7
  have hq7alt := base_gauntlet_q7_composite_forces_depth_zero
    N a7 q7 hN h7eq hq7gt hbud7
  have hq7refined :
      (Nat.Prime q7 ∧ a7 ≤ 2) ∨
        (a7 = 0 ∧
          ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
            ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
              q7 = p * q ∧
              ((p % 3 = 1 ∧ q % 3 = 2) ∨
                (p % 3 = 2 ∧ q % 3 = 1)))) := by
    rcases hq7alt with hprime | hcomposite
    · exact Or.inl hprime
    · exact Or.inr ⟨hcomposite.1,
        (base_gauntlet_q7_composite_factor_residues
          N a7 q7 hN h7eq).2 hcomposite.2⟩
  exact ⟨a5, q5, a7, q7, a9, q9, a10, q10,
    h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
    h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
    hq5prime, hq9prime, hq10prime,
    ha5, ha7, ha9, ha10, hsplit, hsum,
    ha5res, ha10res, ha70, ha71, ha72, ha90, ha91, ha92, hq7refined⟩

def depth5 (N : ℕ) : ℕ := if N % 5 = 4 then 1 else 0

def depth7 (N : ℕ) : ℕ :=
  if N % 49 = 26 then 2 else if N % 7 = 5 then 1 else 0

def depth9 (N : ℕ) : ℕ :=
  if N % 9 = 1 then 2 else if N % 3 = 1 then 1 else 0

def depth10 (N : ℕ) : ℕ := if N % 5 = 3 then 1 else 0

/-- Every candidate has a four-cofactor base state in which the adic depths
are explicit functions of the three small residue coordinates of N. -/
theorem candidate_normalized_base_survivor_state :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ q5 q7 q9 q10 : ℕ,
        504 * N - 1 = 5 ^ depth5 N * q5 ∧ ¬ 5 ∣ q5 ∧ 1 < q5 ∧
        360 * N - 1 = 7 ^ depth7 N * q7 ∧ ¬ 7 ∣ q7 ∧ 1 < q7 ∧
        280 * N - 1 = 3 ^ depth9 N * q9 ∧ ¬ 3 ∣ q9 ∧ 1 < q9 ∧
        252 * N - 1 = 5 ^ depth10 N * q10 ∧ ¬ 5 ∣ q10 ∧ 1 < q10 ∧
        Nat.Prime q5 ∧ Nat.Prime q9 ∧ Nat.Prime q10 ∧
        (depth5 N = 0 ∨ depth10 N = 0) ∧
        depth5 N + depth7 N + depth9 N + depth10 N ≤ 5 ∧
        (Nat.Prime q7 ∨
          (depth7 N = 0 ∧
            ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
              ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
                q7 = p * q ∧
                ((p % 3 = 1 ∧ q % 3 = 2) ∨
                  (p % 3 = 2 ∧ q % 3 = 1))))) := by
  intro n N hn84 hnN H
  obtain ⟨a5, q5, a7, q7, a9, q9, a10, q10,
      h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
      h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
      hq5prime, hq9prime, hq10prime,
      ha5, ha7, ha9, ha10, hsplit, hsum,
      ha5res, ha10res, ha70, ha71, ha72, ha90, ha91, ha92, hq7alt⟩ :=
    candidate_exact_base_survivor_state_with_bounds n N hn84 hnN H
  have hdepth5 : a5 = depth5 N := by
    unfold depth5
    split_ifs with h
    · exact ha5res.mpr h
    · have hne : a5 ≠ 1 := fun ha => h (ha5res.mp ha)
      omega
  have hdepth10 : a10 = depth10 N := by
    unfold depth10
    split_ifs with h
    · exact ha10res.mpr h
    · have hne : a10 ≠ 1 := fun ha => h (ha10res.mp ha)
      omega
  have hdepth7 : a7 = depth7 N := by
    unfold depth7
    split_ifs with h49 h7
    · exact ha72.mpr h49
    · exact ha71.mpr ⟨h7, h49⟩
    · exact ha70.mpr h7
  have hdepth9 : a9 = depth9 N := by
    unfold depth9
    split_ifs with h9 h3
    · exact ha92.mpr h9
    · exact ha91.mpr ⟨h3, h9⟩
    · exact ha90.mpr h3
  subst a5
  subst a7
  subst a9
  subst a10
  have hq7normalized :
      Nat.Prime q7 ∨
        (depth7 N = 0 ∧
          ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
            ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
              q7 = p * q ∧
              ((p % 3 = 1 ∧ q % 3 = 2) ∨
                (p % 3 = 2 ∧ q % 3 = 1)))) := by
    rcases hq7alt with hprime | hcomposite
    · exact Or.inl hprime.1
    · exact Or.inr hcomposite
  exact ⟨q5, q7, q9, q10,
    h5eq, hq5ndvd, hq5gt, h7eq, hq7ndvd, hq7gt,
    h9eq, hq9ndvd, hq9gt, h10eq, hq10ndvd, hq10gt,
    hq5prime, hq9prime, hq10prime, hsplit, hsum, hq7normalized⟩

/-- The normalized cofactors inherit the complete six-edge coprimality clique
from their four ambient rung cofactors. -/
theorem normalized_cofactors_pairwise_coprime :
    ∀ N q5 q7 q9 q10 : ℕ, 1 ≤ N →
      504 * N - 1 = 5 ^ depth5 N * q5 →
      360 * N - 1 = 7 ^ depth7 N * q7 →
      280 * N - 1 = 3 ^ depth9 N * q9 →
      252 * N - 1 = 5 ^ depth10 N * q10 →
      Nat.Coprime q5 q7 ∧ Nat.Coprime q5 q9 ∧
      Nat.Coprime q5 q10 ∧ Nat.Coprime q7 q9 ∧
      Nat.Coprime q7 q10 ∧ Nat.Coprime q9 q10 := by
  intro N q5 q7 q9 q10 hN h5 h7 h9 h10
  have hq5dvd : q5 ∣ 504 * N - 1 := by
    rw [h5]
    exact dvd_mul_left q5 _
  have hq7dvd : q7 ∣ 360 * N - 1 := by
    rw [h7]
    exact dvd_mul_left q7 _
  have hq9dvd : q9 ∣ 280 * N - 1 := by
    rw [h9]
    exact dvd_mul_left q9 _
  have hq10dvd : q10 ∣ 252 * N - 1 := by
    rw [h10]
    exact dvd_mul_left q10 _
  let M := N - 1
  have hNM : N = M + 1 := by dsimp [M]; omega
  have h504 : 504 * N - 1 = 504 * M + 503 := by dsimp [M]; omega
  have h360 : 360 * N - 1 = 360 * M + 359 := by dsimp [M]; omega
  have h280 : 280 * N - 1 = 280 * M + 279 := by dsimp [M]; omega
  have h252 : 252 * N - 1 = 252 * M + 251 := by dsimp [M]; omega
  have coprime_of_relation : ∀ A C u v : ℕ,
      u * A = v * C + 1 → Nat.Coprime A C := by
    intro A C u v hrel
    apply Nat.coprime_of_dvd'
    intro p hp hpA hpC
    have hpUA : p ∣ u * A := Dvd.dvd.mul_left hpA u
    have hpVC : p ∣ v * C := Dvd.dvd.mul_left hpC v
    have hpVC1 : p ∣ v * C + 1 := hrel ▸ hpUA
    exact (Nat.dvd_add_right hpVC).mp hpVC1
  have h57 : Nat.Coprime (504 * N - 1) (360 * N - 1) := by
    apply coprime_of_relation _ _ (900 * N) (1260 * N + 1)
    rw [h504, h360, hNM]
    ring
  have h59 : Nat.Coprime (504 * N - 1) (280 * N - 1) := by
    apply coprime_of_relation _ _ (350 * N) (630 * N + 1)
    rw [h504, h280, hNM]
    ring
  have h510 : Nat.Coprime (504 * N - 1) (252 * N - 1) := by
    apply coprime_of_relation _ _ 1 2
    omega
  have h79 : Nat.Coprime (360 * N - 1) (280 * N - 1) := by
    apply coprime_of_relation _ _ (980 * N) (1260 * N + 1)
    rw [h360, h280, hNM]
    ring
  have h710 : Nat.Coprime (360 * N - 1) (252 * N - 1) := by
    apply coprime_of_relation _ _ (588 * N) (840 * N + 1)
    rw [h360, h252, hNM]
    ring
  have h910 : Nat.Coprime (280 * N - 1) (252 * N - 1) := by
    apply coprime_of_relation _ _ 9 10
    omega
  exact ⟨
    Nat.Coprime.of_dvd hq5dvd hq7dvd h57,
    Nat.Coprime.of_dvd hq5dvd hq9dvd h59,
    Nat.Coprime.of_dvd hq5dvd hq10dvd h510,
    Nat.Coprime.of_dvd hq7dvd hq9dvd h79,
    Nat.Coprime.of_dvd hq7dvd hq10dvd h710,
    Nat.Coprime.of_dvd hq9dvd hq10dvd h910⟩

/-- Candidate-facing assembly of the normalized local classifications with
the global coprimality clique between their four cofactors. -/
theorem candidate_normalized_coprime_cofactor_clique :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ q5 q7 q9 q10 : ℕ,
        504 * N - 1 = 5 ^ depth5 N * q5 ∧ ¬ 5 ∣ q5 ∧ 1 < q5 ∧
        360 * N - 1 = 7 ^ depth7 N * q7 ∧ ¬ 7 ∣ q7 ∧ 1 < q7 ∧
        280 * N - 1 = 3 ^ depth9 N * q9 ∧ ¬ 3 ∣ q9 ∧ 1 < q9 ∧
        252 * N - 1 = 5 ^ depth10 N * q10 ∧ ¬ 5 ∣ q10 ∧ 1 < q10 ∧
        Nat.Prime q5 ∧ Nat.Prime q9 ∧ Nat.Prime q10 ∧
        (depth5 N = 0 ∨ depth10 N = 0) ∧
        depth5 N + depth7 N + depth9 N + depth10 N ≤ 5 ∧
        (Nat.Prime q7 ∨
          (depth7 N = 0 ∧
            ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧ p % 3 = 2) ∨
              ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
                q7 = p * q ∧
                ((p % 3 = 1 ∧ q % 3 = 2) ∨
                  (p % 3 = 2 ∧ q % 3 = 1))))) ∧
        Nat.Coprime q5 q7 ∧ Nat.Coprime q5 q9 ∧
        Nat.Coprime q5 q10 ∧ Nat.Coprime q7 q9 ∧
        Nat.Coprime q7 q10 ∧ Nat.Coprime q9 q10 := by
  intro n N hn84 hnN H
  obtain ⟨q5, q7, q9, q10,
      h5, h5ndvd, h5gt, h7, h7ndvd, h7gt,
      h9, h9ndvd, h9gt, h10, h10ndvd, h10gt,
      hp5, hp9, hp10, hsplit, hsum, hq7⟩ :=
    candidate_normalized_base_survivor_state n N hn84 hnN H
  have hN : 1 ≤ N := by omega
  obtain ⟨h57, h59, h510, h79, h710, h910⟩ :=
    normalized_cofactors_pairwise_coprime
      N q5 q7 q9 q10 hN h5 h7 h9 h10
  exact ⟨q5, q7, q9, q10,
    h5, h5ndvd, h5gt, h7, h7ndvd, h7gt,
    h9, h9ndvd, h9gt, h10, h10ndvd, h10gt,
    hp5, hp9, hp10, hsplit, hsum, hq7,
    h57, h59, h510, h79, h710, h910⟩

/-- The q7 classification and the coprimality clique expose either four or
five genuinely distinct prime atoms across the four normalized cofactors. -/
theorem four_cofactor_prime_atom_trichotomy :
    ∀ q5 q7 q9 q10 : ℕ,
      Nat.Prime q5 → Nat.Prime q9 → Nat.Prime q10 →
      Nat.Coprime q5 q7 → Nat.Coprime q5 q9 →
      Nat.Coprime q5 q10 → Nat.Coprime q7 q9 →
      Nat.Coprime q7 q10 → Nat.Coprime q9 q10 →
      (Nat.Prime q7 ∨
        ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
          ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q)) →
      (Nat.Prime q7 ∧
          q5 ≠ q7 ∧ q5 ≠ q9 ∧ q5 ≠ q10 ∧
          q7 ≠ q9 ∧ q7 ≠ q10 ∧ q9 ≠ q10) ∨
        (∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3 ∧
          q5 ≠ p ∧ q9 ≠ p ∧ q10 ≠ p ∧
          q5 ≠ q9 ∧ q5 ≠ q10 ∧ q9 ≠ q10) ∨
        (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q ∧
          q5 ≠ p ∧ q5 ≠ q ∧ q9 ≠ p ∧ q9 ≠ q ∧
          q10 ≠ p ∧ q10 ≠ q ∧
          q5 ≠ q9 ∧ q5 ≠ q10 ∧ q9 ≠ q10) := by
  intro q5 q7 q9 q10 hp5 hp9 hp10 h57 h59 h510 h79 h710 h910 hq7
  have distinct_of_coprime : ∀ {a b : ℕ},
      Nat.Prime a → Nat.Prime b → Nat.Coprime a b → a ≠ b := by
    intro a b ha hb hab
    exact (Nat.coprime_primes ha hb).mp hab
  have left_ne_factor : ∀ {a b p : ℕ},
      Nat.Prime a → Nat.Coprime a b → Nat.Prime p → p ∣ b → a ≠ p := by
    intro a b p ha hab hp hpdiv hap
    subst p
    exact ha.ne_one (Nat.eq_one_of_dvd_coprimes hab (dvd_refl a) hpdiv)
  have h59ne : q5 ≠ q9 := distinct_of_coprime hp5 hp9 h59
  have h510ne : q5 ≠ q10 := distinct_of_coprime hp5 hp10 h510
  have h910ne : q9 ≠ q10 := distinct_of_coprime hp9 hp10 h910
  rcases hq7 with hp7 | hcomp
  · exact Or.inl ⟨hp7,
      distinct_of_coprime hp5 hp7 h57,
      h59ne, h510ne,
      distinct_of_coprime hp7 hp9 h79,
      distinct_of_coprime hp7 hp10 h710,
      h910ne⟩
  · rcases hcomp with ⟨p, hp, hq7cube⟩ | ⟨p, q, hp, hq, hpq, hq7prod⟩
    · have hpdvd : p ∣ q7 := by
        rw [hq7cube]
        exact dvd_pow_self p (by omega)
      exact Or.inr (Or.inl ⟨p, hp, hq7cube,
        left_ne_factor hp5 h57 hp hpdvd,
        left_ne_factor hp9 h79.symm hp hpdvd,
        left_ne_factor hp10 h710.symm hp hpdvd,
        h59ne, h510ne, h910ne⟩)
    · have hpdvd : p ∣ q7 := by rw [hq7prod]; exact dvd_mul_right p q
      have hqdvd : q ∣ q7 := by rw [hq7prod]; exact dvd_mul_left q p
      exact Or.inr (Or.inr ⟨p, q, hp, hq, hpq, hq7prod,
        left_ne_factor hp5 h57 hp hpdvd,
        left_ne_factor hp5 h57 hq hqdvd,
        left_ne_factor hp9 h79.symm hp hpdvd,
        left_ne_factor hp9 h79.symm hq hqdvd,
        left_ne_factor hp10 h710.symm hp hpdvd,
        left_ne_factor hp10 h710.symm hq hqdvd,
        h59ne, h510ne, h910ne⟩)

/-- Every remaining candidate supplies four pairwise-distinct primes larger
than ten at the exact base shifts `5,7,9,10`.  In the composite q7 branches
we select one of its certified prime atoms. -/
theorem candidate_base_rungs_supply_large_distinct_primes :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ p5 p7 p9 p10 : ℕ,
        Nat.Prime p5 ∧ 10 < p5 ∧ p5 ∣ n - 5 ∧
        Nat.Prime p7 ∧ 10 < p7 ∧ p7 ∣ n - 7 ∧
        Nat.Prime p9 ∧ 10 < p9 ∧ p9 ∣ n - 9 ∧
        Nat.Prime p10 ∧ 10 < p10 ∧ p10 ∣ n - 10 ∧
        p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
        p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 := by
  intro n N hn84 hnN H
  obtain ⟨q5, q7, q9, q10,
      h5, h5ndvd, h5gt, h7, h7ndvd, h7gt,
      h9, h9ndvd, h9gt, h10, h10ndvd, h10gt,
      hp5, hp9, hp10, hsplit, hsum, hq7,
      h57, h59, h510, h79, h710, h910⟩ :=
    candidate_normalized_coprime_cofactor_clique n N hn84 hnN H
  have hN : 1 ≤ N := by omega
  have hq5host : q5 ∣ 504 * N - 1 := by rw [h5]; exact dvd_mul_left q5 _
  have hq7host : q7 ∣ 360 * N - 1 := by rw [h7]; exact dvd_mul_left q7 _
  have hq9host : q9 ∣ 280 * N - 1 := by rw [h9]; exact dvd_mul_left q9 _
  have hq10host : q10 ∣ 252 * N - 1 := by rw [h10]; exact dvd_mul_left q10 _
  obtain ⟨p7, hp7, hp7q7⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ q7 := by
    rcases hq7 with hp7 | ⟨hdepth, hcube | hsemi⟩
    · exact ⟨q7, hp7, dvd_refl q7⟩
    · obtain ⟨p, hp, hq7cube, hpmod⟩ := hcube
      refine ⟨p, hp, ?_⟩
      rw [hq7cube]
      exact dvd_pow_self p (by omega)
    · obtain ⟨p, q, hp, hq, hpq, hq7prod, hmods⟩ := hsemi
      refine ⟨p, hp, ?_⟩
      rw [hq7prod]
      exact dvd_mul_right p q
  have hp7host : p7 ∣ 360 * N - 1 := hp7q7.trans hq7host
  have hNpos : 0 < N := by omega
  have not_small_dvd_host : ∀ p A : ℕ, 1 < p → 0 < A →
      p ∣ A → p ∣ A * N - 1 → False := by
    intro p A hpgt hA hpA hpHost
    have hpAN : p ∣ A * N := Dvd.dvd.mul_right hpA N
    have hpOne : p ∣ 1 := by
      have hpSum : p ∣ (A * N - 1) + 1 := by
        rw [Nat.sub_add_cancel (Nat.mul_pos hA hNpos)]
        exact hpAN
      exact (Nat.dvd_add_right hpHost).mp hpSum
    have hpEq : p = 1 := Nat.dvd_one.mp hpOne
    omega
  have prime_gt_ten : ∀ p : ℕ, Nat.Prime p →
      ¬ 2 ∣ p → ¬ 3 ∣ p → ¬ 5 ∣ p → ¬ 7 ∣ p → 10 < p := by
    intro p hp h2 h3 h5 h7
    by_contra hle
    have hp2 := hp.two_le
    have hcases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨
        p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h
    · subst p; exact h2 (by norm_num)
    · subst p; exact h3 (by norm_num)
    · subst p; norm_num at hp
    · subst p; exact h5 (by norm_num)
    · subst p; norm_num at hp
    · subst p; exact h7 (by norm_num)
    · subst p; norm_num at hp
    · subst p; norm_num at hp
    · subst p; norm_num at hp
  have hq5large : 10 < q5 := by
    apply prime_gt_ten q5 hp5
    · intro h; exact not_small_dvd_host 2 504 (by norm_num) (by norm_num) (by norm_num) (h.trans hq5host)
    · intro h; exact not_small_dvd_host 3 504 (by norm_num) (by norm_num) (by norm_num) (h.trans hq5host)
    · exact h5ndvd
    · intro h; exact not_small_dvd_host 7 504 (by norm_num) (by norm_num) (by norm_num) (h.trans hq5host)
  have hp7large : 10 < p7 := by
    apply prime_gt_ten p7 hp7
    · intro h; exact not_small_dvd_host 2 360 (by norm_num) (by norm_num) (by norm_num) (h.trans hp7host)
    · intro h; exact not_small_dvd_host 3 360 (by norm_num) (by norm_num) (by norm_num) (h.trans hp7host)
    · intro h; exact not_small_dvd_host 5 360 (by norm_num) (by norm_num) (by norm_num) (h.trans hp7host)
    · intro h; exact h7ndvd ((h.trans hp7q7))
  have hq9large : 10 < q9 := by
    apply prime_gt_ten q9 hp9
    · intro h; exact not_small_dvd_host 2 280 (by norm_num) (by norm_num) (by norm_num) (h.trans hq9host)
    · exact h9ndvd
    · intro h; exact not_small_dvd_host 5 280 (by norm_num) (by norm_num) (by norm_num) (h.trans hq9host)
    · intro h; exact not_small_dvd_host 7 280 (by norm_num) (by norm_num) (by norm_num) (h.trans hq9host)
  have hq10large : 10 < q10 := by
    apply prime_gt_ten q10 hp10
    · intro h; exact not_small_dvd_host 2 252 (by norm_num) (by norm_num) (by norm_num) (h.trans hq10host)
    · intro h; exact not_small_dvd_host 3 252 (by norm_num) (by norm_num) (by norm_num) (h.trans hq10host)
    · exact h10ndvd
    · intro h; exact not_small_dvd_host 7 252 (by norm_num) (by norm_num) (by norm_num) (h.trans hq10host)
  have h5dvd : q5 ∣ n - 5 := by
    rw [hnN]
    have heq : 2520 * N - 5 = 5 * (504 * N - 1) := by omega
    rw [heq]
    exact Dvd.dvd.mul_left hq5host 5
  have h7dvd : p7 ∣ n - 7 := by
    rw [hnN]
    have heq : 2520 * N - 7 = 7 * (360 * N - 1) := by omega
    rw [heq]
    exact Dvd.dvd.mul_left hp7host 7
  have h9dvd : q9 ∣ n - 9 := by
    rw [hnN]
    have heq : 2520 * N - 9 = 9 * (280 * N - 1) := by omega
    rw [heq]
    exact Dvd.dvd.mul_left hq9host 9
  have h10dvd : q10 ∣ n - 10 := by
    rw [hnN]
    have heq : 2520 * N - 10 = 10 * (252 * N - 1) := by omega
    rw [heq]
    exact Dvd.dvd.mul_left hq10host 10
  have left_ne_factor : ∀ {a b p : ℕ},
      Nat.Prime a → Nat.Coprime a b → Nat.Prime p → p ∣ b → a ≠ p := by
    intro a b p ha hab hp hpdiv hap
    subst p
    exact ha.ne_one (Nat.eq_one_of_dvd_coprimes hab (dvd_refl a) hpdiv)
  have h5ne7 : q5 ≠ p7 := left_ne_factor hp5 h57 hp7 hp7q7
  have h7ne9 : p7 ≠ q9 :=
    (left_ne_factor hp9 h79.symm hp7 hp7q7).symm
  have h7ne10 : p7 ≠ q10 :=
    (left_ne_factor hp10 h710.symm hp7 hp7q7).symm
  exact ⟨q5, p7, q9, q10,
    hp5, hq5large, h5dvd,
    hp7, hp7large, h7dvd,
    hp9, hq9large, h9dvd,
    hp10, hq10large, h10dvd,
    h5ne7, (Nat.coprime_primes hp5 hp9).mp h59,
    (Nat.coprime_primes hp5 hp10).mp h510,
    h7ne9, h7ne10, (Nat.coprime_primes hp9 hp10).mp h910⟩

/-- Indexed form of the four large base-rung primes.  This removes the last
tuple-level impedance mismatch before an arbitrary-shift CRT re-entry step. -/
theorem candidate_base_rungs_indexed_large_primes :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ (shift P : Fin 4 → ℕ),
        shift 0 = 5 ∧ shift 1 = 7 ∧ shift 2 = 9 ∧ shift 3 = 10 ∧
        (∀ i : Fin 4,
          Nat.Prime (P i) ∧ 10 < P i ∧ P i ∣ n - shift i) ∧
        Function.Injective P := by
  intro n N hn84 hnN H
  obtain ⟨p5, p7, p9, p10,
      hp5, hp5large, hp5dvd,
      hp7, hp7large, hp7dvd,
      hp9, hp9large, hp9dvd,
      hp10, hp10large, hp10dvd,
      h57, h59, h510, h79, h710, h910⟩ :=
    candidate_base_rungs_supply_large_distinct_primes n N hn84 hnN H
  let shift : Fin 4 → ℕ := ![5, 7, 9, 10]
  let P : Fin 4 → ℕ := ![p5, p7, p9, p10]
  refine ⟨shift, P, by rfl, by rfl, by rfl, by rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [P, shift, hp5, hp5large, hp5dvd,
      hp7, hp7large, hp7dvd, hp9, hp9large, hp9dvd,
      hp10, hp10large, hp10dvd]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [P]

/-- Exact candidate-facing base-prime dichotomy.  Either the product of the
four distinct primes already reaches `n`, or their CRT re-entry remainder must
pay the four-prime divisor budget `16`. -/
theorem candidate_base_prime_product_or_reentry :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ p5 p7 p9 p10 : ℕ,
        Nat.Prime p5 ∧ 10 < p5 ∧ p5 ∣ n - 5 ∧
        Nat.Prime p7 ∧ 10 < p7 ∧ p7 ∣ n - 7 ∧
        Nat.Prime p9 ∧ 10 < p9 ∧ p9 ∣ n - 9 ∧
        Nat.Prime p10 ∧ 10 < p10 ∧ p10 ∣ n - 10 ∧
        p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
        p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 ∧
        (n ≤ p5 * p7 * p9 * p10 ∨
          16 ≤ n % (p5 * p7 * p9 * p10) + 2) := by
  classical
  intro n N hn84 hnN hcand
  obtain ⟨p5, p7, p9, p10,
      hp5, hp5large, hp5dvd,
      hp7, hp7large, hp7dvd,
      hp9, hp9large, hp9dvd,
      hp10, hp10large, hp10dvd,
      h57, h59, h510, h79, h710, h910⟩ :=
    candidate_base_rungs_supply_large_distinct_primes n N hn84 hnN hcand
  refine ⟨p5, p7, p9, p10,
    hp5, hp5large, hp5dvd,
    hp7, hp7large, hp7dvd,
    hp9, hp9large, hp9dvd,
    hp10, hp10large, hp10dvd,
    h57, h59, h510, h79, h710, h910, ?_⟩
  let Q := p5 * p7 * p9 * p10
  by_cases hQn : Q < n
  · right
    have hQpos : 0 < Q := by
      dsimp [Q]
      positivity
    have hp5Q : p5 ∣ Q := by
      dsimp [Q]
      exact ⟨p7 * p9 * p10, by ring⟩
    have hp7Q : p7 ∣ Q := by
      dsimp [Q]
      exact ⟨p5 * p9 * p10, by ring⟩
    have hp9Q : p9 ∣ Q := by
      dsimp [Q]
      exact ⟨p5 * p7 * p10, by ring⟩
    have hp10Q : p10 ∣ Q := by
      dsimp [Q]
      exact ⟨p5 * p7 * p9, by ring⟩
    have hQnotdvd : ¬ Q ∣ n := by
      intro hQdvd
      have hp5n : p5 ∣ n := hp5Q.trans hQdvd
      have h := Nat.dvd_sub hp5n hp5dvd
      have heq : n - (n - 5) = 5 := by omega
      have hp5five : p5 ∣ 5 := by rwa [heq] at h
      have hp5le : p5 ≤ 5 := Nat.le_of_dvd (by norm_num) hp5five
      omega
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
    let S : Finset ℕ := {p5, p7, p9, p10}
    have hScard : S.card = 4 := by
      dsimp [S]
      simp [h57, h59, h510, h79, h710, h910]
    have hS : ∀ p ∈ S, p.Prime ∧ p ∣ n - n % Q := by
      intro p hp
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨hp5, hp5Q.trans hQhost⟩
      · exact ⟨hp7, hp7Q.trans hQhost⟩
      · exact ⟨hp9, hp9Q.trans hQhost⟩
      · exact ⟨hp10, hp10Q.trans hQhost⟩
    have htau : 16 ≤ ArithmeticFunction.sigma 0 (n - n % Q) := by
      rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hhostpos.ne']
      have hsubset : S ⊆ (n - n % Q).primeFactors := by
        intro p hp
        exact Nat.mem_primeFactors.mpr
          ⟨(hS p hp).1, (hS p hp).2, hhostpos.ne'⟩
      have hcard : 4 ≤ (n - n % Q).primeFactors.card := by
        rw [← hScard]
        exact Finset.card_le_card hsubset
      have hpow : 2 ^ (n - n % Q).primeFactors.card ≤
          ∏ p ∈ (n - n % Q).primeFactors,
            ((n - n % Q).factorization p + 1) := by
        apply Finset.pow_card_le_prod
        intro p hp
        have hp' : p ∈ (n - n % Q).factorization.support := by simpa using hp
        have hfac : (n - n % Q).factorization p ≠ 0 :=
          Finsupp.mem_support_iff.mp hp'
        omega
      exact (pow_le_pow_right' (by norm_num) hcard).trans hpow
    let f : Fin n → ℕ := fun x =>
      (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hcard := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - n % Q, by omega⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) hcand
    dsimp [f, m] at hm
    have hbudget : ArithmeticFunction.sigma 0 (n - n % Q) ≤ n % Q + 2 := by
      omega
    simpa [Q] using htau.trans hbudget
  · left
    simpa [Q] using Nat.le_of_not_gt hQn

/-- Sharpened numerical form: in the proper-product branch the CRT remainder
lies in the explicit interval `[14,Q)`. -/
theorem candidate_base_prime_product_or_large_remainder :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ p5 p7 p9 p10 : ℕ,
        Nat.Prime p5 ∧ 10 < p5 ∧ p5 ∣ n - 5 ∧
        Nat.Prime p7 ∧ 10 < p7 ∧ p7 ∣ n - 7 ∧
        Nat.Prime p9 ∧ 10 < p9 ∧ p9 ∣ n - 9 ∧
        Nat.Prime p10 ∧ 10 < p10 ∧ p10 ∣ n - 10 ∧
        p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
        p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 ∧
        (n ≤ p5 * p7 * p9 * p10 ∨
          (p5 * p7 * p9 * p10 < n ∧
            14 ≤ n % (p5 * p7 * p9 * p10) ∧
            n % (p5 * p7 * p9 * p10) < p5 * p7 * p9 * p10)) := by
  intro n N hn84 hnN hcand
  obtain ⟨p5, p7, p9, p10,
      hp5, hp5large, hp5dvd,
      hp7, hp7large, hp7dvd,
      hp9, hp9large, hp9dvd,
      hp10, hp10large, hp10dvd,
      h57, h59, h510, h79, h710, h910, halt⟩ :=
    candidate_base_prime_product_or_reentry n N hn84 hnN hcand
  refine ⟨p5, p7, p9, p10,
    hp5, hp5large, hp5dvd,
    hp7, hp7large, hp7dvd,
    hp9, hp9large, hp9dvd,
    hp10, hp10large, hp10dvd,
    h57, h59, h510, h79, h710, h910, ?_⟩
  let Q := p5 * p7 * p9 * p10
  by_cases hQn : Q < n
  · right
    have hQpos : 0 < Q := by dsimp [Q]; positivity
    have hbound : 16 ≤ n % Q + 2 := by
      rcases halt with hlarge | hbound
      · exfalso
        exact (not_lt_of_ge (by simpa [Q] using hlarge)) hQn
      · simpa [Q] using hbound
    exact ⟨hQn, by omega, Nat.mod_lt n hQpos⟩
  · left
    simpa [Q] using Nat.le_of_not_gt hQn

/-- Self-contained four-rung residue accumulation: exact shift residues force
some three-prime subproduct below the cube of the CRT remainder. -/
theorem base_four_prime_remainder_triple_bound :
    ∀ n p5 p7 p9 p10 : ℕ,
      10 < n →
      p5.Prime → 10 < p5 → p5 ∣ n - 5 →
      p7.Prime → 10 < p7 → p7 ∣ n - 7 →
      p9.Prime → 10 < p9 → p9 ∣ n - 9 →
      p10.Prime → 10 < p10 → p10 ∣ n - 10 →
      let R := n % (p5 * p7 * p9 * p10)
      p5 * p7 * p9 ≤ R ^ 3 ∨ p5 * p7 * p10 ≤ R ^ 3 ∨
        p5 * p9 * p10 ≤ R ^ 3 ∨ p7 * p9 * p10 ≤ R ^ 3 := by
  classical
  intro n p5 p7 p9 p10 hn
    hp5 hp5large hp5dvd hp7 hp7large hp7dvd
    hp9 hp9large hp9dvd hp10 hp10large hp10dvd
  let Q := p5 * p7 * p9 * p10
  let R := n % Q
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hp5Q : p5 ∣ Q := by dsimp [Q]; exact ⟨p7 * p9 * p10, by ring⟩
  have hp7Q : p7 ∣ Q := by dsimp [Q]; exact ⟨p5 * p9 * p10, by ring⟩
  have hp9Q : p9 ∣ Q := by dsimp [Q]; exact ⟨p5 * p7 * p10, by ring⟩
  have hp10Q : p10 ∣ Q := by dsimp [Q]; exact ⟨p5 * p7 * p9, by ring⟩
  have residue : ∀ p s : ℕ, p ∣ Q → s < p → s < n →
      p ∣ n - s → R % p = s := by
    intro p s hpQ hsp hsn hpdvd
    have hsplit : n = s + (n - s) := by
      simpa [Nat.add_comm] using (Nat.sub_add_cancel hsn.le).symm
    have hzero : (n - s) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpdvd
    calc
      R % p = n % p := Nat.mod_mod_of_dvd n hpQ
      _ = (s + (n - s)) % p := by rw [← hsplit]
      _ = s := by
        simpa [Nat.add_mod, hzero] using Nat.mod_eq_of_lt hsp
  have pair_bound : ∀ p s q t : ℕ,
      p ∣ Q → q ∣ Q → s < p → t < q → s < n → t < n →
      p ∣ n - s → q ∣ n - t → s ≠ t → p ≤ R ∨ q ≤ R := by
    intro p s q t hpQ hqQ hsp htq hsn htn hpd hqd hst
    by_cases hpR : p ≤ R
    · exact Or.inl hpR
    right
    by_contra hqR
    have hRp : R < p := Nat.lt_of_not_ge hpR
    have hRq : R < q := Nat.lt_of_not_ge hqR
    have hrs : R = s := by
      have h := residue p s hpQ hsp hsn hpd
      rwa [Nat.mod_eq_of_lt hRp] at h
    have hrt : R = t := by
      have h := residue q t hqQ htq htn hqd
      rwa [Nat.mod_eq_of_lt hRq] at h
    exact hst (hrs.symm.trans hrt)
  have h57 : p5 ≤ R ∨ p7 ≤ R :=
    pair_bound p5 5 p7 7 hp5Q hp7Q (by omega) (by omega)
      (by omega) (by omega) hp5dvd hp7dvd (by norm_num)
  have h59 : p5 ≤ R ∨ p9 ≤ R :=
    pair_bound p5 5 p9 9 hp5Q hp9Q (by omega) (by omega)
      (by omega) (by omega) hp5dvd hp9dvd (by norm_num)
  have h510 : p5 ≤ R ∨ p10 ≤ R :=
    pair_bound p5 5 p10 10 hp5Q hp10Q (by omega) (by omega)
      (by omega) (by omega) hp5dvd hp10dvd (by norm_num)
  have h79 : p7 ≤ R ∨ p9 ≤ R :=
    pair_bound p7 7 p9 9 hp7Q hp9Q (by omega) (by omega)
      (by omega) (by omega) hp7dvd hp9dvd (by norm_num)
  have h710 : p7 ≤ R ∨ p10 ≤ R :=
    pair_bound p7 7 p10 10 hp7Q hp10Q (by omega) (by omega)
      (by omega) (by omega) hp7dvd hp10dvd (by norm_num)
  have h910 : p9 ≤ R ∨ p10 ≤ R :=
    pair_bound p9 9 p10 10 hp9Q hp10Q (by omega) (by omega)
      (by omega) (by omega) hp9dvd hp10dvd (by norm_num)
  have triple_le : ∀ {x y z : ℕ}, x ≤ R → y ≤ R → z ≤ R →
      x * y * z ≤ R ^ 3 := by
    intro x y z hx hy hz
    calc
      x * y * z ≤ R * R * R := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
      _ = R ^ 3 := by ring
  dsimp
  change p5 * p7 * p9 ≤ R ^ 3 ∨ p5 * p7 * p10 ≤ R ^ 3 ∨
    p5 * p9 * p10 ≤ R ^ 3 ∨ p7 * p9 * p10 ≤ R ^ 3
  by_cases h5 : p5 ≤ R
  · by_cases h7 : p7 ≤ R
    · by_cases h9 : p9 ≤ R
      · exact Or.inl (triple_le h5 h7 h9)
      · exact Or.inr (Or.inl (triple_le h5 h7 (h910.resolve_left h9)))
    · exact Or.inr (Or.inr (Or.inl
        (triple_le h5 (h79.resolve_left h7) (h710.resolve_left h7))))
  · exact Or.inr (Or.inr (Or.inr
      (triple_le (h57.resolve_left h5) (h59.resolve_left h5)
        (h510.resolve_left h5))))

/-- A genuine candidate carries the exact four-prime product/remainder alternative
together with the cubic restriction forced by its four distinct shift residues. -/
theorem candidate_base_prime_product_or_cubic_remainder :
    ∀ n N : ℕ, 84 < n → n = 2520 * N →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ p5 p7 p9 p10 : ℕ,
        Nat.Prime p5 ∧ 10 < p5 ∧ p5 ∣ n - 5 ∧
        Nat.Prime p7 ∧ 10 < p7 ∧ p7 ∣ n - 7 ∧
        Nat.Prime p9 ∧ 10 < p9 ∧ p9 ∣ n - 9 ∧
        Nat.Prime p10 ∧ 10 < p10 ∧ p10 ∣ n - 10 ∧
        p5 ≠ p7 ∧ p5 ≠ p9 ∧ p5 ≠ p10 ∧
        p7 ≠ p9 ∧ p7 ≠ p10 ∧ p9 ≠ p10 ∧
        (n ≤ p5 * p7 * p9 * p10 ∨
          (p5 * p7 * p9 * p10 < n ∧
            14 ≤ n % (p5 * p7 * p9 * p10) ∧
            n % (p5 * p7 * p9 * p10) < p5 * p7 * p9 * p10 ∧
            (p5 * p7 * p9 ≤ (n % (p5 * p7 * p9 * p10)) ^ 3 ∨
             p5 * p7 * p10 ≤ (n % (p5 * p7 * p9 * p10)) ^ 3 ∨
             p5 * p9 * p10 ≤ (n % (p5 * p7 * p9 * p10)) ^ 3 ∨
             p7 * p9 * p10 ≤ (n % (p5 * p7 * p9 * p10)) ^ 3))) := by
  intro n N hn84 hnN hcand
  obtain ⟨p5, p7, p9, p10,
      hp5, hp5large, hp5dvd,
      hp7, hp7large, hp7dvd,
      hp9, hp9large, hp9dvd,
      hp10, hp10large, hp10dvd,
      h57, h59, h510, h79, h710, h910, hbranch⟩ :=
    candidate_base_prime_product_or_large_remainder n N hn84 hnN hcand
  have htriple := base_four_prime_remainder_triple_bound n p5 p7 p9 p10
    (by omega) hp5 hp5large hp5dvd hp7 hp7large hp7dvd
    hp9 hp9large hp9dvd hp10 hp10large hp10dvd
  refine ⟨p5, p7, p9, p10,
    hp5, hp5large, hp5dvd,
    hp7, hp7large, hp7dvd,
    hp9, hp9large, hp9dvd,
    hp10, hp10large, hp10dvd,
    h57, h59, h510, h79, h710, h910, ?_⟩
  rcases hbranch with hsmall | ⟨hlarge, hR14, hRlt⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hlarge, hR14, hRlt, htriple⟩

/-- If one of the four three-factor subproducts is controlled by `R^3`, then
the whole product is controlled by `R^3` times the one omitted factor.  This
isolates the sole prime that can remain exceptional after CRT reentry. -/
theorem four_factor_one_exception_envelope :
    ∀ a b c d R : ℕ,
      (a * b * c ≤ R ^ 3 ∨ a * b * d ≤ R ^ 3 ∨
        a * c * d ≤ R ^ 3 ∨ b * c * d ≤ R ^ 3) →
      a * b * c * d ≤ R ^ 3 * d ∨
        a * b * c * d ≤ R ^ 3 * c ∨
        a * b * c * d ≤ R ^ 3 * b ∨
        a * b * c * d ≤ R ^ 3 * a := by
  intro a b c d R h
  rcases h with habc | habd | hacd | hbcd
  · exact Or.inl (Nat.mul_le_mul_right d habc)
  · right
    left
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_le_mul_right c habd)
  · right
    right
    left
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_le_mul_right b hacd)
  · right
    right
    right
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.mul_le_mul_right a hbcd)

end Erdos647.ExactBaseState
