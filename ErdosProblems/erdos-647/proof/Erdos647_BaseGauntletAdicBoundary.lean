import Mathlib

/-!
# Erdős #647 — base-gauntlet total-adic-depth boundary lemma (locked priority 1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  dfc0b1f3-082a-46c2-b8b3-ccb3428e5969
  episode_id          982a1f59-d072-4aa9-9aaa-56544ee7869a
  root_statement_hash 44981f8a2719d805e8f30a49aad62833bc618076400e1d72a36ffb9b866aeaee
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     5a7b410e-af81-4855-9365-fa29e38545f3 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a survivor of the base-gauntlet budgets (rungs 5, 7, 9, 10)
carries adic decompositions whose depths are individually and totally
bounded:

  `a₅ ≤ B+3`, `a₇ ≤ B+5`, `a₉ ≤ B+6`, `2·a₁₀ ≤ B+6`,
  `a₅ + a₇ + a₉ + a₁₀ ≤ 4B + 20`.

**Stated honestly as a BOUNDARY lemma, not the accumulation theorem**
(per the strategic review): for fixed `B` this is a fixed bound on a
fixed number of primes, and CRT can accommodate those finitely many
residue demands — this lemma cannot itself imply survival-depth
sublinearity. Its long-term value is to formalize:

> The base block consumes only bounded local digits, so any
> contradiction must come from repeatedly generating new blocks or a
> genuinely growing family of constraints.

The true next negative target is the arbitrary-block production theorem
with a proven novelty/non-reuse condition
(`dossiers/growing-gauntlet-criterion.md`).
-/

theorem erdos647_base_gauntlet_adic_boundary :
    ∀ (N B : ℕ), 1 ≤ N →
      ArithmeticFunction.sigma 0 (2520 * N - 5) ≤ B + 5 →
      ArithmeticFunction.sigma 0 (2520 * N - 7) ≤ B + 7 →
      ArithmeticFunction.sigma 0 (2520 * N - 9) ≤ B + 9 →
      ArithmeticFunction.sigma 0 (2520 * N - 10) ≤ B + 10 →
      ∃ a5 a7 a9 a10 : ℕ,
        5 ^ a5 ∣ 504 * N - 1 ∧ 7 ^ a7 ∣ 360 * N - 1 ∧
        3 ^ a9 ∣ 280 * N - 1 ∧ 5 ^ a10 ∣ 252 * N - 1 ∧
        a5 ≤ B + 3 ∧ a7 ≤ B + 5 ∧ a9 ≤ B + 6 ∧ 2 * a10 ≤ B + 6 ∧
        a5 + a7 + a9 + a10 ≤ 4 * B + 20 := by
  intro N B hN h5 h7 h9 h10
  have hone : ∀ q : ℕ, q ≠ 0 → 1 ≤ ArithmeticFunction.sigma 0 q := by
    intro q hq
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_pos.mpr ⟨q, Nat.mem_divisors_self q hq⟩
  have hr5 : ∃ a : ℕ, 5 ^ a ∣ 504 * N - 1 ∧ a ≤ B + 3 := by
    have hne : 504 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq5, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 5 (by norm_num)
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heq
      omega
    have hval : 2520 * N - 5 = 5 ^ (a + 1) * q := by
      have hx : 2520 * N - 5 = 5 * (504 * N - 1) := by omega
      rw [hx, heq, pow_succ]
      ring
    have hcop : Nat.Coprime (5 ^ (a + 1)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq5)
    have hs : ArithmeticFunction.sigma 0 (5 ^ (a + 1)) = a + 2 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
        Finset.card_range]
    have hsig : ArithmeticFunction.sigma 0 (2520 * N - 5) =
        (a + 2) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
    rw [hsig] at h5
    have hq1 := hone q hqne
    have hb : a + 2 ≤ (a + 2) * ArithmeticFunction.sigma 0 q :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨a, ⟨q, heq⟩, by omega⟩
  have hr7 : ∃ a : ℕ, 7 ^ a ∣ 360 * N - 1 ∧ a ≤ B + 5 := by
    have hne : 360 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq7, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 7 (by norm_num)
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heq
      omega
    have hval : 2520 * N - 7 = 7 ^ (a + 1) * q := by
      have hx : 2520 * N - 7 = 7 * (360 * N - 1) := by omega
      rw [hx, heq, pow_succ]
      ring
    have hcop : Nat.Coprime (7 ^ (a + 1)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hq7)
    have hs : ArithmeticFunction.sigma 0 (7 ^ (a + 1)) = a + 2 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map,
        Finset.card_range]
    have hsig : ArithmeticFunction.sigma 0 (2520 * N - 7) =
        (a + 2) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
    rw [hsig] at h7
    have hq1 := hone q hqne
    have hb : a + 2 ≤ (a + 2) * ArithmeticFunction.sigma 0 q :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨a, ⟨q, heq⟩, by omega⟩
  have hr9 : ∃ a : ℕ, 3 ^ a ∣ 280 * N - 1 ∧ a ≤ B + 6 := by
    have hne : 280 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq3, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 3 (by norm_num)
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heq
      omega
    have hval : 2520 * N - 9 = 3 ^ (a + 2) * q := by
      have hx : 2520 * N - 9 = 9 * (280 * N - 1) := by omega
      rw [hx, heq]
      have h9e : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [h9e, ← mul_assoc, ← pow_add]
      ring_nf
    have hcop : Nat.Coprime (3 ^ (a + 2)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr hq3)
    have hs : ArithmeticFunction.sigma 0 (3 ^ (a + 2)) = a + 3 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 3), Finset.card_map,
        Finset.card_range]
    have hsig : ArithmeticFunction.sigma 0 (2520 * N - 9) =
        (a + 3) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
    rw [hsig] at h9
    have hq1 := hone q hqne
    have hb : a + 3 ≤ (a + 3) * ArithmeticFunction.sigma 0 q :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨a, ⟨q, heq⟩, by omega⟩
  have hr10 : ∃ a : ℕ, 5 ^ a ∣ 252 * N - 1 ∧ 2 * a ≤ B + 6 := by
    have hne : 252 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq5, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 5 (by norm_num)
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heq
      omega
    have hqodd : ¬ 2 ∣ q := by
      intro h2q
      have h2 : (2 : ℕ) ∣ 252 * N - 1 := by
        rw [heq]
        exact Dvd.dvd.mul_left h2q (5 ^ a)
      obtain ⟨w, hw⟩ := h2
      omega
    have hval : 2520 * N - 10 = 2 * 5 ^ (a + 1) * q := by
      have hx : 2520 * N - 10 = 10 * (252 * N - 1) := by omega
      rw [hx, heq, pow_succ]
      ring
    have hcop5 : Nat.Coprime (5 ^ (a + 1)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq5)
    have hcop2 : Nat.Coprime 2 q := ((by norm_num : Nat.Prime 2).coprime_iff_not_dvd).mpr hqodd
    have hcop : Nat.Coprime (2 * 5 ^ (a + 1)) q := hcop2.mul_left hcop5
    have hcop25 : Nat.Coprime 2 (5 ^ (a + 1)) := Nat.Coprime.pow_right _ (by norm_num)
    have hs5 : ArithmeticFunction.sigma 0 (5 ^ (a + 1)) = a + 2 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
        Finset.card_range]
    have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
    have hs25 : ArithmeticFunction.sigma 0 (2 * 5 ^ (a + 1)) = 2 * (a + 2) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25, hs2, hs5]
    have hsig : ArithmeticFunction.sigma 0 (2520 * N - 10) =
        2 * (a + 2) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs25]
    rw [hsig] at h10
    have hq1 := hone q hqne
    have hb : 2 * (a + 2) ≤ 2 * (a + 2) * ArithmeticFunction.sigma 0 q :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨a, ⟨q, heq⟩, by omega⟩
  obtain ⟨a5, hd5, hb5⟩ := hr5
  obtain ⟨a7, hd7, hb7⟩ := hr7
  obtain ⟨a9, hd9, hb9⟩ := hr9
  obtain ⟨a10, hd10, hb10⟩ := hr10
  exact ⟨a5, a7, a9, a10, hd5, hd7, hd9, hd10, hb5, hb7, hb9, hb10, by omega⟩

/-- Candidate-budget-facing form of the sharpened base-gauntlet boundary.

The earlier theorem bounded the total depth by `4B+20`.  The rung-5 and
rung-10 cofactors satisfy `504N-1 = 2(252N-1)+1`, so their 5-adic depths
cannot both be positive.  This improves the returned total to `3B+14`.
-/
theorem erdos647_base_gauntlet_adic_boundary_sharpened :
    ∀ (N B : ℕ), 1 ≤ N →
      ArithmeticFunction.sigma 0 (2520 * N - 5) ≤ B + 5 →
      ArithmeticFunction.sigma 0 (2520 * N - 7) ≤ B + 7 →
      ArithmeticFunction.sigma 0 (2520 * N - 9) ≤ B + 9 →
      ArithmeticFunction.sigma 0 (2520 * N - 10) ≤ B + 10 →
      ∃ a5 a7 a9 a10 : ℕ,
        5 ^ a5 ∣ 504 * N - 1 ∧ 7 ^ a7 ∣ 360 * N - 1 ∧
        3 ^ a9 ∣ 280 * N - 1 ∧ 5 ^ a10 ∣ 252 * N - 1 ∧
        a5 ≤ B + 3 ∧ a7 ≤ B + 5 ∧ a9 ≤ B + 6 ∧ 2 * a10 ≤ B + 6 ∧
        a5 + a7 + a9 + a10 ≤ 3 * B + 14 := by
  intro N B hN h5 h7 h9 h10
  obtain ⟨a5, a7, a9, a10, hd5, hd7, hd9, hd10,
      hb5, hb7, hb9, hb10, _⟩ :=
    erdos647_base_gauntlet_adic_boundary N B hN h5 h7 h9 h10
  have hsplit : a5 = 0 ∨ a10 = 0 := by
    by_contra hboth
    push Not at hboth
    have h5pow5 : 5 ∣ 5 ^ a5 := dvd_pow_self 5 hboth.1
    have h5pow10 : 5 ∣ 5 ^ a10 := dvd_pow_self 5 hboth.2
    have h5A : 5 ∣ 504 * N - 1 := h5pow5.trans hd5
    have h5C : 5 ∣ 252 * N - 1 := h5pow10.trans hd10
    have hrel : 504 * N - 1 = 2 * (252 * N - 1) + 1 := by omega
    have h5twice : 5 ∣ 2 * (252 * N - 1) := Dvd.dvd.mul_left h5C 2
    have h5plus : 5 ∣ 2 * (252 * N - 1) + 1 := hrel ▸ h5A
    have h51 : 5 ∣ 1 := (Nat.dvd_add_right h5twice).mp h5plus
    norm_num at h51
  refine ⟨a5, a7, a9, a10, hd5, hd7, hd9, hd10,
    hb5, hb7, hb9, hb10, ?_⟩
  rcases hsplit with h5zero | h10zero
  · omega
  · omega
