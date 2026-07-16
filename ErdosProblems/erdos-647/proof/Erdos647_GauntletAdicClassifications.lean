import Mathlib

/-!
# Erdős #647 — B-parametric adic classifications for gauntlet rungs 5, 9, 10

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  eca7eff8-01d1-44d8-a18b-8b640b093c42
  episode_id          0f5d4132-218b-4aec-94b7-a29ef80b82ee
  root_statement_hash 5ae64e2a22b2214f740251eec9d5e4696880936ad14bacf7fbfc11a5304011d4
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     cf295bf4-1e73-449d-a79f-5f097d008dd9 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the remaining peel-rungs of the empirical gauntlet, B-parametric:

- rung 5:  `504N−1 = 5^a·q`, `5∤q`, `(a+2)·τ(q) ≤ B+5`;
- rung 9:  `280N−1 = 3^a·q`, `3∤q`, `(a+3)·τ(q) ≤ B+9`
  (fixed factor `9 = 3²` contributes two 3-adic layers up front);
- rung 10: `252N−1 = 5^a·q`, `5∤q`, `2·(a+2)·τ(q) ≤ B+10`
  (fixed factor `10 = 2·5`; the cofactor is automatically odd, so the
  2-part is exactly one layer).

Together with `erdos647_shift7_adic_classification` (rung 7) and the
trivial direct budget at rung 11, this COMPLETES the B-parametric formal
base block of the five-rung gauntlet that killed all 719 seven-form
survivors in the 450M-parameter audit
(`dossiers/sqrt-prefix-failure-audit.md`). Main declaration is `B = 2`;
uniformity in `B` serves the limit declaration.

The frontier run's depth-13 record survivor
(`N = 245,678,060,791,306`, `n ≈ 6.19×10¹⁷`, first failure at rung 13
with `n−13 = 13·97·439·p`, τ = 16 > 15) confirms the gauntlet grows past
the base block — exactly the behavior the growing-gauntlet criterion
(`dossiers/growing-gauntlet-criterion.md`) is built around, and exactly
why the strategic guardrail forbids targeting the fixed five rungs.
-/

theorem erdos647_gauntlet_adic_classifications :
    ∀ (N B : ℕ), 1 ≤ N →
      (ArithmeticFunction.sigma 0 (2520 * N - 5) ≤ B + 5 →
        ∃ a q : ℕ, 504 * N - 1 = 5 ^ a * q ∧ ¬ 5 ∣ q ∧
          (a + 2) * ArithmeticFunction.sigma 0 q ≤ B + 5) ∧
      (ArithmeticFunction.sigma 0 (2520 * N - 9) ≤ B + 9 →
        ∃ a q : ℕ, 280 * N - 1 = 3 ^ a * q ∧ ¬ 3 ∣ q ∧
          (a + 3) * ArithmeticFunction.sigma 0 q ≤ B + 9) ∧
      (ArithmeticFunction.sigma 0 (2520 * N - 10) ≤ B + 10 →
        ∃ a q : ℕ, 252 * N - 1 = 5 ^ a * q ∧ ¬ 5 ∣ q ∧
          2 * ((a + 2) * ArithmeticFunction.sigma 0 q) ≤ B + 10) := by
  intro N B hN
  refine ⟨?_, ?_, ?_⟩
  · intro hbud
    have hne : 504 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq5, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 5 (by norm_num)
    refine ⟨a, q, heq, hq5, ?_⟩
    have hval : 2520 * N - 5 = 5 ^ (a + 1) * q := by
      have h5 : 2520 * N - 5 = 5 * (504 * N - 1) := by omega
      rw [h5, heq, pow_succ]
      ring
    have hcop : Nat.Coprime (5 ^ (a + 1)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq5)
    have hs5 : ArithmeticFunction.sigma 0 (5 ^ (a + 1)) = a + 2 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
        Finset.card_range]
    have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 5) =
        (a + 2) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs5]
    rw [hsigma] at hbud
    exact hbud
  · intro hbud
    have hne : 280 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq3, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 3 (by norm_num)
    refine ⟨a, q, heq, hq3, ?_⟩
    have hval : 2520 * N - 9 = 3 ^ (a + 2) * q := by
      have h9 : 2520 * N - 9 = 9 * (280 * N - 1) := by omega
      rw [h9, heq]
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this, ← mul_assoc, ← pow_add]
      ring_nf
    have hcop : Nat.Coprime (3 ^ (a + 2)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr hq3)
    have hs3 : ArithmeticFunction.sigma 0 (3 ^ (a + 2)) = a + 3 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 3), Finset.card_map,
        Finset.card_range]
    have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 9) =
        (a + 3) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs3]
    rw [hsigma] at hbud
    exact hbud
  · intro hbud
    have hne : 252 * N - 1 ≠ 0 := by omega
    obtain ⟨a, q, hq5, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 5 (by norm_num)
    refine ⟨a, q, heq, hq5, ?_⟩
    have hqodd : ¬ 2 ∣ q := by
      intro h2q
      have h2 : (2 : ℕ) ∣ 252 * N - 1 := by
        rw [heq]
        exact Dvd.dvd.mul_left h2q (5 ^ a)
      obtain ⟨w, hw⟩ := h2
      omega
    have hval : 2520 * N - 10 = 2 * 5 ^ (a + 1) * q := by
      have h10 : 2520 * N - 10 = 10 * (252 * N - 1) := by omega
      rw [h10, heq, pow_succ]
      ring
    have hcop5 : Nat.Coprime (5 ^ (a + 1)) q :=
      Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hq5)
    have hcop2 : Nat.Coprime 2 q := ((by norm_num : Nat.Prime 2).coprime_iff_not_dvd).mpr hqodd
    have hcop : Nat.Coprime (2 * 5 ^ (a + 1)) q := Nat.Coprime.mul hcop2 hcop5
    have hcop25 : Nat.Coprime 2 (5 ^ (a + 1)) :=
      Nat.Coprime.pow_right _ (by norm_num)
    have hs5 : ArithmeticFunction.sigma 0 (5 ^ (a + 1)) = a + 2 := by
      rw [ArithmeticFunction.sigma_zero_apply,
        Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map,
        Finset.card_range]
    have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
    have hs25 : ArithmeticFunction.sigma 0 (2 * 5 ^ (a + 1)) = 2 * (a + 2) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25, hs2, hs5]
    have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 10) =
        2 * (a + 2) * ArithmeticFunction.sigma 0 q := by
      rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs25]
    rw [hsigma] at hbud
    calc 2 * ((a + 2) * ArithmeticFunction.sigma 0 q)
        = 2 * (a + 2) * ArithmeticFunction.sigma 0 q := by ring
      _ ≤ B + 10 := hbud
