import Mathlib

/-!
# Erdős #647 — the gauntlet factor non-reuse theorem (theory run, priority 3)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  e968df98-c597-4e20-92ee-d9ba60484421
  episode_id          a6cb1a59-8e43-40b1-beef-2ca7d6b557a1
  root_statement_hash 4c0890d4f051b88b11ddc379265d940b97ba630e8f4d409ad5a60802395bcb6a
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     728687ed-f881-47df-b273-b2aee2fe13bd (kernel_pass;
                      one prior round 567ada8b: `Nat.dvd_sub'` is not in
                      this pin — the unprimed core `Nat.dvd_sub` is — and
                      the four 2520N−11 blocks had their ℕ-subtractions
                      in the truncating order, caught precisely by omega)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the five empirical gauntlet cofactors — `504N−1` (rung 5),
`360N−1` (rung 7), `280N−1` (rung 9), `252N−1` (rung 10), `2520N−11`
(rung 11), the forms that killed all 719 seven-form survivors in the
450M-parameter audit — are PAIRWISE COPRIME for every `N ≥ 1`: all ten
pairs.

Mechanism (per pair): any common prime divides the pair determinant
(144, 224, 252, 80, 108, 28, 3024, 1440, 560, 252), each determinant's
prime set ({2,3}, {2,7}, {2,3,7}, {2,5}, {2,3}, {2,7}, {2,3,7}, {2,3,5},
{2,5,7}, {2,3,7}) is absorbed by the corresponding coefficient, and a
prime dividing both a coefficient and its form value divides the
constant — impossible (constants are 1 and 11; no determinant is
divisible by 11). The user's coupling identity
`5·(504N−1) − 7·(360N−1) = 2` is the (5,7) instance.

**Consequence for the negative lane**: prime factors used by one rung's
near-prime certificate can NEVER be reused by another rung's — the five
low-divisor demands are arithmetically independent in a strictly
stronger sense than the density heuristic requires. This is the first
concrete `ladder_factor_reuse_bounded`-type fact; the growing-gauntlet
criterion (priority 4) asks which further rungs below `2√n` extend it.
-/

theorem erdos647_gauntlet_pairwise_coprime :
    ∀ N : ℕ, 1 ≤ N →
      Nat.Coprime (504 * N - 1) (360 * N - 1) ∧
      Nat.Coprime (504 * N - 1) (280 * N - 1) ∧
      Nat.Coprime (504 * N - 1) (252 * N - 1) ∧
      Nat.Coprime (360 * N - 1) (280 * N - 1) ∧
      Nat.Coprime (360 * N - 1) (252 * N - 1) ∧
      Nat.Coprime (280 * N - 1) (252 * N - 1) ∧
      Nat.Coprime (504 * N - 1) (2520 * N - 11) ∧
      Nat.Coprime (360 * N - 1) (2520 * N - 11) ∧
      Nat.Coprime (280 * N - 1) (2520 * N - 11) ∧
      Nat.Coprime (252 * N - 1) (2520 * N - 11) := by
  intro N hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 504 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 360 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 144 := by
      have h1 : p ∣ 360 * (504 * N - 1) := Dvd.dvd.mul_left hpA 360
      have h2 : p ∣ 504 * (360 * N - 1) := Dvd.dvd.mul_left hpB 504
      have hE : 360 * (504 * N - 1) - 504 * (360 * N - 1) = 144 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 144 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 144 = {2, 3} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 504 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 280 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 224 := by
      have h1 : p ∣ 280 * (504 * N - 1) := Dvd.dvd.mul_left hpA 280
      have h2 : p ∣ 504 * (280 * N - 1) := Dvd.dvd.mul_left hpB 504
      have hE : 280 * (504 * N - 1) - 504 * (280 * N - 1) = 224 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 224 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 224 = {2, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 504 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 252 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 252 := by
      have h1 : p ∣ 252 * (504 * N - 1) := Dvd.dvd.mul_left hpA 252
      have h2 : p ∣ 504 * (252 * N - 1) := Dvd.dvd.mul_left hpB 504
      have hE : 252 * (504 * N - 1) - 504 * (252 * N - 1) = 252 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 252 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 252 = {2, 3, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 360 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 280 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 80 := by
      have h1 : p ∣ 280 * (360 * N - 1) := Dvd.dvd.mul_left hpA 280
      have h2 : p ∣ 360 * (280 * N - 1) := Dvd.dvd.mul_left hpB 360
      have hE : 280 * (360 * N - 1) - 360 * (280 * N - 1) = 80 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 80 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 80 = {2, 5} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 360 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 252 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 108 := by
      have h1 : p ∣ 252 * (360 * N - 1) := Dvd.dvd.mul_left hpA 252
      have h2 : p ∣ 360 * (252 * N - 1) := Dvd.dvd.mul_left hpB 360
      have hE : 252 * (360 * N - 1) - 360 * (252 * N - 1) = 108 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 108 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 108 = {2, 3} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 280 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 252 * N - 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 28 := by
      have h1 : p ∣ 252 * (280 * N - 1) := Dvd.dvd.mul_left hpA 252
      have h2 : p ∣ 280 * (252 * N - 1) := Dvd.dvd.mul_left hpB 280
      have hE : 252 * (280 * N - 1) - 280 * (252 * N - 1) = 28 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 28 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 28 = {2, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 504 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 2520 * N - 11 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 3024 := by
      have h1 : p ∣ 2520 * (504 * N - 1) := Dvd.dvd.mul_left hpA 2520
      have h2 : p ∣ 504 * (2520 * N - 11) := Dvd.dvd.mul_left hpB 504
      have hE : 2520 * (504 * N - 1) - 504 * (2520 * N - 11) = 3024 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 3024 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 3024 = {2, 3, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 360 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 2520 * N - 11 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 1440 := by
      have h1 : p ∣ 2520 * (360 * N - 1) := Dvd.dvd.mul_left hpA 2520
      have h2 : p ∣ 360 * (2520 * N - 11) := Dvd.dvd.mul_left hpB 360
      have hE : 2520 * (360 * N - 1) - 360 * (2520 * N - 11) = 1440 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 1440 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 1440 = {2, 3, 5} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 280 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 2520 * N - 11 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 560 := by
      have h1 : p ∣ 2520 * (280 * N - 1) := Dvd.dvd.mul_left hpA 2520
      have h2 : p ∣ 280 * (2520 * N - 11) := Dvd.dvd.mul_left hpB 280
      have hE : 2520 * (280 * N - 1) - 280 * (2520 * N - 11) = 560 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 560 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 560 = {2, 5, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
  · by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpA : p ∣ 252 * N - 1 := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpB : p ∣ 2520 * N - 11 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hdet : p ∣ 252 := by
      have h1 : p ∣ 2520 * (252 * N - 1) := Dvd.dvd.mul_left hpA 2520
      have h2 : p ∣ 252 * (2520 * N - 11) := Dvd.dvd.mul_left hpB 252
      have hE : 2520 * (252 * N - 1) - 252 * (2520 * N - 11) = 252 := by omega
      have := Nat.dvd_sub h1 h2
      rwa [hE] at this
    have hmem : p ∈ Nat.primeFactors 252 := Nat.mem_primeFactors.mpr ⟨hp, hdet, by norm_num⟩
    rw [show Nat.primeFactors 252 = {2, 3, 7} from by native_decide] at hmem
    fin_cases hmem <;> · obtain ⟨w, hw⟩ := hpA; omega
