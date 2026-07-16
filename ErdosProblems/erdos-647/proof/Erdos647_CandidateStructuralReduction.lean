import Erdos647_FiniteBandClosure
import Erdos647_CandidateDivisible2520
import Erdos647_ShiftDepthInterface
import Erdos647_Thm2_Stage12
import Erdos647_Thm2_Stage4
import Erdos647_Thm2_Stage8

/-!
# Erdős #647 — exact structural reduction for every hypothetical candidate

This assembly joins the certified finite-band closure to the recovered
divisibility and prime-chain reductions.  It does not settle existence: it
places every remaining hypothetical candidate beyond `84`, makes it a
multiple of `2520`, and puts it in one of the two prime-chain families.
-/

namespace Erdos647

/-- Every hypothetical candidate is larger than `84` and divisible by `2520`. -/
theorem candidate_gt84_and_dvd2520 :
    ∀ n : ℕ, 24 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      84 < n ∧ 2520 ∣ n := by
  intro n hn24 H
  have hn84 : 84 < n := by
    by_contra h
    exact no_full_max_in_finite_band n hn24 (by omega) H
  exact ⟨hn84, candidate_dvd_2520 n hn84 H⟩

/-- Nonexistence is now exactly the large-range failed-shift obligation. -/
theorem no_candidates_iff_all_large_have_shift_failure :
    (∀ n : ℕ, 24 < n →
      ¬(⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2) ↔
    ∀ n : ℕ, 84 < n →
      ∃ k : ℕ, 0 < k ∧ k < n ∧
        k + 2 < ArithmeticFunction.sigma 0 (n - k) := by
  constructor
  · intro H n hn84
    exact (not_full_max_iff_exists_shift_failure n).mp
      (H n (by omega))
  · intro H n hn24
    by_cases hn84 : 84 < n
    · exact (not_full_max_iff_exists_shift_failure n).mpr (H n hn84)
    · exact no_full_max_in_finite_band n hn24 (by omega)

/--
Every hypothetical large candidate lies in one of the two prime-chain
families from the verified `k = 1,2,4,8` reduction.
-/
theorem candidate_primechain_families :
    ∀ n : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∃ s : ℕ, s.Prime ∧
        ((n = 8 * s + 8 ∧
            (2 * s + 1).Prime ∧
            (4 * s + 3).Prime ∧
            (8 * s + 7).Prime) ∨
          (n = 16 * s + 8 ∧
            (4 * s + 1).Prime ∧
            (8 * s + 3).Prime ∧
            (16 * s + 7).Prime)) := by
  intro n hn84 H
  have shift : ∀ k : ℕ, 0 < k → k < n →
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
  have h1 := shift 1 (by omega) (by omega)
  have h2 := shift 2 (by omega) (by omega)
  obtain ⟨q, hqprime, hnq, hn1prime⟩ :=
    erdos647_primechain_stage12 n (by omega) h1 h2
  have h2q1prime : (2 * q + 1).Prime := by
    convert hn1prime using 1 <;> omega
  have h4 := shift 4 (by omega) (by omega)
  have hn4 : n - 4 = 2 * q - 2 := by omega
  rw [hn4] at h4
  obtain ⟨p, hpprime, hqp⟩ :=
    erdos647_primechain_stage4 q (by omega) hqprime h2q1prime h4
  have h2p1prime : (2 * p + 1).Prime := by
    rw [← hqp]
    exact hqprime
  have h8 := shift 8 (by omega) (by omega)
  have hn8 : n - 8 = 4 * p - 4 := by omega
  rw [hn8] at h8
  obtain ⟨s, hsprime, hps | hps⟩ :=
    erdos647_primechain_stage8 p (by omega) hpprime h2p1prime h8
  · refine ⟨s, hsprime, Or.inl ⟨by omega, ?_, ?_, ?_⟩⟩
    · rw [← hps]
      exact hpprime
    · convert hqprime using 1 <;> omega
    · convert hn1prime using 1 <;> omega
  · refine ⟨s, hsprime, Or.inr ⟨by omega, ?_, ?_, ?_⟩⟩
    · rw [← hps]
      exact hpprime
    · convert hqprime using 1 <;> omega
    · convert hn1prime using 1 <;> omega

end Erdos647
