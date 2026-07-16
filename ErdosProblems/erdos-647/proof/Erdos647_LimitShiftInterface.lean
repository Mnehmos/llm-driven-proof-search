import Mathlib

/-!
# Erdős #647 — exact interface for the limit variant

The conjectured convergence of the translated maximum to `atTop` is exactly
equivalent to an eventual failed-shift statement with arbitrarily large
excess.  Prime powers prove only that the sequence is unbounded along an
explicit subsequence; they do not provide the uniform-in-`n` conclusion.

Proof-search provenance for `lim_iff_eventual_shift_excess`:

* verification `d9d87fbd-54b8-4e0e-9d83-f99d23d871b5`: `kernel_pass`;
* problem version `7f51a2e4-b598-4a05-88ff-a0068f7e8a30`;
* episode `3baedfa9-85ed-48b0-b477-18faa0d9e47f`:
  `kernel_verified` (`root_proved`).

The prime-power lower bound was separately checked under verification job
`23015b9f-023c-44e7-a025-a6fdd9e1b417` (`kernel_pass`).
-/

namespace Erdos647

open Filter ArithmeticFunction.sigma

theorem lim_iff_eventual_shift_excess :
    atTop.Tendsto (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) atTop ↔
      ∀ B : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ k : ℕ, 0 < k ∧ k < n ∧ B + k < σ 0 (n - k) := by
  constructor
  · intro hlim B
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hlim (B + 1)
    refine ⟨max N 2, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hB : B + 1 ≤ ⨆ m : Fin n, σ 0 m + m - n := hN n hnN
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    obtain ⟨m, hm⟩ :
        ∃ m : Fin n, σ 0 m + m - n = ⨆ i : Fin n, σ 0 i + i - n :=
      exists_eq_ciSup_of_finite
    have hBm : B + 1 ≤ σ 0 m + (m : ℕ) - n := by
      rw [hm]
      exact hB
    have hm0 : (m : ℕ) ≠ 0 := by
      intro hmzero
      have hs0 : σ 0 (0 : ℕ) = 0 := by native_decide
      rw [hmzero, hs0] at hBm
      omega
    let k := n - (m : ℕ)
    refine ⟨k, ?_, ?_, ?_⟩
    · dsimp [k]
      omega
    · dsimp [k]
      omega
    · dsimp [k]
      have hm_lt : (m : ℕ) < n := m.isLt
      have hnkm : n - (n - (m : ℕ)) = (m : ℕ) := by omega
      rw [hnkm]
      omega
  · intro hshift
    rw [tendsto_atTop_atTop]
    intro B
    obtain ⟨N, hN⟩ := hshift B
    refine ⟨max N 1, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    obtain ⟨k, hk0, hkn, hkfail⟩ := hN n hnN
    let m : Fin n := ⟨n - k, by omega⟩
    have hterm : B ≤ σ 0 m + (m : ℕ) - n := by
      dsimp [m]
      omega
    have hbdd : BddAbove (Set.range fun i : Fin n ↦ σ 0 i + (i : ℕ) - n) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨i, rfl⟩
      dsimp
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (i : ℕ)
      have hi : (i : ℕ) < n := i.isLt
      omega
    exact hterm.trans (le_ciSup hbdd m)

/-- The elementary prime-power witness makes the sequence unbounded along a
subsequence, but does not prove convergence to `atTop`. -/
theorem prime_power_subsequence_lower_bound (B : ℕ) :
    B ≤ ⨆ m : Fin (2 ^ B + 1), σ 0 m + m - (2 ^ B + 1) := by
  let m : Fin (2 ^ B + 1) := ⟨2 ^ B, by omega⟩
  have hterm : B ≤ σ 0 m + (m : ℕ) - (2 ^ B + 1) := by
    dsimp [m]
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]
    omega
  have hbdd :
      BddAbove
        (Set.range fun i : Fin (2 ^ B + 1) ↦
          σ 0 i + (i : ℕ) - (2 ^ B + 1)) := by
    refine ⟨2 * (2 ^ B + 1), ?_⟩
    rintro y ⟨i, rfl⟩
    dsimp
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (i : ℕ)
    have hi : (i : ℕ) < 2 ^ B + 1 := i.isLt
    omega
  exact hterm.trans (le_ciSup hbdd m)

theorem lim_sequence_unbounded :
    ∀ B : ℕ, ∃ n : ℕ,
      B ≤ ⨆ m : Fin n, σ 0 m + m - n := by
  intro B
  exact ⟨2 ^ B + 1, prime_power_subsequence_lower_bound B⟩

theorem lim_sequence_not_bddAbove :
    ¬BddAbove
      (Set.range fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) := by
  rintro ⟨M, hM⟩
  have hlo := prime_power_subsequence_lower_bound (M + 1)
  have hhi := hM
    (show (⨆ m : Fin (2 ^ (M + 1) + 1),
        σ 0 m + m - (2 ^ (M + 1) + 1)) ∈
      Set.range (fun n ↦ ⨆ m : Fin n, σ 0 m + m - n) from
      ⟨2 ^ (M + 1) + 1, rfl⟩)
  omega

end Erdos647
