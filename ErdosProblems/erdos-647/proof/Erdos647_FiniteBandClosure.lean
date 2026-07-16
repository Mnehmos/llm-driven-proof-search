import Mathlib

/-!
# Erdős #647 — exact closure of the finite band `25 ≤ n ≤ 84`

The density proof previously absorbed this interval into a constant.  For the
existence question that is insufficient, so this file certifies an explicit
failed shift for every number in the band.

Proof-search record for `finite_band_has_shift_failure`:

* problem version: `2c7952fa-4342-40ed-8a1d-43b093f585aa`
* episode: `88a8417d-715f-4d93-aad6-6317e8f1be80`
* root statement hash:
  `0b8b7fe73cb4aecbdb9e650fe50ee9e982ecab4d23273c92297fa331c6f8724d`
* outcome: `kernel_verified`
-/

namespace Erdos647

/-- Every `n` from `25` through `84` has a concrete failed shift budget. -/
theorem finite_band_has_shift_failure :
    ∀ n ∈ Finset.Icc 25 84,
      ∃ k ∈ Finset.Icc 1 (n - 1),
        k + 2 < ArithmeticFunction.sigma 0 (n - k) := by
  native_decide

/-- Consequently no number in the band satisfies the global maximum bound. -/
theorem no_full_max_in_finite_band :
    ∀ n : ℕ, 24 < n → n ≤ 84 →
      ¬(⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hn24 hn84 H
  obtain ⟨k, hk, hkfail⟩ :=
    finite_band_has_shift_failure n (Finset.mem_Icc.mpr ⟨by omega, hn84⟩)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn1 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
  have hk0 : 0 < k := by omega
  have hkn : k < n := by omega
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

end Erdos647
