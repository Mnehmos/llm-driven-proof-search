import Mathlib

/-!
# Erdős #647 — shift-depth interface for the existence campaign

The completed density theorem controls how many candidates can occur, but does
not exclude an individual candidate.  This file exposes the original maximum
condition as the family of pointwise divisor-count budgets

`σ₀ (n - k) ≤ k + 2`.

That is the common interface for the next two possible closing arguments:

* a growing-depth obstruction, which finds a failing shift `k ≤ D(n)`; or
* a direct prime-chain contradiction, which derives such a failing shift from
  the classified shapes of the preceding shifts.

The main bridge was kernel-verified through the tracked proof-search pipeline:

* problem version: `11379956-bdc3-4ed9-bef3-3e373c8e85c2`
* episode: `3061458d-df2c-4e48-b05d-76b48209a2f6`
* root statement hash:
  `df1b2ec8493146e374e83d3c293fd3a25f7c6d4f4c4d48f1049a9050c3a6faa9`
* outcome: `kernel_verified`

The exact converse `full_max_iff_shift_budgets` was independently tracked:

* problem version: `e997a6ae-30ba-4af3-b49a-39a4c405b2d4`
* episode: `8bc57f29-adcc-467d-b986-3e060b2d2e3c`
* root statement hash:
  `7e1e0ea545ac3f75298bbece75068750bc4036dd40ed53d16886103725cb4556`
* outcome: `kernel_verified`
-/

namespace Erdos647

/-- `n` satisfies every Erdős #647 shift budget through depth `D`. -/
def SurvivesThrough (n D : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ D → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ k + 2

/-- The global maximum condition implies every positive shift budget. -/
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
theorem full_max_iff_shift_budgets (n : ℕ) :
    ((⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 ↔
      ∀ k : ℕ, 0 < k → k < n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) := by
  constructor
  · exact full_max_implies_shift_budgets n
  · intro H
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
      apply ciSup_le
      intro m
      by_cases hm0 : (m : ℕ) = 0
      · have hs0 : ArithmeticFunction.sigma 0 (m : ℕ) = 0 := by
          rw [hm0]
          native_decide
        omega
      · let k := n - (m : ℕ)
        have hk0 : 0 < k := by
          dsimp [k]
          omega
        have hkn : k < n := by
          dsimp [k]
          omega
        have hk := H k hk0 hkn
        have hnkm : n - k = (m : ℕ) := by
          dsimp [k]
          omega
        rw [hnkm] at hk
        omega

/-- A number satisfying the global maximum condition survives every depth. -/
theorem full_max_implies_survivesThrough {n : ℕ}
    (H : (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2)
    (D : ℕ) : SurvivesThrough n D := by
  intro k hk0 _ hkn
  exact full_max_implies_shift_budgets n H k hk0 hkn

/-- Surviving through the full available depth is exactly the maximum condition. -/
theorem full_max_iff_survivesThrough_full (n : ℕ) :
    ((⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 ↔
      SurvivesThrough n (n - 1)) := by
  rw [full_max_iff_shift_budgets]
  constructor
  · intro H k hk0 _ hkn
    exact H k hk0 hkn
  · intro H k hk0 hkn
    exact H k hk0 (by omega) hkn

/-- The original existential asks exactly for a full-depth survivor above `24`. -/
theorem exists_full_max_iff_exists_full_depth_survivor :
    (∃ n > 24,
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2) ↔
      ∃ n, 24 < n ∧ SurvivesThrough n (n - 1) := by
  constructor
  · rintro ⟨n, hn24, hn⟩
    exact ⟨n, hn24, (full_max_iff_survivesThrough_full n).mp hn⟩
  · rintro ⟨n, hn24, hn⟩
    exact ⟨n, hn24, (full_max_iff_survivesThrough_full n).mpr hn⟩

/-- Failure of the maximum condition is exactly witnessed by one bad shift. -/
theorem not_full_max_iff_exists_shift_failure (n : ℕ) :
    (¬(⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2) ↔
      ∃ k : ℕ, 0 < k ∧ k < n ∧
        k + 2 < ArithmeticFunction.sigma 0 (n - k) := by
  rw [full_max_iff_shift_budgets]
  push Not
  rfl

/-- Any failed budget, at any finite depth, excludes the global condition. -/
theorem not_full_max_of_depth_failure {n D : ℕ}
    (hfail : ∃ k : ℕ, 0 < k ∧ k ≤ D ∧ k < n ∧
      k + 2 < ArithmeticFunction.sigma 0 (n - k)) :
    ¬(⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro H
  obtain ⟨k, hk0, hkD, hkn, hkfail⟩ := hfail
  have hk := full_max_implies_survivesThrough H D k hk0 hkD hkn
  omega

end Erdos647
