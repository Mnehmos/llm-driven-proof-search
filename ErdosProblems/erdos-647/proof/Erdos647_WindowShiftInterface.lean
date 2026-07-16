import Mathlib

/-!
# Erdős #647 — short-window / finite-shift interface

This is the exact adapter for the `variants.infinite` formulation in Formal
Conjectures.  A short-window maximum bound is equivalent to the corresponding
finite family of pointwise divisor-count budgets.

Proof-search record for `window_iff_shift_budgets`:

* problem version: `0c4b9003-af8d-4da4-8fb0-0129d1f85a67`
* episode: `74fbfc4b-da2f-467c-9d44-d02b6eeb28f4`
* root statement hash:
  `bdf2ab2b8d18289e8a6131c18f9fd0da555d7571ecf7f24b8243005adcca5409`
* outcome: `kernel_verified`
-/

namespace Erdos647

/-- The short-window maximum is exactly the associated finite shift budget. -/
theorem window_iff_shift_budgets :
    ∀ n k : ℕ,
      ((⨆ m : Set.Ioo (n - k) n,
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2) ↔
        ∀ j : ℕ, 0 < j → j ≤ k - 1 → j < n →
          ArithmeticFunction.sigma 0 (n - j) ≤ j + 2 := by
  intro n k
  constructor
  · intro H j hj0 hjk hjn
    let g : Set.Ioo (n - k) n → ℕ := fun m =>
      (m : ℕ) + ArithmeticFunction.sigma 0 m
    have hbdd : BddAbove (Set.range g) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [g]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.property.2
      omega
    have hjk' : j < k := by omega
    let m : Set.Ioo (n - k) n :=
      ⟨n - j, by constructor <;> omega⟩
    have hm : g m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [g, m] at hm
    omega
  · intro H
    apply ciSup_le'
    intro m
    have hmlo : n - k < (m : ℕ) := m.property.1
    have hmhi : (m : ℕ) < n := m.property.2
    let j := n - (m : ℕ)
    have hj0 : 0 < j := by dsimp [j]; omega
    have hjk : j ≤ k - 1 := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hs := H j hj0 hjk hjn
    have hsubeq : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    dsimp [j] at hs
    rw [hsubeq] at hs
    omega

/-- Pointwise survival through a fixed shift depth. -/
def WindowSurvivesThrough (n D : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ D → j < n →
    ArithmeticFunction.sigma 0 (n - j) ≤ j + 2

/-- The infinite-window conjecture is exactly fixed-depth survivor infinitude. -/
theorem infinite_windows_iff_shift_survivors :
    (∀ k : ℕ,
      {n | (⨆ m : Set.Ioo (n - k) n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2}.Infinite) ↔
    ∀ k : ℕ, {n | WindowSurvivesThrough n (k - 1)}.Infinite := by
  constructor
  · intro H k
    have hset :
        {n | (⨆ m : Set.Ioo (n - k) n,
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2} =
        {n | WindowSurvivesThrough n (k - 1)} := by
      ext n
      exact window_iff_shift_budgets n k
    rw [← hset]
    exact H k
  · intro H k
    have hset :
        {n | (⨆ m : Set.Ioo (n - k) n,
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2} =
        {n | WindowSurvivesThrough n (k - 1)} := by
      ext n
      exact window_iff_shift_budgets n k
    rw [hset]
    exact H k

end Erdos647
