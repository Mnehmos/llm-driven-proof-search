import Mathlib

/-!
# Erdős #647 — compatibility witnesses for both terminated shift-16 leaves

These finite certificates show that neither prime-producing leaf from the
shift-16 residual classification contradicts the four prime forms of the
family-A Hughes chain. They are steering evidence against a purely local
cross-shift contradiction; they do not construct a full Erdős #647 candidate.

The stronger first-leaf cross-shift certificate was preverified in job
`12f26e15-b8d5-41c7-aed8-55d9bbf2a801` and tracked under problem
`3cd08301-bd6a-496d-9d80-2d61fc98e32f`, episode
`46964738-9924-4e44-86b1-039836b286ee`, root hash
`673038a699048e85dc374a1ec5257080cddb73594fb750ef4ae1d29e9a484571`.
The episode ended `kernel_verified` / `root_proved`.
-/

theorem erdos647_shift16_residual_leaves_compatible_with_familyA :
    let Q := 63
    let M₁ := 16 * Q + 11
    let N₁ := 2 * M₁
    let R := 370
    let M₂ := 32 * R + 3
    let N₂ := 2 * M₂
    (M₁ = 1019 ∧ N₁ = 2038 ∧
      Nat.Prime (315 * N₁ - 1) ∧
      Nat.Prime (630 * N₁ - 1) ∧
      Nat.Prime (1260 * N₁ - 1) ∧
      Nat.Prime (2520 * N₁ - 1) ∧
      Nat.Prime (630 * Q + 433)) ∧
    (M₂ = 11843 ∧ N₂ = 23686 ∧
      Nat.Prime (315 * N₂ - 1) ∧
      Nat.Prime (630 * N₂ - 1) ∧
      Nat.Prime (1260 * N₂ - 1) ∧
      Nat.Prime (2520 * N₂ - 1) ∧
      Nat.Prime (630 * R + 59)) := by
  native_decide

/-- The first leaf witness also simultaneously satisfies the actual divisor
budgets at shifts 11, 13, 14, 15, and 16. Thus those five shift constraints,
even together with the family-A prime chain and the terminated residual leaf,
do not give a contradiction. -/
theorem erdos647_shift16_first_residual_leaf_cross_shift_compatible :
    let Q := 63
    let M := 16 * Q + 11
    let N := 2 * M
    let n := 2520 * N
    N = 2038 ∧ M % 8 = 3 ∧
      Nat.Prime (315 * N - 1) ∧
      Nat.Prime (630 * N - 1) ∧
      Nat.Prime (1260 * N - 1) ∧
      Nat.Prime (2520 * N - 1) ∧
      Nat.Prime (630 * Q + 433) ∧
      ArithmeticFunction.sigma 0 (n - 11) = 4 ∧
      ArithmeticFunction.sigma 0 (n - 13) = 2 ∧
      ArithmeticFunction.sigma 0 (n - 14) = 16 ∧
      ArithmeticFunction.sigma 0 (n - 15) = 16 ∧
      ArithmeticFunction.sigma 0 (n - 16) = 16 := by
  native_decide
