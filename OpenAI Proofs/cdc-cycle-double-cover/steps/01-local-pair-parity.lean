/-
CDC step 01 — Local pair parity (paper eqs. (2)–(3); mirrors CDCLean.local_pair_parity)
Problem version : 64ea8680-26c9-4544-acb3-eaf565df0e2e
Episode         : 90be1f6b-3408-4362-9711-17380cd615fb
Outcome         : kernel_verified (2026-07-11)
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

theorem root_theorem : ∀ (x y t s : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  let z := x + y
  let count : ℕ :=
    (if s = t ∨ s = t + x then 1 else 0) +
    (if s = t + x ∨ s = t + z then 1 else 0) +
    (if s = t ∨ s = t + z then 1 else 0)
  count = 0 ∨ count = 2 := by
intro x y t s hx hy hxy
dsimp
have hz : x + y ≠ 0 := by
  intro h
  apply hxy
  funext i
  apply CharTwo.add_eq_zero.mp
  exact congrFun h i
by_cases h0 : s = t <;>
  by_cases h1 : s = t + x <;>
  by_cases h2 : s = t + (x + y) <;>
  simp_all
