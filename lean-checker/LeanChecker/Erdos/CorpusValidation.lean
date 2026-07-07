import Mathlib
import LeanChecker.Kits.ArithmeticKit

/-!
# Erdős corpus validation (solved problems)

Checking the lab against **solved** problems from the Erdős problem corpus
(erdosproblems.com / teorth/erdosproblems, with Lean statements catalogued in
google-deepmind/formal-conjectures). Everything here is **kernel-verified in
the pinned toolchain** (lean4:v4.32.0-rc1 + mathlib@360da6fa), on the same
trust ladder the kit lab uses.

This file is deliberately NOT imported by the `LeanChecker` root — it is an
on-demand validation artifact (the EGZ n=3 `decide` is ~15s). Verify with
`lake env lean LeanChecker/Erdos/CorpusValidation.lean`.

## What this validates

1. Erdős–Ginzburg–Ziv, both as concrete finite instances (rung 1 of the
   certificate ladder — the "EGZ small instances" target the
   ExtremalCombinatoricsKit registry entry claims) and as the general
   theorem (our environment correctly verifies real Mathlib mathematics).
2. Erdős–Ko–Rado (general, via Mathlib).
3. Perfect numbers via the ArithmeticKit σ-bridges — Erdős's long-running
   interest in σ(n)/perfect/abundant numbers.

No proof body of any tracked benchmark is involved; these are open-corpus
named theorems.
-/

namespace LeanChecker.Erdos.CorpusValidation

/-! ## Erdős–Ginzburg–Ziv

The theorem: any `2n − 1` integers contain `n` whose sum is divisible by `n`.
A canonical solved Erdős/additive-combinatorics result, and exactly the
"Erdős–Ginzburg–Ziv small instances" family the ExtremalCombinatoricsKit
lists as a target. -/

/-- **EGZ, n = 2** (rung 1, kernel `decide`): among any 3 elements of `ZMod 2`
two sum to `0`. The finite certificate is the whole `2³` colouring space. -/
theorem egz_two : ∀ a : Fin 3 → ZMod 2, ∃ i j, i ≠ j ∧ a i + a j = 0 := by decide

set_option maxRecDepth 4000 in
/-- **EGZ, n = 3** (rung 1, kernel `decide`): among any 5 elements of `ZMod 3`
three sum to `0` — the `3⁵ = 243`-colouring search, checked in-kernel. -/
theorem egz_three :
    ∀ a : Fin 5 → ZMod 3, ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ a i + a j + a k = 0 := by
  decide

/-- **EGZ, general** (via Mathlib's `Int.erdos_ginzburg_ziv`): any sequence of
`≥ 2n − 1` integers has an `n`-subset whose sum is divisible by `n`. Faithful
statement of the solved problem; our environment verifies the real proof. -/
theorem egz_general {ι : Type*} (n : ℕ) (s : Finset ι) (a : ι → ℤ)
    (hs : 2 * n - 1 ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ (n : ℤ) ∣ ∑ i ∈ t, a i :=
  Int.erdos_ginzburg_ziv a hs

/-! ## Erdős–Ko–Rado

The maximum size of an intersecting family of `r`-sets in an `n`-element
ground set is `C(n−1, r−1)` when `r ≤ n/2`. Solved; stated faithfully and
verified via Mathlib. -/

theorem ekr {n : ℕ} {𝒜 : Finset (Finset (Fin n))} {r : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (h₂ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₃ : r ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (r - 1) :=
  Finset.erdos_ko_rado h𝒜 h₂ h₃

/-! ## Perfect numbers via the ArithmeticKit

Erdős returned repeatedly to `σ(n)`, perfect and abundant numbers. Here the
ArithmeticKit's divisor-sum bridges verify the two smallest perfect numbers
(`σ(n) = 2n`), computed through the coprime factorisation rather than raw
enumeration — the exact use the kit was built for. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `6` is perfect: `σ₁(6) = 12 = 2·6`, via `sigma_mul_of_coprime` over
`2 · 3`. -/
theorem perfect_six : σ 1 6 = 2 * 6 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    LeanChecker.ArithmeticKit.sigma_mul_of_coprime (by decide)]
  decide

/-- `28` is perfect: `σ₁(28) = 56 = 2·28`, via `sigma_mul_of_coprime` over
`4 · 7`. -/
theorem perfect_twenty_eight : σ 1 28 = 2 * 28 := by
  rw [show (28 : ℕ) = 4 * 7 by norm_num,
    LeanChecker.ArithmeticKit.sigma_mul_of_coprime (by decide)]
  decide

end LeanChecker.Erdos.CorpusValidation
