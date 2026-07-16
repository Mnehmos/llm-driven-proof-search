import Mathlib

/-!
# Erdős #647 — finite height of every fixed exceptional p-adic spine

Snapshot of the exact statement and proof kernel-verified through the tracked
proof-search pipeline on 2026-07-15.

* preverification job: `f4a2d5e7-f8bd-4ef9-a015-92c3e5c547e0`
  (`kernel_pass`);
* problem version: `4f75b91a-8e28-48a4-a315-24202a76e298`;
* episode: `4d4a6605-0d92-4f12-a0f0-448e5ab502ec`;
* root statement hash:
  `b12a35215e6bae5f6d8f236f2856df34dd9a29cb6fc53563299adb01b39b19c3`;
* tracked outcome: `kernel_verified` (`root_proved`).

The companion forced-transition-or-exit dichotomy was independently checked
and tracked as well:

* preverification job: `d13eaf30-7a27-4218-8b78-6222bd5f5f34`
  (`kernel_pass`);
* problem version: `64fe14f7-ff25-42a4-afda-17ee1322a59b`;
* episode: `23739805-fc84-4467-aa89-0c7534884f7f`;
* root statement hash:
  `1eac92d7176619915a6f06df000d3b364a9705e6e24d23f178fbe5df9a5e937b`;
* tracked outcome: `kernel_verified` (`root_proved`).

If a nonzero integer `x` has divisor budget `sigma₀(x) ≤ B` and contains
`p^e`, then `e < B`.  Thus the honest rank

`B - (e + 1)`

strictly decreases whenever an exceptional branch exposes one additional
copy of the same prime, and no fixed `p`-adic branch can continue through
`p^B`.

Scope warning: this proves termination of a **fixed** `p`-adic refinement
spine.  It does not prove that a hypothetical Erdős #647 candidate must keep
taking that spine rather than leave it at a terminal prime or almost-prime
cofactor.  A global contradiction still needs a theorem linking those
terminal leaves across shifts.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Divisibility by `p^e` contributes at least `e+1` divisors, so a divisor
budget `B` forces the strict exponent bound `e < B`. -/
theorem prime_power_exponent_lt_of_sigma_zero_le :
    ∀ x p e B : ℕ, x ≠ 0 → Nat.Prime p → p ^ e ∣ x →
      ArithmeticFunction.sigma 0 x ≤ B → e < B := by
  intro x p e B hx hp hpow hbudget
  have hsub : (p ^ e).divisors ⊆ x.divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.trans hpow, hx⟩
  have hcard : (p ^ e).divisors.card ≤ x.divisors.card :=
    Finset.card_le_card hsub
  have hsigma : ArithmeticFunction.sigma 0 (p ^ e) ≤
      ArithmeticFunction.sigma 0 x := by
    simpa [ArithmeticFunction.sigma_zero_apply] using hcard
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp] at hsigma
  omega

/-- Every fixed `p`-adic node has the exact local dichotomy needed by the
refinement framework: either another copy of `p` occurs, or the spine exits
with a cofactor whose divisor budget has been divided by `e+1`. -/
theorem next_adic_lift_or_terminal_budget :
    ∀ p e q B : ℕ, Nat.Prime p →
      ArithmeticFunction.sigma 0 (p ^ e * q) ≤ B →
      (p ∣ q) ∨
        (Nat.Coprime p q ∧
          ArithmeticFunction.sigma 0 q ≤ B / (e + 1)) := by
  intro p e q B hp hbound
  by_cases hpq : p ∣ q
  · exact Or.inl hpq
  · right
    have hcop : Nat.Coprime p q :=
      (hp.coprime_iff_not_dvd).mpr hpq
    refine ⟨hcop, ?_⟩
    have hcopPow : Nat.Coprime (p ^ e) q := hcop.pow_left e
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopPow,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp] at hbound
    apply (Nat.le_div_iff_mul_le (by omega : 0 < e + 1)).2
    simpa [Nat.mul_comm] using hbound

end Erdos647
