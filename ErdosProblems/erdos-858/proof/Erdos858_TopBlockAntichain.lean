/-
Erdős Problem #858 — the trivial lower bound: (√N, N] is an antichain.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 29440e6b-6595-46ba-982b-15a6004ab282,
problem_version_id ff11730f-bb32-4880-b967-38ad719165df.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a504844e…

The paper's immediate lower bound is
    M(N) ≥ Σ_{√N < n ≤ N} 1/n = ½ log N + O(1),
"because every subset of (√N, N] is admissible" — i.e. (√N, N] is a ⪯-antichain.

Here that admissibility is formalized: if `N < a²` (so `a > √N`) and
`a < b ≤ N`, then `a ⋠ b`. Proof: `b = a·t` with `a < b` forces `t ≥ 2`, so `t`
has a prime factor `p`; since every prime factor of `t` exceeds `a`, `t ≥ p > a`,
hence `b = a·t > a·a = a² > N ≥ b`, a contradiction. Thus no two distinct
elements of `(√N, N]` are `⪯`-comparable, and the whole block is admissible.
-/
import Mathlib

namespace Erdos858

/-- Admissibility of the top block: for `N < a*a` and `a < b ≤ N`, `a ⋠ b`. So
every subset of `(√N, N]` is a `⪯`-antichain (the paper's `M(N) ≥ ½ log N + O(1)`
lower bound). -/
theorem top_block_antichain :
    ∀ N a b : ℕ, N < a * a → a < b → b ≤ N →
      ¬ (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) := by
  intro N a b hNa hab hbN
  rintro ⟨t, hbt, ht⟩
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at hNa; omega
    · exact h
  have ht_ne1 : t ≠ 1 := by rintro rfl; rw [mul_one] at hbt; omega
  have ht_pos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero] at hbt; omega
    · exact h
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht_ne1
  have hap : a < p := ht p hp hpt
  have hpt_le : p ≤ t := Nat.le_of_dvd ht_pos hpt
  have hat : a < t := lt_of_lt_of_le hap hpt_le
  have hlt : a * a < a * t := mul_lt_mul_of_pos_left hat ha_pos
  rw [← hbt] at hlt
  omega

end Erdos858
