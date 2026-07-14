/-
Erdős problem #858 — Chojecki 2026, Proposition 4.1, small instance ν(1) = 4.

Verifier-backed proof via the `proofsearch` MCP (Lean 4, pinned
leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56).

  problem_version_id : 747a0252-bc83-40e2-9ceb-6c995214d8b2
  episode_id         : f5a2bf4c-fe85-479f-bf65-dcd8fff475f4
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  root_statement_hash: 5fb9176d92f5bf8590cbb32f836f1a5bea430ab1907434b527dd6442a058c5e6

Math context. With `a ⪯ b := ∃ t, b = a·t ∧ (∀ prime p ∣ t, a < p)` and
`C_N(a) := Σ_{n≤N : π(n)=a} 1/n`, where `π(n) = a` means `a` is `n`'s maximal
proper `⪯`-ancestor, the paper's threshold `ν(a)` is the smallest `N` with
`C_N(a) > 1/a`. For `a = 1`, `π(n) = 1` on `n ∈ {2,3,4}` is equivalent to "no
`b` with `1 < b < n` is a `⪯`-ancestor of `n`" (`n`'s only proper ancestor is
`1`). This theorem verifies: (i) for every `n ∈ {2,3,4}`, no intermediate
ancestor `b` exists, so each contributes to `C_N(1)`; and (ii) the reciprocal
sum `1/2 + 1/3 + 1/4` exceeds `1` while `1/2 + 1/3` does not — together
establishing `ν(1) = 4` exactly, matching the paper's Proposition 4.1 table.

Proof sketch: `interval_cases n <;> interval_cases b` reduces the first
conjunct to the finitely many `(n, b)` pairs with `2 ≤ n ≤ 4` and
`1 < b < n`. Every pair except `n = 4, b = 2` has no integer solution `t` to
`n = b * t`, so `omega` closes those directly from the hypothesis. For
`n = 4, b = 2`, `omega` derives `t = 2`, then the divisibility hypothesis is
instantiated at the prime `p = 2` (via `Nat.prime_two` and `dvd_refl 2`) to
get `b < p`, i.e. `2 < 2`, a contradiction closed by `omega`. The remaining
two conjuncts are decided by `norm_num` over `ℚ`.
-/
import Mathlib

namespace Erdos858

theorem prop41_nu_one_eq_four :
    (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ¬ ∃ b : ℕ, 1 < b ∧ b < n ∧ ∃ t : ℕ, n = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) ∧
      (1:ℚ)/2 + 1/3 + 1/4 > 1 ∧ (1:ℚ)/2 + 1/3 ≤ 1 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro n hn2 hn4
  rintro ⟨b, hb1, hbn, t, hnbt, hcond⟩
  interval_cases n <;> interval_cases b <;>
    first
      | omega
      | (have ht2 : t = 2 := by omega
         rw [ht2] at hcond
         have := hcond 2 Nat.prime_two (dvd_refl 2)
         omega)

end Erdos858
