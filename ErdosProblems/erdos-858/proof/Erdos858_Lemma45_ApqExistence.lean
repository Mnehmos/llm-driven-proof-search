/-
Erdős Problem #858 — Lemma 4.5 connection, `π(a·p·q)=a` existence half (Chojecki 2026).

For primes `p,q` both exceeding `a`: `a ⪯ (a·p·q)`, i.e. `a*p*q = a*t` for
`t:=p*q`, with every prime factor of `t` exceeding `a`. This is the existence
component of the `π(a·p·q)=a` maximality argument (Lemma 4.5), companion to
the uniqueness gap-bounds B1/B2 (`Erdos858_Lemma45_ApqGapBound1/2.lean`) and
`lemma45_pi_apq_subfact` (`Erdos858_Lemma45_PiApqSubfact.lean`).

Proof: witness `t:=p*q` (`a*p*q=a*(p*q)` by `ring`). For any prime `r∣p*q`,
`Nat.Prime.dvd_mul` gives `r∣p ∨ r∣q`; `Nat.prime_dvd_prime_iff_eq` upgrades
either disjunct (both primes) to `r=p` or `r=q`, closing `a<r` via `hap`/`haq`.
Used term-mode `Or.elim` with each branch as a separately-parenthesized
lambda, avoiding the established bullet-flattening pitfall (multiple `·`
bullets on one flat line don't reliably transition between goals — see
`feedback-lean-bullet-flattening`).

Kernel-verified via the proofsearch MCP:
  episode 2d096f3b-86a4-4399-b3f3-07d2e64d89ff,
  problem_version_id e3425d2f-09c3-4715-839b-7491bfb797ea.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c6692b356be6a728cfe2c66557f243370ba51eed1074e34ff1b668fdbcb61023.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 connection, `π(a·p·q)=a` existence half: `a ⪯ (a·p·q)` via
`t:=p*q`, since every prime factor of `p*q` (namely `p` or `q`) exceeds `a`. -/
theorem lemma45_apq_existence :
    ∀ a p q : ℕ, Nat.Prime p → Nat.Prime q → a < p → a < q →
      ∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := by
  intro a p q hp hq hap haq
  refine ⟨p*q, by ring, ?_⟩
  intro r hr hrpq
  exact ((Nat.Prime.dvd_mul hr).mp hrpq).elim (fun hrp => by rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp hrp]; exact hap) (fun hrq => by rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp hrq]; exact haq)

end Erdos858
