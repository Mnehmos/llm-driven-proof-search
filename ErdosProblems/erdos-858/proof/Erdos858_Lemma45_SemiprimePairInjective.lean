/-
Erdős Problem #858 — Lemma 4.5 connection, semiprime-pair injectivity (Chojecki 2026).

The map `(p,q)↦a·p·q` from ORDERED prime pairs (`p≤q`) is injective. Needed
for the future `C_N(a)=R_N(a)/a` Finset-bijection (Lemma 4.5): reindexes the
semiprime piece of `Σ_{n:π n=a}1/n` as a sum over `Q_N(a)`'s ordered-pair
domain (`Erdos858_Prop46_QNMonotone.lean`'s `(Icc(a+1)N)×ˢ(Icc(a+1)N)`
filtered by `p≤q`).

Proof: cancel `a` (via the `mul_assoc` bridge pattern from
`Erdos858_Lemma45_ApqUniqueness.lean`) to get `p*q=p'*q'`. Since `p` is
prime, `p∣p'*q'` gives `p∣p'` or `p∣q'` (`Nat.Prime.dvd_mul`). If `p∣p'`:
both prime forces `p=p'` (`Nat.prime_dvd_prime_iff_eq`), then cancelling `p`
from `p*q=p'*q'=p*q'` gives `q=q'`. If `p∣q'`: forces `p=q'`, and
substituting+commuting+cancelling gives `q=p'`; the ORDERING constraints
`p≤q` and `p'≤q'` then force `p'=q'` too (pure `omega` from the four
(in)equalities `p=q'`,`q=p'`,`p≤q`,`p'≤q'`), collapsing this branch to the
SAME conclusion (`p=p'∧q=q'`) via the degenerate case where all four
coincide.

Uses `proof_format=raw_lean_block` for the 2-way `rcases...with h|h` bullet
split.

Kernel-verified via the proofsearch MCP:
  episode 212eb5a9-6b30-4be7-b590-4ba262e0d84d,
  problem_version_id d067e372-6223-4eb9-aeb5-ddfa901dc17a.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f1b8e7226d8163c4f0c4085daffe70fd6c1cbf80443b3530cf82ceab339baadb.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 semiprime-pair injectivity: `(p,q)↦a·p·q` is injective on
ordered prime pairs `p≤q`. -/
theorem lemma45_semiprime_pair_injective :
    ∀ a p q p' q' : ℕ, 1 ≤ a → Nat.Prime p → Nat.Prime q → p ≤ q → Nat.Prime p' → Nat.Prime q' → p' ≤ q' →
      a * p * q = a * p' * q' → p = p' ∧ q = q' := by
  intro a p q p' q' ha hp hq hpq hp' hq' hp'q' heq
  have e1 : a*(p*q) = a*p*q := (mul_assoc a p q).symm
  have e2 : a*(p'*q') = a*p'*q' := (mul_assoc a p' q').symm
  have heq2 : p*q = p'*q' := Nat.eq_of_mul_eq_mul_left ha (by rw [e1, e2]; exact heq)
  have hpdvd : p ∣ p'*q' := (by rw [← heq2]; exact ⟨q, rfl⟩)
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h1 | h1
  · have hpp' : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp h1
    have hqq' : q = q' := (by rw [hpp'] at heq2; exact Nat.eq_of_mul_eq_mul_left hp'.pos heq2)
    exact ⟨hpp', hqq'⟩
  · have hpqeqa : p = q' := (Nat.prime_dvd_prime_iff_eq hp hq').mp h1
    have heq2a := heq2
    have heq2b : q'*q = p'*q' := (by rw [hpqeqa] at heq2a; exact heq2a)
    have heq2c : q*q' = p'*q' := (by rw [mul_comm q' q] at heq2b; exact heq2b)
    have hqpa : q = p' := Nat.eq_of_mul_eq_mul_right hq'.pos heq2c
    have hpqeq2 : p' = q' := (by omega)
    exact ⟨(by omega), (by omega)⟩

end Erdos858
