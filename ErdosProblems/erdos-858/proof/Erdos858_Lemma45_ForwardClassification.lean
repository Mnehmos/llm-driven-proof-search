/-
Erdős Problem #858 — Lemma 4.5 connection, forward classification (Chojecki 2026).

For `a>N^{1/4}` (via the nat surrogate `N<a^4`) and any `n∈[1,N]` with
`π(n)=a`: `n` is EITHER `a·p` for a single prime `p`, OR `a·p·q` for two
primes `p,q`. This is the FORWARD direction needed for the `C_N(a)=R_N(a)/a`
bijection (Lemma 4.5) — the previously-verified `lemma45_pi_apq_full`/
`lemma27_pi_ap_full` are the REVERSE direction (showing `a·p`/`a·p·q` DO have
`π=a`); this atom shows there is NOTHING ELSE.

Combines π-soundness (`n=π(n)·t` with the cofactor `t`'s prime factors all
exceeding `π(n)`) with the pre-verified `Ω≤2` dichotomy
(`lemma45_prime_semiprime_full`, `Erdos858_Lemma45_FullDichotomy.lean`,
taken as a hypothesis: `t` is `1`, prime, or a product of two primes) to
classify every child of `a`. The `t=1` case is refuted via the standard
π-axiom `π(n)<n` for `n≥2` (since `t=1` would force `n=a`, giving `a<a`).

Proof: `n≠1` (else `π(1)=0` contradicts `π(n)=a≥1`), so `n≥2`; the
soundness witness `t` satisfies `n=a·t` (after substituting `π(n)=a`) with
`t<a³` (from `a·t=n≤N<a^4=a·a³`, cancelled via `lt_of_mul_lt_mul_left`) and
`t>0` (else `n=0`). Apply the dichotomy hypothesis to `t`; the three
resulting cases give: `t=1` refuted, `t` prime gives the first disjunct
(`p:=t`), `t=p·q` gives the second (`n=a·(p·q)=a·p·q` by `ring`).

Uses `proof_format=raw_lean_block` for the 3-way `rcases...with h|h|h`
bullet split (mirrors the discipline established in
`Erdos858_Lemma45_ApqUniqueness.lean`).

Kernel-verified via the proofsearch MCP:
  episode 778710f6-19bd-451c-80e8-032cd42adc56,
  problem_version_id 3ee9aea8-bc8b-434b-a077-e1f7bdb2abc4.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0e2b84fa79826a8284f55d8e19c4a139952cd69afa2faabe4b07d42265b4585a.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 forward classification: for `a>N^{1/4}` and `n∈[1,N]` with
`π(n)=a`, `n=a·p` (single prime) or `n=a·p·q` (two primes) — no other
possibility, via π-soundness + the `Ω≤2` dichotomy. -/
theorem lemma45_forward_classification :
    ∀ (π : ℕ → ℕ) (N a n : ℕ), N < a^4 → 1 ≤ a →
      π 1 = 0 → (∀ m : ℕ, 2 ≤ m → m ≤ N → 1 ≤ π m ∧ π m < m) →
      (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π w < p) →
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      n ∈ Finset.Icc 1 N → π n = a →
      (∃ p : ℕ, Nat.Prime p ∧ n = a * p) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = a * p * q) := by
  intro π N a n hN4 ha hπ1 hax hsound hdichotomy hnrange hpna
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
  have hn2 : 2 ≤ n := (by by_contra hlt; push_neg at hlt; have heq1 : n = 1 := (by omega); rw [heq1, hπ1] at hpna; omega)
  obtain ⟨t, hnt, htp⟩ := hsound n hn2
  rw [hpna] at hnt htp
  have ht0 : 0 < t := (by by_contra hlt; push_neg at hlt; have ht0' : t = 0 := (by omega); rw [ht0', mul_zero] at hnt; omega)
  have htcube : t < a^3 := (by
    have h1 : a*t ≤ N := (by rw [← hnt]; exact hnN)
    have h2 : a*t < a^4 := (by omega)
    have h3 : a^4 = a*a^3 := (by ring)
    rw [h3] at h2
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le a))
  rcases hdichotomy a t ha ht0 htcube htp with ht1 | ht1 | ⟨p,q,hp,hq,htpq⟩
  · exfalso
    have hna : n = a := (by rw [hnt, ht1, mul_one])
    have hlt := (hax n hn2 hnN).2
    rw [hpna, hna] at hlt
    omega
  · left
    exact ⟨t, ht1, hnt⟩
  · right
    exact ⟨p, q, hp, hq, (by rw [hnt, htpq]; ring)⟩

end Erdos858
