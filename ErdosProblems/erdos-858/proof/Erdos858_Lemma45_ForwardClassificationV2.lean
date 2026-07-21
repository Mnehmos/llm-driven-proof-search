/-
Erdős Problem #858 — Lemma 4.5 connection, forward classification v2 (Chojecki 2026).

Upgrades `lemma45_forward_classification` (`Erdos858_Lemma45_ForwardClassification.lean`)
to include the `a<p` (resp. `a<p∧a<q`) bounds in its conclusion — discovered
missing while scoping Stage A of the `C_N(a)=R_N(a)/a` Finset-bijection
(image-membership `p∈Icc(a+1)N` needs `a<p` explicitly; the original atom's
conclusion only gave `n=a·p`/`n=a·p·q` without the bound, which does NOT
follow from those equations alone).

For `a>N^{1/4}` (via `N<a^4`) and `n∈[1,N]` with `π(n)=a`: `n=a·p` for a
prime `p>a`, OR `n=a·p·q` for primes `p,q` both `>a`.

Proof: identical to the original, additionally extracting the bounds from
the soundness witness's "cofactor's prime factors exceed `a`" property
(`htp`) — applied at `r:=t` itself (via `dvd_refl`) in the single-prime
case, and at `r:=p`/`r:=q` (via `p∣t`/`q∣t` from `t=p·q`, `dvd_mul_right`/
`dvd_mul_left`) in the semiprime case.

Kernel-verified via the proofsearch MCP:
  episode 4ae619d1-3d6b-41b7-8916-55abae4026e0,
  problem_version_id 0d973381-8706-4126-8242-757e06489740.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 242846f89bb190954c87d0a89821062b81e134807c5138747c369002dd8030cc.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 forward classification (v2, with bounds): for `a>N^{1/4}` and
`n∈[1,N]` with `π(n)=a`, `n=a·p` (prime `p>a`) or `n=a·p·q` (primes
`p,q>a`). Upgrades `lemma45_forward_classification` with the `a<p`/`a<q`
bounds needed for the future `C_N=R_N/a` bijection's Stage A. -/
theorem lemma45_forward_classification_v2 :
    ∀ (π : ℕ → ℕ) (N a n : ℕ), N < a^4 → 1 ≤ a →
      π 1 = 0 → (∀ m : ℕ, 2 ≤ m → m ≤ N → 1 ≤ π m ∧ π m < m) →
      (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π w < p) →
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      n ∈ Finset.Icc 1 N → π n = a →
      (∃ p : ℕ, Nat.Prime p ∧ a < p ∧ n = a * p) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ a < p ∧ a < q ∧ n = a * p * q) := by
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
    have hap : a < t := htp t ht1 (dvd_refl t)
    exact ⟨t, ht1, hap, hnt⟩
  · right
    have hapd : p ∣ t := (by rw [htpq]; exact dvd_mul_right p q)
    have haqd : q ∣ t := (by rw [htpq]; exact dvd_mul_left q p)
    have hap : a < p := htp p hp hapd
    have haq : a < q := htp q hq haqd
    exact ⟨p, q, hp, hq, hap, haq, (by rw [hnt, htpq]; ring)⟩

end Erdos858
