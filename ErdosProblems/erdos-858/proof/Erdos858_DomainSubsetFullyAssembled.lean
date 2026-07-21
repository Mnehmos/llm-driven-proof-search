/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED domain subset (Chojecki 2026).

Reduces `lemma45_CN_domain_subset`'s (`Erdos858_Lemma45_DomainSubset.lean`)
`hfwd` hypothesis to genuinely primitive π-structure axioms (`π 1=0`,
range, soundness) plus the standalone `lemma45_prime_semiprime_full`
dichotomy theorem — inlining `lemma45_forward_classification_v2`'s
(`Erdos858_Lemma45_ForwardClassificationV2.lean`) derivation of `hfwd`
directly. Needs only 6 leaf hypotheses (much smaller than the supset
direction's 11, since the forward direction doesn't need maximality,
sandwich, `lemma27`, the gap-bounds, or `apq`-uniqueness).

Proof: splices forward-classification's exact body (deriving `hfwd`
inline) with `lemma45_CN_domain_subset`'s exact verified body (re-read
from the snapshot to reuse its CORRECTED parenthesized-inner-`by` form,
not the failed round-1 draft).

Kernel-verified via the proofsearch MCP:
  episode d0133f44-3f8d-4726-80a6-d4197e207d13,
  problem_version_id 49645187-e87b-4571-bfa4-53aa71428c68.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5034faf6058f990e398d6bf02d72fdc41b53603f2decb193e54f3362d9a60960.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled domain subset: `{n:π n=a} ⊆ P_N(a)-image ∪ Q_N(a)-image`,
needing only `π 1=0` + range + soundness + the dichotomy theorem (all
opaque) — not the pre-derived `hfwd` forward-classification fact. -/
theorem lemma45_CN_domain_subset_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a : ℕ), N < a^4 → 1 ≤ a → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      (Finset.Icc 1 N).filter (fun n => π n = a) ⊆
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2) := by
  intro π N a hN4 ha hπ1 hax hsound hdichotomy
  have hfwd : ∀ n : ℕ, n ∈ Finset.Icc 1 N → π n = a → (∃ p : ℕ, Nat.Prime p ∧ a < p ∧ n = a * p) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ a < p ∧ a < q ∧ n = a * p * q) := (by
    intro n hnrange hpna
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
      exact ⟨p, q, hp, hq, hap, haq, (by rw [hnt, htpq]; ring)⟩)
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnmem, hpna⟩ := hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hnmem).2
  rw [Finset.mem_union]
  rcases hfwd n hnmem hpna with ⟨p,hp,hap,hnp⟩ | ⟨p,q,hp,hq,hap,haq,hnpq⟩
  · left
    rw [Finset.mem_image]
    refine ⟨p, ?_, hnp.symm⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hapN : a*p ≤ N := (by rw [← hnp]; exact hnN)
    have h1 : p ≤ a*p := (by nlinarith [ha, hp.pos])
    exact ⟨⟨by omega, by omega⟩, hp, hapN⟩
  · right
    rw [Finset.mem_image]
    rcases Classical.em (p ≤ q) with hpq | hpq
    · refine ⟨(p,q), ?_, hnpq.symm⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      have hapqN : a*p*q ≤ N := (by rw [← hnpq]; exact hnN)
      have e1 : a*(p*q) = a*p*q := (by ring)
      have hapqN' : a*(p*q) ≤ N := (by rw [e1]; exact hapqN)
      have e2 : a*p*q = p*(a*q) := (by ring)
      have h1 : 1 ≤ a*q := (by have h2 := Nat.mul_pos (show 0<a by omega) hq.pos; omega)
      have hp_le : p ≤ a*p*q := (by rw [e2]; nlinarith [h1])
      have e3 : a*p*q = q*(a*p) := (by ring)
      have h3 : 1 ≤ a*p := (by have h4 := Nat.mul_pos (show 0<a by omega) hp.pos; omega)
      have hq_le : q ≤ a*p*q := (by rw [e3]; nlinarith [h3])
      exact ⟨⟨⟨by omega, by omega⟩,⟨by omega, by omega⟩⟩, hp, hq, hpq, hapqN'⟩
    · have hqp : q < p := not_le.mp hpq
      refine ⟨(q,p), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        have hapqN : a*p*q ≤ N := (by rw [← hnpq]; exact hnN)
        have e1 : a*(q*p) = a*p*q := (by ring)
        have hqpN' : a*(q*p) ≤ N := (by rw [e1]; exact hapqN)
        have e3 : a*p*q = q*(a*p) := (by ring)
        have h3 : 1 ≤ a*p := (by have h4 := Nat.mul_pos (show 0<a by omega) hp.pos; omega)
        have hq_le : q ≤ a*p*q := (by rw [e3]; nlinarith [h3])
        have e2 : a*p*q = p*(a*q) := (by ring)
        have h1 : 1 ≤ a*q := (by have h2 := Nat.mul_pos (show 0<a by omega) hq.pos; omega)
        have hp_le : p ≤ a*p*q := (by rw [e2]; nlinarith [h1])
        exact ⟨⟨⟨by omega, by omega⟩,⟨by omega, by omega⟩⟩, hq, hp, by omega, hqpN'⟩
      · have e2 : a*q*p = a*p*q := (by ring)
        have e : a*q*p = n := (by rw [e2]; exact hnpq.symm)
        exact e

end Erdos858
