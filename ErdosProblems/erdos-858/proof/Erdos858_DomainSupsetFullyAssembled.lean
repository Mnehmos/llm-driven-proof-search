/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED domain supset (Chojecki 2026).

Reduces `lemma45_CN_domain_supset`'s (`Erdos858_Lemma45_DomainSupset.lean`)
`hrevap`/`hrevapq` hypotheses to genuinely primitive π-structure axioms
(range, maximality, soundness) plus standalone theorems (`lemma21_sandwich`,
`lemma27_pi_ap_full`, the gap-bounds B1/B2, `lemma45_pi_apq_subfact`,
`lemma45_apq_uniqueness`) — INLINING the literal-π-value derivations
(mirroring `literal_pi_value_ap_fully_assembled`/`_apq_fully_assembled`)
directly at each call site, where the `a·p≤N`/`a·p·q≤N` bound needed by the
N-bounded range axiom is naturally available from the Finset membership
conditions (`hapN`/`hapqN`).

**Note**: `N<a^4` must be an EXPLICIT top-level hypothesis here — it is NOT
derivable from `a·p·q≤N` alone (they bound `N` from opposite directions);
this was a real gap caught mid-draft before submission.

The single largest splice attempted this session (~60 lines combining 6
previously-separate proof bodies: `lemma45_CN_domain_supset` plus TWO
inline copies of the maximality→sandwich→uniqueness pi-value-bridge logic)
— verified on the FIRST submission.

Kernel-verified via the proofsearch MCP:
  episode 989a07b5-7270-486e-baeb-dbfda990a102,
  problem_version_id 8e5eda85-d5ac-4ef7-b778-8d742cf8b7b3.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 25413f8cb824761db7ab5b29c4da83ca01a29665f30f1a4ae1c82ee595cf5f78.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled domain supset: `P_N(a)-image ∪ Q_N(a)-image ⊆ {n:π n=a}`,
needing only the range axiom, maximality, soundness, sandwich, `lemma27`,
gap-bounds B1/B2, subfact, and `apq`-uniqueness (all opaque) — not the
pre-derived `hrevap`/`hrevapq` literal π-value facts. -/
theorem lemma45_CN_domain_supset_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a : ℕ), N < a^4 → 1 ≤ a →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      (∀ a' p' : ℕ, 1 ≤ a' → Nat.Prime p' → a' < p' →
        (∃ t : ℕ, a' * p' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) ∧
          (∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
            (∃ w : ℕ, a' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a' ∨ b = a' * p')) →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → a' * p' * q' ≤ N' → N' < a' ^ 4 → q' < a' * p') →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → p' ≤ q' → a' * p' * q' ≤ N' → N' < a' ^ 4 → p' < a' * q') →
      (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
      (∀ a' p' q' : ℕ, 1 ≤ a' → Nat.Prime p' → Nat.Prime q' → a' < p' → p' ≤ q' →
        q' < a' * p' → p' < a' * q' →
        (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        ∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
          (∃ w : ℕ, a' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
          b = a' ∨ b = a' * p' * q') →
      (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2))
        ⊆ (Finset.Icc 1 N).filter (fun n => π n = a) := by
  intro π N a hN4 ha hax hmax hsound hsandwich hlemma27 hB1 hB2 hsubfact huniqapq
  intro n hn
  rw [Finset.mem_union] at hn
  rw [Finset.mem_filter, Finset.mem_Icc]
  rcases hn with hn | hn
  · rw [Finset.mem_image] at hn
    obtain ⟨p, hpmem, hpn⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hpmem
    obtain ⟨⟨hap1, hpN⟩, hp, hapN⟩ := hpmem
    rw [← hpn]
    refine ⟨⟨?_, hapN⟩, ?_⟩
    · nlinarith [ha, hp.pos]
    · have hap : a < p := by omega
      obtain ⟨hexap, huniqap⟩ := hlemma27 a p ha hp hap
      have hn2ap : 2 ≤ a*p := (by nlinarith [hp.two_le, ha])
      have hrangeap : π (a*p) < a*p := (hax (a*p) hn2ap hapN).2
      have hanap : a < a*p := (by nlinarith [hp.two_le, ha])
      have haleap : a ≤ π (a*p) := hmax a (a*p) hanap hexap
      rcases haleap.lt_or_eq with hltap | heqap
      · have hasandap := hsandwich a (π (a*p)) (a*p) hltap hrangeap hexap (hsound (a*p) hn2ap)
        rcases huniqap (π (a*p)) hasandap (hsound (a*p) hn2ap) with h1ap | h1ap
        · exact h1ap
        · exfalso
          omega
      · exact heqap.symm
  · rw [Finset.mem_image] at hn
    obtain ⟨⟨p,q⟩, hpqmem, hpqn0⟩ := hn
    have hpqn : a*p*q = n := hpqn0
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpqmem
    obtain ⟨⟨⟨hap10,hpN0⟩,⟨haq10,hqN0⟩⟩, hp0, hq0, hpq0, hapqN0⟩ := hpqmem
    have hap1 : a+1 ≤ p := hap10
    have hpN : p ≤ N := hpN0
    have haq1 : a+1 ≤ q := haq10
    have hqN : q ≤ N := hqN0
    have hp : Nat.Prime p := hp0
    have hq : Nat.Prime q := hq0
    have hpq : p ≤ q := hpq0
    have hapqN : a*(p*q) ≤ N := hapqN0
    have hapqN' : a*p*q ≤ N := (by have e : a*p*q = a*(p*q) := (by ring); rw [e]; exact hapqN)
    have hpos : 0 < a*p*q := (by have h1 : 0 < a*p := Nat.mul_pos (by omega) hp.pos; exact Nat.mul_pos h1 hq.pos)
    rw [← hpqn]
    refine ⟨⟨by omega, hapqN'⟩, ?_⟩
    have hap : a < p := by omega
    have haq : a < q := by omega
    have hB1' : q < a*p := hB1 a p q N ha hap hapqN' hN4
    have hB2' : p < a*q := hB2 a p q N ha hap hpq hapqN' hN4
    have hexapq : ∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := ⟨p*q, (by ring), fun r hr hrpq => ((Nat.Prime.dvd_mul hr).mp hrpq).elim (fun hrp => by rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp hrp]; exact hap) (fun hrq => by rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp hrq]; exact haq)⟩
    have huniqapq2 := huniqapq a p q ha hp hq hap hpq hB1' hB2' hsubfact
    have hn2apq : 2 ≤ a*p*q := (by nlinarith [hp.two_le, hq.two_le, ha])
    have hrangeapq : π (a*p*q) < a*p*q := (hax (a*p*q) hn2apq hapqN').2
    have hanapq : a < a*p*q := (by nlinarith [hp.two_le, hq.two_le, ha])
    have haleapq : a ≤ π (a*p*q) := hmax a (a*p*q) hanapq hexapq
    rcases haleapq.lt_or_eq with hltapq | heqapq
    · have hasandapq : ∃ t : ℕ, π (a*p*q) = a*t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := hsandwich a (π (a*p*q)) (a*p*q) hltapq hrangeapq hexapq (hsound (a*p*q) hn2apq)
      rcases huniqapq2 (π (a*p*q)) hasandapq (hsound (a*p*q) hn2apq) with h1apq | h1apq
      · exact h1apq
      · exfalso
        omega
    · exact heqapq.symm

end Erdos858
