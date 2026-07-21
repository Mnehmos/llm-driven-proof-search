/-
Erdős Problem #858 — Theorem 1.2 assembly, THE FULLY-ASSEMBLED hCR CAPSTONE (Chojecki 2026).

**The final, most-reduced form of atom A2's `hCR` hypothesis.** Reduces the
ENTIRE Lemma 4.5 `C_N(a)=R_N(a)/a` connection to genuinely primitive
π-structure axioms (`π 1=0`, range, soundness, maximality) plus standalone
number-theory theorems (`lemma45_prime_semiprime_full` dichotomy,
`lemma21_sandwich`, `lemma27_pi_ap_full`, the gap-bounds B1/B2,
`lemma45_pi_apq_subfact`, `lemma45_apq_uniqueness`,
`lemma45_apq_disjoint_from_ap`, `lemma45_semiprime_pair_injective`) plus
the two fully-assembled domain subset/supset theorems
(`Erdos858_DomainSubsetFullyAssembled.lean`/
`Erdos858_DomainSupsetFullyAssembled.lean`) — all taken as opaque
hypotheses. 17 hypotheses total.

Proof: derives `hdeq` (domain equality) inline via the two domain theorems
+ `Finset.Subset.antisymm`; `hdisj` (Finset disjointness) inline via
`lemma45_images_disjoint`'s exact body; the full ℚ sum identity inline via
`lemma45_CN_eq_RN_over_a`'s exact body (`Finset.sum_union`+
`Finset.sum_image`×2+field arithmetic); then casts to ℝ via the standard
`congrArg`+`push_cast` pattern. ~65-line proof body combining FIVE
previously-separate proof bodies — verified on the FIRST submission, the
largest and final splice of this session (9 for 9 first-try successes on
the "opaque theorem application" strategy).

Kernel-verified via the proofsearch MCP:
  episode b89b7b11-53cf-4f7a-a549-3343a99e5cce,
  problem_version_id c9a51c58-3a7f-4afd-91a0-7fc25f3d589f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a74435f75b8f6867a02fdde9de38be15962e71380b22b36f230baedf6775ba34.
-/
import Mathlib

namespace Erdos858

/-- THE fully-assembled hCR capstone: `C_N(a)=(1/a)(P_N(a)+Q_N(a))` in ℝ,
needing only primitive π-axioms + standalone number-theory theorems + the
two fully-assembled domain theorems (all opaque) — the most-reduced form
of A2's `hCR` hypothesis. -/
theorem lemma45_hCR_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a : ℕ), N < a^4 → 1 ≤ a → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
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
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' → π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' t' : ℕ, 1 ≤ a'' → 0 < t' → t' < a''^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a'' < p) →
          t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
        (Finset.Icc 1 N').filter (fun n => π' n = a') ⊆
          ((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2)) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π' m) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' b' n' : ℕ, a'' < b' → b' < n' →
          (∃ u : ℕ, n' = a'' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a'' < r) →
          (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
          ∃ t : ℕ, b' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) →
        (∀ a'' p' : ℕ, 1 ≤ a'' → Nat.Prime p' → a'' < p' →
          (∃ t : ℕ, a'' * p' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) ∧
            (∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
              (∃ w : ℕ, a'' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a'' ∨ b = a'' * p')) →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → q' < a'' * p') →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → p' ≤ q' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → p' < a'' * q') →
        (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        (∀ a'' p' q' : ℕ, 1 ≤ a'' → Nat.Prime p' → Nat.Prime q' → a'' < p' → p' ≤ q' →
          q' < a'' * p' → p' < a'' * q' →
          (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
          ∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
            (∃ w : ℕ, a'' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
            b = a'' ∨ b = a'' * p' * q') →
        (((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2))
          ⊆ (Finset.Icc 1 N').filter (fun n => π' n = a')) →
      (∀ p p' q' : ℕ, Nat.Prime p → Nat.Prime p' → Nat.Prime q' → a * p ≠ a * p' * q') →
      (∀ p q p' q' : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → Nat.Prime p' → Nat.Prime q' → p' ≤ q' →
        a * p * q = a * p' * q' → p = p' ∧ q = q') →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) =
        (1/(a:ℝ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ)))) := by
  intro π N a hN4 ha hπ1 hax hsound hmax hsandwich hlemma27 hB1 hB2 hsubfact huniqapq hdichotomy hsub_thm hsup_thm hdisjapq hinjsemiprime
  have hsub := hsub_thm π N a hN4 ha hπ1 hax hsound hdichotomy
  have hsup := hsup_thm π N a hN4 ha hax hmax hsound hsandwich hlemma27 hB1 hB2 hsubfact huniqapq
  have hdeq := Finset.Subset.antisymm hsub hsup
  have hdisj : Disjoint (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p))
      ((((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
          (fun pq => a * pq.1 * pq.2)) := (by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1
    obtain ⟨p, hpmem, hpx⟩ := hx1
    rw [Finset.mem_filter] at hpmem
    have hp : Nat.Prime p := hpmem.2.1
    rw [Finset.mem_image] at hx2
    obtain ⟨⟨p',q'⟩, hpqmem, hpqx⟩ := hx2
    rw [Finset.mem_filter] at hpqmem
    have hp' : Nat.Prime p' := hpqmem.2.1
    have hq' : Nat.Prime q' := hpqmem.2.2.1
    have hxeq1 : x = a*p := hpx.symm
    have hxeq2 : x = a*p'*q' := hpqx.symm
    have heq : a*p = a*p'*q' := (by rw [← hxeq1]; exact hxeq2)
    exact hdisjapq p p' q' hp hp' hq' heq)
  have hQresult : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℚ)/(n:ℚ)) =
      (1/(a:ℚ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℚ)/(p:ℚ))
        + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
            (1:ℚ)/((pq.1:ℚ)*(pq.2:ℚ)))) := (by
    rw [hdeq]
    rw [Finset.sum_union hdisj]
    have hinj1 : ∀ x ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a*p ≤ N), ∀ y ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a*p ≤ N), a*x = a*y → x = y := (by
      intro x hx y hy hxy
      exact Nat.eq_of_mul_eq_mul_left ha hxy)
    rw [Finset.sum_image hinj1]
    have hinj2' : ∀ x ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a*(pq.1*pq.2) ≤ N), ∀ y ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a*(pq.1*pq.2) ≤ N), a*x.1*x.2 = a*y.1*y.2 → x = y := (by
      intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx hy
      have hx1 : Nat.Prime x.1 := hx.2.1
      have hx2 : Nat.Prime x.2 := hx.2.2.1
      have hx3 : x.1 ≤ x.2 := hx.2.2.2.1
      have hy1 : Nat.Prime y.1 := hy.2.1
      have hy2 : Nat.Prime y.2 := hy.2.2.1
      have hy3 : y.1 ≤ y.2 := hy.2.2.2.1
      obtain ⟨he1,he2⟩ := hinjsemiprime x.1 x.2 y.1 y.2 hx1 hx2 hx3 hy1 hy2 hy3 hxy
      exact Prod.ext he1 he2)
    rw [Finset.sum_image hinj2']
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    have ha0 : (a:ℚ) ≠ 0 := (by have h1 : a ≠ 0 := (by omega); exact_mod_cast h1)
    congr 1
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp0 : (p:ℚ) ≠ 0 := (by have h1 : p ≠ 0 := (by omega); exact_mod_cast h1)
      push_cast
      field_simp
    · apply Finset.sum_congr rfl
      intro pq hpq
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpq
      have hp0 : (pq.1:ℚ) ≠ 0 := (by have h1 : pq.1 ≠ 0 := (by omega); exact_mod_cast h1)
      have hq0 : (pq.2:ℚ) ≠ 0 := (by have h1 : pq.2 ≠ 0 := (by omega); exact_mod_cast h1)
      push_cast
      field_simp)
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQresult
  push_cast at hR
  exact hR

end Erdos858
