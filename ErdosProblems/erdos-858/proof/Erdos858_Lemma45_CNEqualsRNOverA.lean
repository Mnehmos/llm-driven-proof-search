/-
Erdős Problem #858 — Lemma 4.5 CAPSTONE: C_N(a) = R_N(a)/a (Chojecki 2026).

**THE CAPSTONE of the entire Lemma 4.5 connection effort.** The full sum
identity:

  `Σ_{n∈[1,N]:π(n)=a} 1/n = (1/a) · (P_N(a) + Q_N(a))`

Combines Stage A (`lemma45_CN_domain_eq`, `Erdos858_Lemma45_DomainEquality.lean`
— the Finset equality, taken as hypothesis `hdeq`), Finset disjointness
(`lemma45_images_disjoint`, `Erdos858_Lemma45_ImagesDisjoint.lean` — `hdisj`),
and semiprime-pair injectivity (`lemma45_semiprime_pair_injective`,
`Erdos858_Lemma45_SemiprimePairInjective.lean` — `hinj2`) via
`Finset.sum_union` + `Finset.sum_image` (twice — single-prime injectivity
is a one-line `Nat.eq_of_mul_eq_mul_left` fact, proven inline) + field
arithmetic (`push_cast`+`field_simp`) to factor out `1/a`.

**This discharges A2's `hCR` hypothesis — the LAST of A2's four hypotheses
(`hSK`, `hC0`, `hHdiff`, `hCR`)** — for the ℚ-valued form. Combined with the
already-proven `hSK`/`hC0`/`hHdiff` (all ℝ, via the `congrArg`+`push_cast`
cast pattern), and once this ℚ result is ALSO cast to ℝ the same way,
`Erdos858_Thm12_A2_Prop51Identity.lean`'s Prop 5.1 identity becomes fully
unconditional (modulo assembling the pieces into one instantiation).

Proof: `rw[hdeq]` switches to the union form; `Finset.sum_union hdisj`
splits the sum; two `Finset.sum_image` applications (single-prime
injectivity inline, semiprime via `hinj2`+`Prod.ext`) convert each piece to
a sum over the ORIGINAL index (`p` or `(p,q)`); `mul_add`+`Finset.mul_sum`
distributes `1/a` on the RHS; `congr 1` splits into two per-sum-type goals,
each closed by `Finset.sum_congr` + `push_cast` + `field_simp` (with
explicit nonzero-denominator `have`s derived via `omega` from the `Icc`
lower bounds `a+1≤p`).

Kernel-verified via the proofsearch MCP:
  episode 3738be37-efff-4b29-9ba2-29e13f7ea98f,
  problem_version_id 625e2bf8-56f9-4b92-92d2-72c749a40d95.
Outcome: kernel_verified / root_kernel_verified (2nd submission — 1st hit a
simple argument-order bug calling `hinj2`: its signature groups all 4 `ℕ`
positional args first (`p q p' q'`) then all 7 hypothesis args, but the
submission interleaved them (`x.1 x.2 hx1 hx2 hx3 y.1 y.2 ...`) mirroring a
mental "p pairs with hp" association that doesn't match the actual
∀-binder grouping in the signature).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash befd77201c613d7fd900a38bdc24e7906c424debac7100a0719d78cabd078167.

**Lean lesson**: when calling a hypothesis with signature
`∀(a b c d:T),P a→P b→...→Q c d`, pass ALL positional args of the SAME
∀-binder group in source order BEFORE any hypothesis args — do not
interleave nat/prop arguments to mirror a mental pairing (`p` with `hp`,
`q` with `hq`); the actual argument order is fixed by the signature's
binder grouping, not by logical association.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 CAPSTONE: `C_N(a) = R_N(a)/a`, i.e.
`Σ_{n:π n=a}1/n = (1/a)(P_N(a)+Q_N(a))`. Combines the Stage A Finset
equality, Finset disjointness, and semiprime-pair injectivity via
`Finset.sum_union`+`Finset.sum_image`+field arithmetic. Discharges A2's
final open hypothesis `hCR`. -/
theorem lemma45_CN_eq_RN_over_a :
    ∀ (π : ℕ → ℕ) (N a : ℕ), 1 ≤ a →
      ((Finset.Icc 1 N).filter (fun n => π n = a) =
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
          ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
              (fun pq => a * pq.1 * pq.2)) →
      (Disjoint (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p))
        ((((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2))) →
      (∀ p q p' q' : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → Nat.Prime p' → Nat.Prime q' → p' ≤ q' →
        a * p * q = a * p' * q' → p = p' ∧ q = q') →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℚ)/(n:ℚ)) =
        (1/(a:ℚ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℚ)/(p:ℚ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℚ)/((pq.1:ℚ)*(pq.2:ℚ)))) := by
  intro π N a ha hdeq hdisj hinj2
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
    obtain ⟨he1,he2⟩ := hinj2 x.1 x.2 y.1 y.2 hx1 hx2 hx3 hy1 hy2 hy3 hxy
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
    field_simp

end Erdos858
