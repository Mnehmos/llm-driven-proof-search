/-
Erdős Problem #858 — Lemma 4.5 connection, Stage B piece 1: images disjoint (Chojecki 2026).

The `P_N(a)`-image and `Q_N(a)`-image Finsets are disjoint, using
`lemma45_apq_disjoint_from_ap` (`Erdos858_Lemma45_ApqDisjointFromAp.lean`,
taken as hypothesis `hdisj`) as the underlying fact. Needed for
`Finset.sum_union` to split `Σ_{n∈union}1/n` into the single-prime and
semiprime pieces (Stage B of the `C_N(a)=R_N(a)/a` bijection).

Proof: `Finset.disjoint_left` — any `x` in both images gives `x=a·p` and
`x=a·p'·q'`, contradicting `hdisj`. Applies the `#198`/`#199` lesson:
`hp'`/`hq'` re-typed via type-ascribed `have`s from `hpqmem.2.1`/`.2.2.1`
(tolerating the `(p',q').1` defeq to `p'`).

Kernel-verified via the proofsearch MCP:
  episode 72a9109d-c4b5-4e96-a1b1-2d43f2c84634,
  problem_version_id 585878b8-43be-4941-bd0f-25da05aec7a0.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c88398b29b23cbb3e58f58a1df8fee053eab3791141d3084134186f204069d6c.
-/
import Mathlib

namespace Erdos858

/-- Stage B piece 1: the `P_N(a)`/`Q_N(a)` images are disjoint Finsets. -/
theorem lemma45_images_disjoint :
    ∀ (a N : ℕ), 1 ≤ a →
      (∀ p p' q' : ℕ, Nat.Prime p → Nat.Prime p' → Nat.Prime q' → a * p ≠ a * p' * q') →
      Disjoint (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p))
        ((((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2)) := by
  intro a N ha hdisj
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
  exact hdisj p p' q' hp hp' hq' heq

end Erdos858
