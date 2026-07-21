/-
Erdős Problem #858 — Lemma 4.5 connection, `C_N(a)` domain equality — STAGE A COMPLETE (Chojecki 2026).

Combines `lemma45_CN_domain_subset` (`Erdos858_Lemma45_DomainSubset.lean`)
and `lemma45_CN_domain_supset` (`Erdos858_Lemma45_DomainSupset.lean`) into
the FULL Finset equality:

  `{n∈[1,N]:π(n)=a} = (P_N(a)-domain).image(a·p) ∪ (Q_N(a)-domain).image(a·p·q)`

This is **Stage A of the `C_N(a)=R_N(a)/a` bijection COMPLETE** — the index
set underlying `C_N(a)` is now exactly characterized as the disjoint union
of the single-prime and semiprime images matching `P_N(a)`/`Q_N(a)`'s exact
domains (`Erdos858_Prop46_PNMonotone.lean`/`QNMonotone.lean`). Pure
bookkeeping glue via `Finset.Subset.antisymm`, no new math.

**Remaining for the FULL `C_N(a)=R_N(a)/a` sum identity (Stage B, not yet
attempted)**: convert this Finset equality into a SUM equality via
`Finset.sum_union` (using `lemma45_apq_disjoint_from_ap` for disjointness)
+ `Finset.sum_image` (using single-prime injectivity [trivial, not yet a
standalone atom] and `lemma45_semiprime_pair_injective`
(`Erdos858_Lemma45_SemiprimePairInjective.lean`)) to turn
`Σ_{n∈{n:π n=a}}1/n` into `Σ1/(a·p) + Σ1/(a·p·q)`, then factor `1/a` out
via `Finset.sum_div`/`mul_sum` to land on `(1/a)(P_N(a)+Q_N(a))`.

Kernel-verified via the proofsearch MCP:
  episode 45016c0f-1e85-490a-9020-4873c7d1a4d7,
  problem_version_id 908e4289-9714-46e2-a1ec-f21114bf1141.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f34d289f694d7a23ee31f61eb17f01429fef3b17fad6f4d790d734aa5a310196.
-/
import Mathlib

namespace Erdos858

/-- `C_N(a)` domain equality (Stage A capstone): `{n:π n=a} = P_N(a)-image ∪
Q_N(a)-image`, combining `lemma45_CN_domain_subset` + `_supset` via
`Finset.Subset.antisymm`. -/
theorem lemma45_CN_domain_eq :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      ((Finset.Icc 1 N).filter (fun n => π n = a) ⊆
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2)) →
      (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2)
        ⊆ (Finset.Icc 1 N).filter (fun n => π n = a)) →
      (Finset.Icc 1 N).filter (fun n => π n = a) =
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2) := by
  intro π N a hsub hsup
  exact Finset.Subset.antisymm hsub hsup

end Erdos858
