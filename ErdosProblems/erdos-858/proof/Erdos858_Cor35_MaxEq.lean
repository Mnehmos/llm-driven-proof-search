/-
Erdős Problem #858 — Corollary 3.5 capstone: M(N) = S_N(K).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Corollary 3.5 / Theorem 1.1's frontier reduction.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode f6aa8db6-ce90-4b06-afb7-d97c9d729319,
problem_version_id 81e87e62-3d15-4d77-9f6c-9ac9229157dd.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 2bf2793f…

M(N) := the maximum reciprocal-weight Σ_{n∈B} 1/n over admissible ⪯-antichains
B ⊆ [1,N]. Concretely the achievable-weight set is
    IMG := ((Icc 1 N).powerset.filter Anti).image (fun B => Σ_{n∈B} w n),
and "M(N) = S" is exactly "S ∈ IMG ∧ (∀ x ∈ IMG, x ≤ S)" (S is achieved and is
an upper bound, i.e. S is the maximum). This theorem proves that characterization
from the two verified directions of the max-closure duality, taken as
hypotheses:
  • hub  — the ≤ direction (Erdos858_Cor35_LeDirection): every admissible
           antichain B ⊆ [1,N] has Σ_B w ≤ S. (Since M(N) is the max, M(N) ≤ S.)
  • hex  — the ≥ witness: ∃ admissible antichain B0 ⊆ [1,N] with Σ_{B0} w = S,
           namely A_N(K) = ∂[1,K] (an antichain by Lemma 3.1, weight S_N(K) by
           Prop 3.2). (So M(N) ≥ S.)

Discharging hub with Erdos858_Cor35_LeDirection and hex with
Lemma 3.1 + Prop 3.2 (S := S_N(K), w := fun n => 1/n, Anti := ⪯-antichain) gives
the full Corollary 3.5: M(N) = S_N(K). This is the frontier reduction that, once
combined with the (analytic) sign theorem of §4, yields Theorem 1.1
(M(N) = M_fr(N)).

Lean note: the statement bakes an explicit `Classical.decPred` instance into the
`Finset.filter`; `rw [Finset.mem_filter]` then fails to re-synthesize
`DecidablePred`, so the instance is pinned via
`@Finset.mem_filter _ _ (Classical.decPred _) _ _`.
-/
import Mathlib

namespace Erdos858

/-- Corollary 3.5, `M(N) = S_N(K)` as a max characterization: `S` is both a
member and an upper bound of the achievable-weight set of admissible antichains,
given the verified `≤` direction (`hub`) and a `≥` witness (`hex`). -/
theorem cor35_max_eq :
    ∀ (N : ℕ) (w : ℕ → ℚ) (S : ℚ) (Anti : Finset ℕ → Prop),
      (∀ B : Finset ℕ, Anti B → B ⊆ Finset.Icc 1 N → (∑ n ∈ B, w n) ≤ S) →
      (∃ B0 : Finset ℕ, Anti B0 ∧ B0 ⊆ Finset.Icc 1 N ∧ (∑ n ∈ B0, w n) = S) →
      S ∈ (@Finset.filter (Finset ℕ) (fun B => Anti B) (Classical.decPred _) (Finset.Icc 1 N).powerset).image (fun B => ∑ n ∈ B, w n) ∧
      (∀ x ∈ (@Finset.filter (Finset ℕ) (fun B => Anti B) (Classical.decPred _) (Finset.Icc 1 N).powerset).image (fun B => ∑ n ∈ B, w n), x ≤ S) := by
  intro N w S Anti hub hex
  obtain ⟨B0, hAnti0, hB0sub, hB0eq⟩ := hex
  constructor
  · rw [Finset.mem_image]
    refine ⟨B0, ?_, hB0eq⟩
    rw [@Finset.mem_filter (Finset ℕ) (fun B => Anti B) (Classical.decPred _) (Finset.Icc 1 N).powerset B0, Finset.mem_powerset]
    exact ⟨hB0sub, hAnti0⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨B, hBmem, hBeq⟩ := hx
    rw [@Finset.mem_filter (Finset ℕ) (fun B => Anti B) (Classical.decPred _) (Finset.Icc 1 N).powerset B, Finset.mem_powerset] at hBmem
    rw [← hBeq]
    exact hub B hBmem.2 hBmem.1

end Erdos858
