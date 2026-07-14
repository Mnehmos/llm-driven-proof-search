/-
Erdős Problem #858 — Proposition 3.4 (max-closure identity).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 3.4.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 7ffe3b0d-97c8-4eb6-a193-1c05d6178333,
problem_version_id ca019ca3-4afe-4932-a50e-7e641a1635c2.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b2bfcaa4…

For a continuation set D (downward-closed under the parent map π, with 1 ∈ D),
the boundary ∂D = {n ≤ N : n ∉ D ∧ π n ∈ D} has reciprocal-sum
    Σ_{n∈∂D} 1/n = 1 + Σ_{a∈D} q_N(a),
where q_N(a) = C_N(a) − 1/a and C_N(a) = Σ_{m≤N : π m = a} 1/m. This is the
structural heart of the reduction M(N) = 1 + max_D Σ_{a∈D} q_N (Cor 3.5): each
continuation set's boundary weight equals 1 plus its q-sum.

Proof: fiberwise grouping (Finset.sum_fiberwise_of_maps_to) gives
Σ_{a∈D} C_N(a) = Σ_{m : π m ∈ D} 1/m; the domain {m : π m ∈ D} partitions as
∂D ⊍ (D \ {1}) (every non-root of D has its parent in D by downward-closure;
every non-D vertex with parent in D is a boundary vertex; the root is excluded
since π 1 = 0 ∉ D); splitting the root off Σ_{a∈D} 1/a and cancelling yields the
identity.
-/
import Mathlib

namespace Erdos858

/-- Proposition 3.4. `Σ_{n∈∂D} 1/n = 1 + Σ_{a∈D} q_N(a)` for a continuation set
`D` (downward-closed, `1 ∈ D`). -/
theorem prop34_max_closure_identity :
    ∀ (π : ℕ → ℕ) (N : ℕ) (D : Finset ℕ), π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) → D ⊆ Finset.Icc 1 N → 1 ∈ D →
      (∀ n ∈ D, 2 ≤ n → π n ∈ D) →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D), (1:ℚ)/(n:ℚ))
        = 1 + ∑ a ∈ D, ((∑ m ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(m:ℚ))
            - 1/(a:ℚ)) := by
  intro π N D hπ1 hax hDsub hone hclosed
  have h0notin : (0:ℕ) ∉ D := by
    intro h0
    have := hDsub h0
    simp only [Finset.mem_Icc] at this
    omega
  have hfib : (∑ a ∈ D, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(m:ℚ))
      = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => π m ∈ D), (1:ℚ)/(m:ℚ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.Icc 1 N).filter (fun m => π m ∈ D)) (t := D) (g := π) (f := fun m => (1:ℚ)/(m:ℚ)) (fun m hm => (Finset.mem_filter.mp hm).2)]
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmS, hmeq⟩
      exact ⟨⟨hmS, by rw [hmeq]; exact ha⟩, hmeq⟩
    · rintro ⟨⟨hmS, _⟩, hmeq⟩
      exact ⟨hmS, hmeq⟩
  have hdisj : Disjoint ((Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D)) (D.filter (fun m => 2 ≤ m)) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_filter] at hm hm'
    exact hm.2.1 hm'.1
  have hpart : (Finset.Icc 1 N).filter (fun m => π m ∈ D)
      = ((Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D)) ∪ (D.filter (fun m => 2 ≤ m)) := by
    ext m
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hmS, hpiD⟩
      by_cases hmD : m ∈ D
      · right
        refine ⟨hmD, ?_⟩
        by_contra hlt
        have hm1 : m = 1 := by
          have := hDsub hmD
          simp only [Finset.mem_Icc] at this
          omega
        rw [hm1, hπ1] at hpiD
        exact h0notin hpiD
      · left; exact ⟨hmS, hmD, hpiD⟩
    · rintro (⟨hmS, hmD, hpiD⟩ | ⟨hmD, hm2⟩)
      · exact ⟨hmS, hpiD⟩
      · exact ⟨hDsub hmD, hclosed m hmD hm2⟩
  have hDsplit : (∑ a ∈ D, (1:ℚ)/(a:ℚ)) = (∑ a ∈ D.filter (fun m => 2 ≤ m), (1:ℚ)/(a:ℚ)) + 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not D (fun m => 2 ≤ m)]
    have hsingle : D.filter (fun m => ¬ 2 ≤ m) = {1} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨haD, ha2⟩
        have := hDsub haD
        simp only [Finset.mem_Icc] at this
        omega
      · rintro rfl
        exact ⟨hone, by omega⟩
    rw [hsingle, Finset.sum_singleton]
    norm_num
  rw [Finset.sum_sub_distrib, hfib, hpart, Finset.sum_union hdisj, hDsplit]
  ring

end Erdos858
