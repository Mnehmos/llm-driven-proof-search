/-
Erdős Problem #858 — parent-counting cast to ℝ (Chojecki 2026).

Cast bridge: the parent-counting identity `Σ_a C_N(a) = H_N − 1`, proven natively
over ℚ (`erdos858_parent_counting`, `Erdos858_ParentCounting.lean`), transported
to ℝ via `Rat.cast`, matching the real-valued convention the Prop 5.1 identity
(atom A2, `Erdos858_Thm12_A2_Prop51Identity.lean`) needs — the combinatorial
layer (§2–4) computes exact rationals; the analytic layer (§5+) works over ℝ.

Proof: `exact_mod_cast hQ` alone FAILS — `norm_cast`'s automation cannot bridge
a NESTED double-sum whose inner filter predicate depends on the outer bound
variable. The working fix: `congrArg (fun x:ℚ => (x:ℝ)) hQ` forces the cast
application explicitly (giving `(↑LHS:ℝ) = (↑RHS:ℝ)`), then `push_cast`
distributes it through `Σ`/`/`/`-`/`1`, landing exactly on the ℝ-native
statement.

Kernel-verified via the proofsearch MCP:
  episode 3820ab14-ed27-4169-9d90-59d70b58c931,
  problem_version_id 64513341-7ffb-4040-8f41-30dd5d7c5581.
Outcome: kernel_verified / root_kernel_verified (2nd submission — 1st tried
bare `exact_mod_cast hQ`, which failed to bridge the nested-sum-with-dependent-
filter structure; the `congrArg`+`push_cast` pattern below is the reusable fix
for casting ANY of the ℚ-valued frontier facts to ℝ).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 77abaabfe65325fe09bd7e4ed5eb2e1d5a7257b5c9311b6f492aca602af151ca.

**Lean lesson**: for casting a ℚ-valued equation with NESTED sums (especially
where an inner sum's filter predicate depends on an outer bound variable) to
another field like ℝ, `exact_mod_cast`/`norm_cast` alone are insufficient — use
`congrArg (fun x:ℚ => (x:ℝ)) hQ` to force the cast application explicitly, then
`push_cast at hR` to distribute it through the arithmetic structure, then
`exact hR`. This pattern is reusable for the OTHER ℚ-valued frontier facts
(#177, #178, `frontier_sweep_step`, `frontier_base_zero`) when they eventually
need casting for A2.
-/
import Mathlib

namespace Erdos858

/-- Parent-counting identity cast to ℝ: `Σ_a C_N(a) = H_N−1` transported from
ℚ (`erdos858_parent_counting`) via `congrArg`+`push_cast` — the reusable pattern
for bridging the ℚ-valued frontier layer to A2's ℝ-valued Prop 5.1 identity. -/
theorem erdos858_parent_counting_cast_R :
    ∀ (π : ℕ → ℕ) (N : ℕ),
      (∑ a ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - 1 →
      (∑ a ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℝ)/(n:ℝ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - 1 := by
  intro π N hQ
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQ
  push_cast at hR
  exact hR

end Erdos858
