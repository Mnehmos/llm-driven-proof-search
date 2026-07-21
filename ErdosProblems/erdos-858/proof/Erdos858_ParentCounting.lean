/-
Erdős Problem #858 — parent-counting identity (Chojecki 2026).

`Σ_{a=1}^N C_N(a) = H_N − 1`, where `C_N(a) = Σ_{n≤N:π n=a} 1/n` and
`H_N = Σ_{n=1}^N 1/n`. Discharges the parent-counting half of the `hSK`
hypothesis of the Prop 5.1 identity (Theorem 1.2 assembly, atom A2,
`Erdos858_Thm12_A2_Prop51Identity.lean`).

Assembled from `frontier_sweep_step` (per-K increment
`S_N(K+1)=S_N(K)+(C_N(K+1)−1/(K+1))`, `Erdos858_FrontierSweepStep.lean`),
`frontier_base_zero` (`S_N(0)=1`, `Erdos858_FrontierBaseZero.lean`),
`erdos858_frontier_top_zero` (`S_N(N)=0`, `Erdos858_FrontierTopZero.lean`), and
the ℚ-valued telescoping identity (`erdos858_telescoping_Q`,
`Erdos858_TelescopingQ.lean`): instantiating telescoping at `S := S_N` over
`[0,N]` gives `Σ_{a=1}^N(C_N(a)−1/a) = S_N(N)−S_N(0) = −1`; splitting the sum
gives `Σ C_N(a) − H_N = −1`, i.e. `Σ C_N(a) = H_N − 1`.

Proof: `hstep` converts each per-K step (via `frontier_sweep_step` at `K:=a−1`,
with a `Nat.cast_sub`-based cast bridge for the `((a−1:ℕ):ℚ)+1=(a:ℚ)` denominator)
into the generic `S(a)−S(a−1)` increment form telescoping needs; the telescoping
application is instantiated at the EXPLICIT `S_N` lambda directly (not via `set`,
per the banked opacity lesson); `Finset.sum_sub_distrib` (used as a `rw`, not a
bare term — see Lean lessons) splits the combined sum; `Finset.sum_congr` +
`hbase`/`htop` substitute the boundary values; a final `Finset.Ioc 0 N = Finset.Icc
1 N` identity (`ext`+`omega`) aligns the summation ranges.

Kernel-verified via the proofsearch MCP:
  episode 3834e2d6-59ff-4311-9a39-60493efcb4ba,
  problem_version_id 52d8eeb6-f8e8-491e-a53c-0d7eef5439d2.
Outcome: kernel_verified / root_kernel_verified (3rd submission — 1st/2nd hit
THREE separate instances of the "bare `:= by tac;` swallows the chain" pitfall
within ONE nested `have` [`hK`, `haeq`, `hcast` — parenthesizing only `hcast`
first left `hK`/`haeq` still swallowing; a full sweep was needed], plus a
`Finset.sum_sub_distrib` term-mode application failing to unify against the
expected type [fixed via `rw` instead of direct term application], plus a
beta-reduction display mismatch where `hS0`/`hSN` needed to be stated in the
POST-`sum_congr`-rewrite REDUCED form, not the raw lambda-application form).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 23e7d39c8d5f1b349cad141b0665f780228b117e4e3e55e639ff742b6c264471.

**Lean lessons**: (1) when a proof has MULTIPLE `have X := by tac` sub-steps at
the SAME nesting level, EVERY one needs parenthesizing if more chain follows —
fixing only the LAST one and missing earlier ones in the same `have`-chain
reproduces the identical error, since the earlier bare `by`-blocks each
independently swallow everything after them. (2) `Finset.sum_sub_distrib`
(and similar structural lemmas with explicit function arguments) may fail to
unify as a bare term against a computed expected type — prefer `by rw
[Finset.sum_sub_distrib]` (tactic-mode, more flexible unification) over direct
term application. (3) After a `Finset.sum_congr`-based rewrite, Lean
auto-beta-reduces the SURROUNDING (untouched) parts of the hypothesis for
display — a later `rw` targeting those parts must be stated in the ALREADY-
REDUCED form (the direct summation, not `(fun K => ...) N`), not the original
unreduced lambda-application form the earlier `have` used.
-/
import Mathlib

namespace Erdos858

/-- Parent-counting identity: `Σ_{a=1}^N C_N(a) = H_N−1`. Assembled from
`frontier_sweep_step`+`frontier_base_zero`+`erdos858_frontier_top_zero`+
`erdos858_telescoping_Q`. Discharges A2's parent-counting input. -/
theorem erdos858_parent_counting :
    ∀ (π : ℕ → ℕ) (N : ℕ), 1 ≤ N → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ (π' : ℕ → ℕ) (N' K : ℕ), π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) → K + 1 ≤ N' →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K + 1 ∧ K + 1 < n), (1:ℚ)/(n:ℚ))
          = (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ))
            + ((∑ n ∈ (Finset.Icc 1 N').filter (fun m => π' m = K + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K:ℚ) + 1))) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), 1 ≤ N' → π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n) →
        (Finset.Icc 1 N').filter (fun n => π' n ≤ 0 ∧ 0 < n) = {1}) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), (Finset.Icc 1 N').filter (fun n => π' n ≤ N' ∧ N' < n) = ∅) →
      (∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n → ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m) →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n) →
      (∑ a ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - 1 := by
  intro π N hN1 hπ1 hax hsweepstep hbase htop htel hax1
  have hstep : ∀ a : ℕ, 1 ≤ a → a ≤ N → (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a ∧ a < n), (1:ℚ)/(n:ℚ)) - (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a-1 ∧ a-1 < n), (1:ℚ)/(n:ℚ)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha1 haN => by have hK : a - 1 + 1 ≤ N := (by omega); have hstep' := hsweepstep π N (a-1) hπ1 hax hK; have haeq : a - 1 + 1 = a := (by omega); rw [haeq] at hstep'; have hcast : ((a-1:ℕ):ℚ) + 1 = (a:ℚ) := (by rw [Nat.cast_sub ha1]; ring); rw [hcast] at hstep'; linarith [hstep']
  have htelapp := htel (fun K => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ)) 0 N (by omega)
  have hrw : ∀ a ∈ Finset.Ioc 0 N, ((fun K => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ)) a - (fun K => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ)) (a-1)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha => hstep a (Finset.mem_Ioc.mp ha).1 (Finset.mem_Ioc.mp ha).2
  rw [Finset.sum_congr rfl hrw] at htelapp
  have hS0 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ 0 ∧ 0 < n), (1:ℚ)/(n:ℚ)) = 1 := by rw [hbase π N hN1 hπ1 hax1]; simp
  have hSN : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ N ∧ N < n), (1:ℚ)/(n:ℚ)) = 0 := by rw [htop π N]; simp
  rw [hS0, hSN] at htelapp
  have hsplit : (∑ a ∈ Finset.Ioc 0 N, ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ))) = (∑ a ∈ Finset.Ioc 0 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (∑ a ∈ Finset.Ioc 0 N, (1:ℚ)/(a:ℚ)) := by rw [Finset.sum_sub_distrib]
  rw [hsplit] at htelapp
  have hIocEqIcc : Finset.Ioc 0 N = Finset.Icc 1 N := by ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIocEqIcc] at htelapp
  linarith [htelapp]

end Erdos858
