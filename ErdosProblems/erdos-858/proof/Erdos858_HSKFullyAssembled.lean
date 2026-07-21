/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED hSK (Chojecki 2026).

Reduces A2's `hSK` hypothesis footprint to just the basic π-structure axioms
(`π 1=0`, the range/order axiom `∀n,2≤n→n≤N→1≤πn∧πn<n`) plus FOUR
already-unconditionally-proven infrastructure theorems — taken as opaque
hypotheses representing their FULL theorems (not re-derived): `frontier_sweep_step`
(`Erdos858_FrontierSweepStep.lean`), `frontier_base_zero`
(`Erdos858_FrontierBaseZero.lean`), `erdos858_frontier_top_zero`
(`Erdos858_FrontierTopZero.lean`), `erdos858_telescoping_Q`
(`Erdos858_TelescopingQ.lean`) — instead of needing the separate
`erdos858_parent_counting` conclusion as an extra opaque hypothesis.

**Key realization**: `frontier_sweep_step` and `frontier_base_zero` need
ONLY `π 1=0`+the range axiom (NO `⪯`/soundness/maximality machinery at
all), and `erdos858_frontier_top_zero`+`erdos858_telescoping_Q` are PURE
combinatorics with ZERO π-dependency. So this atom's hypothesis list is
just 8 items total — far smaller than the 30-50+ feared when "master
composition" was conflated with "re-derive everything from primitive
axioms." The trick: take PRIOR PROVEN THEOREMS as opaque hypotheses and
*apply* them (not re-derive their proofs).

Proof: derives `hparent` (the parent-counting capstone) INLINE via
`erdos858_parent_counting`'s exact proof body (`Erdos858_ParentCounting.lean`),
then chains directly into `erdos858_hSK_general`'s exact proof body
(`Erdos858_HSKGeneral.lean`) using that freshly-derived `hparent`, then
casts to ℝ via the standard `congrArg`+`push_cast` pattern. Both source
proof bodies were already independently verified this session; splicing
them together (with harmless `have`-name shadowing between the two blocks
— `hstep`/`htelapp`/`hrw`/`hS0` are reused names, safely shadowed) worked
on the FIRST submission.

Kernel-verified via the proofsearch MCP:
  episode baf7e671-32e0-4ac2-99f6-0e69ed57bad8,
  problem_version_id 789711f4-6000-46ff-b955-172afe00a6f2.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5ee2c97d333fa78a2e9602084f2a427c90e380910a983d5fd86e954f70966c7e.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled hSK: `S_N(K)=H_N−H_K−Σ_{K<a≤N}C_N(a)` in ℝ, needing only
`π 1=0` + the range axiom + the four opaque infrastructure theorems
(sweep-step, base-zero, top-zero, telescoping) — NOT the separate
parent-counting conclusion. Derives parent-counting inline. -/
theorem erdos858_hSK_fully_assembled :
    ∀ (π : ℕ → ℕ) (N K : ℕ), K ≤ N → 1 ≤ N → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ (π' : ℕ → ℕ) (N' K' : ℕ), π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) → K' + 1 ≤ N' →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' + 1 ∧ K' + 1 < n), (1:ℚ)/(n:ℚ))
          = (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ))
            + ((∑ n ∈ (Finset.Icc 1 N').filter (fun m => π' m = K' + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K':ℚ) + 1))) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), 1 ≤ N' → π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n) →
        (Finset.Icc 1 N').filter (fun n => π' n ≤ 0 ∧ 0 < n) = {1}) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), (Finset.Icc 1 N').filter (fun n => π' n ≤ N' ∧ N' < n) = ∅) →
      (∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n → ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℝ)/(n:ℝ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - (∑ n ∈ Finset.Icc 1 K, (1:ℝ)/(n:ℝ))
          - (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℝ)/(n:ℝ))) := by
  intro π N K hKN hN1 hπ1 hax hsweepstep hbase htop htel
  have hparent : (∑ a ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - 1 := (by
    have hstepA : ∀ a : ℕ, 1 ≤ a → a ≤ N → (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a ∧ a < n), (1:ℚ)/(n:ℚ)) - (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a-1 ∧ a-1 < n), (1:ℚ)/(n:ℚ)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha1 haN => by have hK : a - 1 + 1 ≤ N := (by omega); have hstep' := hsweepstep π N (a-1) hπ1 hax hK; have haeq : a - 1 + 1 = a := (by omega); rw [haeq] at hstep'; have hcast : ((a-1:ℕ):ℚ) + 1 = (a:ℚ) := (by rw [Nat.cast_sub ha1]; ring); rw [hcast] at hstep'; linarith [hstep']
    have htelappA := htel (fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) 0 N (by omega)
    have hrwA : ∀ a ∈ Finset.Ioc 0 N, ((fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) a - (fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) (a-1)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha => hstepA a (Finset.mem_Ioc.mp ha).1 (Finset.mem_Ioc.mp ha).2
    rw [Finset.sum_congr rfl hrwA] at htelappA
    have hS0A : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ 0 ∧ 0 < n), (1:ℚ)/(n:ℚ)) = 1 := by rw [hbase π N hN1 hπ1 (fun n hn2 hnN => (hax n hn2 hnN).1)]; simp
    have hSNA : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ N ∧ N < n), (1:ℚ)/(n:ℚ)) = 0 := by rw [htop π N]; simp
    rw [hS0A, hSNA] at htelappA
    have hsplitA : (∑ a ∈ Finset.Ioc 0 N, ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ))) = (∑ a ∈ Finset.Ioc 0 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (∑ a ∈ Finset.Ioc 0 N, (1:ℚ)/(a:ℚ)) := by rw [Finset.sum_sub_distrib]
    rw [hsplitA] at htelappA
    have hIocEqIccA : Finset.Ioc 0 N = Finset.Icc 1 N := by ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIocEqIccA] at htelappA
    linarith [htelappA])
  have hstep : ∀ a : ℕ, 1 ≤ a → a ≤ N → (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a ∧ a < n), (1:ℚ)/(n:ℚ)) - (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ a-1 ∧ a-1 < n), (1:ℚ)/(n:ℚ)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha1 haN => by have hKa : a - 1 + 1 ≤ N := (by omega); have hstep' := hsweepstep π N (a-1) hπ1 hax hKa; have haeq : a - 1 + 1 = a := (by omega); rw [haeq] at hstep'; have hcast : ((a-1:ℕ):ℚ) + 1 = (a:ℚ) := (by rw [Nat.cast_sub ha1]; ring); rw [hcast] at hstep'; linarith [hstep']
  have htelapp := htel (fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) 0 K (by omega)
  have hrw : ∀ a ∈ Finset.Ioc 0 K, ((fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) a - (fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ)) (a-1)) = (∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ) := fun a ha => hstep a (Finset.mem_Ioc.mp ha).1 (by have hle := (Finset.mem_Ioc.mp ha).2; omega)
  rw [Finset.sum_congr rfl hrw] at htelapp
  have hS0 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ 0 ∧ 0 < n), (1:ℚ)/(n:ℚ)) = 1 := by rw [hbase π N hN1 hπ1 (fun n hn2 hnN => (hax n hn2 hnN).1)]; simp
  rw [hS0] at htelapp
  have hsplit2 : (∑ a ∈ Finset.Ioc 0 K, ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (1:ℚ)/(a:ℚ))) = (∑ a ∈ Finset.Ioc 0 K, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) - (∑ a ∈ Finset.Ioc 0 K, (1:ℚ)/(a:ℚ)) := by rw [Finset.sum_sub_distrib]
  rw [hsplit2] at htelapp
  have hIocEqIccK : Finset.Ioc 0 K = Finset.Icc 1 K := by ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIocEqIccK] at htelapp
  have hIocEqIccN : Finset.Ioc 0 N = Finset.Icc 1 N := by ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hparentIoc : (∑ a ∈ Finset.Ioc 0 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - 1 := by rw [hIocEqIccN]; exact hparent
  have hconsec : (∑ a ∈ Finset.Ioc 0 K, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) + (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) = ∑ a ∈ Finset.Ioc 0 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ) := Finset.sum_Ioc_consecutive (fun a => ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) (Nat.zero_le K) hKN
  rw [hparentIoc] at hconsec
  rw [hIocEqIccK] at hconsec
  have hSK_Q : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ)) = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - (∑ n ∈ Finset.Icc 1 K, (1:ℚ)/(n:ℚ)) - (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) := (by linarith [htelapp, hconsec])
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hSK_Q
  push_cast at hR
  exact hR

end Erdos858
