/-
Erdős Problem #858 — Theorem 1.2 assembly, general-K frontier recursion
(Chojecki 2026). Discharges the `hSK` hypothesis of atom A2
(`Erdos858_Thm12_A2_Prop51Identity.lean`) in ℚ, for arbitrary `K ≤ N`
(the parent-counting capstone `erdos858_parent_counting` only gives the
fixed top case `K=N`).

`S_N(K) = H_N − H_K − Σ_{K<a≤N} C_N(a)`, for any `0 ≤ K ≤ N`, where
`S_N(K) := Σ_{n≤N: π n≤K<n} 1/n`, `C_N(a) := Σ_{n≤N: π n=a} 1/n`,
`H_m := Σ_{n=1}^m 1/n`.

Assembled from (all taken as hypotheses, conditional-assembly convention):
  `frontier_sweep_step` (per-K increment `S_N(K+1)=S_N(K)+(C_N(K+1)−1/(K+1))`),
  `frontier_base_zero` (`S_N(0)=1`, as the Finset `{n:π n≤0<n}={1}`),
  `erdos858_telescoping_Q` (ℚ telescoping `S(n)−S(m)=Σ_{Ioc m n}(S a−S(a−1))`),
  `erdos858_parent_counting` (`Σ_{a=1}^N C_N(a)=H_N−1`, the K=N capstone).

Proof: (1) telescope `S_N` over `[0,K]` via `frontier_sweep_step`+
`frontier_base_zero` to get `Σ_{a≤K}C_N(a) − H_K = S_N(K) − 1`; (2) split the
parent-counting capstone `Σ_{a≤N}C_N(a)=H_N−1` at `K` via
`Finset.sum_Ioc_consecutive`; (3) `linarith` combines both into the target
identity. Mirrors `erdos858_parent_counting`'s exact composition template
(`hstep`/`htelapp`/`hrw`/`hS0`/`hsplit`), generalized from the fixed top
`K=N` to arbitrary `K≤N` via one extra `Finset.sum_Ioc_consecutive` split.

Kernel-verified via the proofsearch MCP:
  episode 56bd0e3c-f57c-4e82-88b3-f1a6ae447561,
  problem_version_id 7e2927dd-241a-4180-a897-e16d8e72b5bb.
Outcome: kernel_verified / root_kernel_verified (1st submission — the #180
template generalized cleanly with no new pitfalls).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash e9fcb6beb73fc5597c5f667778fe59bff4bd892558e9dbbce235a14ca8f8bdac.
-/
import Mathlib

namespace Erdos858

/-- General-K frontier recursion: `S_N(K) = H_N−H_K−Σ_{K<a≤N}C_N(a)` for any
`K≤N`, assembled from `frontier_sweep_step`+`frontier_base_zero`+
`erdos858_telescoping_Q`+`erdos858_parent_counting`. Discharges A2's `hSK`
hypothesis in ℚ (the ℚ→ℝ cast is the separate remaining step, via the
`congrArg`+`push_cast` pattern proven in #181/#182). -/
theorem erdos858_hSK_general :
    ∀ (π : ℕ → ℕ) (N K : ℕ), K ≤ N → 1 ≤ N → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ (π' : ℕ → ℕ) (N' K' : ℕ), π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) → K' + 1 ≤ N' →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' + 1 ∧ K' + 1 < n), (1:ℚ)/(n:ℚ))
          = (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ))
            + ((∑ n ∈ (Finset.Icc 1 N').filter (fun m => π' m = K' + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K':ℚ) + 1))) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), 1 ≤ N' → π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n) →
        (Finset.Icc 1 N').filter (fun n => π' n ≤ 0 ∧ 0 < n) = {1}) →
      (∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n → ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m) →
      (∑ a ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - 1 →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - (∑ n ∈ Finset.Icc 1 K, (1:ℚ)/(n:ℚ))
          - (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ)) := by
  intro π N K hKN hN1 hπ1 hax hsweepstep hbase htel hparent
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
  linarith [htelapp, hconsec]

end Erdos858
