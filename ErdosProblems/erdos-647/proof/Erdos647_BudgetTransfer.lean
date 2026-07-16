import Mathlib

/-!
# Erdős #647 — generic gcd-factorization / budget-transfer theorem (theory run, priority 1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  4d4d4991-bc9a-4565-b860-f25f9094cbdd
  episode_id          11da654b-0a1e-4978-bd84-ea57bcf12f1a
  root_statement_hash b794b95a0ef630f76ee861235917a5972e9318bd6dcd4b012d5961aab3a1af76
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     8a1e434b-5050-4406-a67c-8c0e1306b972 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the single generic engine behind every ladder-rung demand. If a
shifted value `n−k` peels as `f·m` with `gcd(f,m)=1`, the excess-`B`
divisor budget transfers to the cofactor:

  `σ₀(f)·σ₀(m) ≤ B+k`  and hence  `σ₀(m) ≤ (B+k)/σ₀(f)`.

B-parametric by design (main declaration is `B = 2`; any B-uniform
consequence serves the limit declaration). Instantiations: rung 5
(`f = 5` or `25`), rung 7 (`f = 7^{a+1}`), rung 9 (`f = 9`), rung 10
(`f = 10`), and every future independent low-divisor rung below `2√n`
identified by the growing-gauntlet criterion.
-/

theorem erdos647_budget_transfer :
    ∀ (n k f m B : ℕ), 0 < f → 0 < m → n - k = f * m → Nat.Coprime f m →
      ArithmeticFunction.sigma 0 (n - k) ≤ B + k →
      ArithmeticFunction.sigma 0 f * ArithmeticFunction.sigma 0 m ≤ B + k ∧
      ArithmeticFunction.sigma 0 m ≤ (B + k) / ArithmeticFunction.sigma 0 f := by
  intro n k f m B hf hm heq hcop hbud
  have hmul : ArithmeticFunction.sigma 0 (n - k) =
      ArithmeticFunction.sigma 0 f * ArithmeticFunction.sigma 0 m := by
    rw [heq]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul] at hbud
  have htf : 0 < ArithmeticFunction.sigma 0 f := by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_pos.mpr ⟨f, Nat.mem_divisors_self f hf.ne'⟩
  refine ⟨hbud, ?_⟩
  rw [Nat.le_div_iff_mul_le htf]
  calc ArithmeticFunction.sigma 0 m * ArithmeticFunction.sigma 0 f
      = ArithmeticFunction.sigma 0 f * ArithmeticFunction.sigma 0 m := by ring
    _ ≤ B + k := hbud
