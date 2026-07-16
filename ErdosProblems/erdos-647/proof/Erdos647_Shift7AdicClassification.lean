import Mathlib

/-!
# Erdős #647 — B-parametric shift-7 adic classification (theory run, priority 2)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  0850b9a6-717d-469d-8d88-11ad4aa00e09
  episode_id          9b42e22a-b2b9-42bd-9bc2-b8a94848c867
  root_statement_hash 525f602193bb55df29b58d47ea5d1e05d6698115f18570e1075c3d603278b607
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     3032e6fa-e6cc-44d2-80bd-72b3ebadb919 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the one gauntlet rung (k ∈ {5,7,9,10,11}) that had no
kernel-verified classification — and empirically the second-biggest
killer (59% kill rate at k=7, the permissive τ≤4 rung where semiprimes
survive; see `dossiers/sqrt-prefix-failure-audit.md`). From
`2520N−7 = 7·(360N−1)`, writing `360N−1 = 7^a·q` with `7 ∤ q` gives
`τ(2520N−7) = (a+2)·τ(q)`, so the excess-`B` budget forces

  `(a+2)·τ(q) ≤ B+7`.

Main declaration (`B = 2`): `a = 0 → τ(q) ≤ 4`; `a = 1 → τ(q) ≤ 3`;
`a = 2 → τ(q) ≤ 2` (q prime); `a ≥ 3` impossible except at bounded
size. Uniform in `B` by design, serving both the main and limit
declarations, and shaped to match `erdos647_budget_transfer`'s generic
peel with `f = 7^{a+1}`.
-/

theorem erdos647_shift7_adic_classification :
    ∀ (N B : ℕ), 1 ≤ N → ArithmeticFunction.sigma 0 (2520 * N - 7) ≤ B + 7 →
      ∃ a q : ℕ, 360 * N - 1 = 7 ^ a * q ∧ ¬ 7 ∣ q ∧
        (a + 2) * ArithmeticFunction.sigma 0 q ≤ B + 7 := by
  intro N B hN hbud
  have hne : 360 * N - 1 ≠ 0 := by omega
  obtain ⟨a, q, hq7, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne 7 (by norm_num)
  refine ⟨a, q, heq, hq7, ?_⟩
  have hval : 2520 * N - 7 = 7 ^ (a + 1) * q := by
    have h7 : 2520 * N - 7 = 7 * (360 * N - 1) := by omega
    rw [h7, heq, pow_succ]
    ring
  have hcop : Nat.Coprime (7 ^ (a + 1)) q :=
    Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hq7)
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ (a + 1)) = a + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map,
      Finset.card_range]
  have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 7) =
      (a + 2) * ArithmeticFunction.sigma 0 q := by
    rw [hval, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs7]
  rw [hsigma] at hbud
  exact hbud
