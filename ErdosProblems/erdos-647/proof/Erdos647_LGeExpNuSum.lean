import Mathlib

/-!
# Erdős #647 — Layer C growth-rate: generic log L ≥ ∑ν(p) bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  d82ea6b1-2e43-49c2-8fac-834c1ffab7fe
  episode_id          09d46e28-6ceb-434e-8bde-c071113ae549
  root_statement_hash c74599d45a83385df1621f8264d5e0fe99a6d056baa4bb0e01a1c4ee455d21bb
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for ANY `s : SelbergSieve`, a generic lower bound on `log L`
(with `L = ∏_{p∈prodPrimes.primeFactors}(1-ν(p))⁻¹`, the Euler-product
closed form from `erdos647_L_eq_prod`) in terms of `∑ν(p)`:

  `∑_{p∈prodPrimes.primeFactors} ν(p) ≤ log(∏_{p∈prodPrimes.primeFactors}(1-ν(p))⁻¹)`

Proof: `Real.log_prod` turns the log of the product into a sum of logs
(needs each factor `(1-ν(p))⁻¹ ≠ 0`, from `ν(p)<1` via `BoundingSieve.
nu_lt_one_of_prime`); then termwise, `Real.log_inv` turns
`log((1-ν(p))⁻¹)` into `-log(1-ν(p))`, and the elementary inequality
`-log(1-x)≥x` for `x∈(0,1)` (from `Real.log_le_sub_one_of_pos` applied
to `y:=1-x>0`, giving `log(1-x)≤(1-x)-1=-x`) closes each term.

Fully generic — NOT tied to any concrete `SelbergSieve` instance — so it
combines directly with `erdos647_nu_sum_ge_seven_mertens` (once
instantiated with this campaign's own concrete seven-tuple construction,
where `prodPrimes.primeFactors` = the admissible primes `≤z`) to get
`log L ≥ 7·loglog(z) − C` for our own `L`, i.e. `L ≥ exp(7·loglog(z)−C) ~
(log z)^7` — the growth rate needed for the final `x/(log x)^7` density
bound (Hughes–Kitamura Theorem 3). No Lean bugs — landed first try on
both the untracked pre-check and the tracked pipeline.
-/

theorem erdos647_L_ge_exp_nu_sum :
    ∀ (s : SelbergSieve), ∑ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ Real.log (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹) := by
  intro s
  rw [Real.log_prod]
  · apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
    have hnu_pos : 0 < s.nu p := s.nu_pos_of_prime p hp_prime hp_dvd
    have hnu_lt1 : s.nu p < 1 := s.nu_lt_one_of_prime p hp_prime hp_dvd
    rw [Real.log_inv]
    have h1mx_pos : 0 < 1 - s.nu p := by linarith
    have hlog := Real.log_le_sub_one_of_pos h1mx_pos
    linarith
  · intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
    have hnu_lt1 : s.nu p < 1 := s.nu_lt_one_of_prime p hp_prime hp_dvd
    have h1mx_pos : 0 < 1 - s.nu p := by linarith
    exact inv_ne_zero h1mx_pos.ne'
