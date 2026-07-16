import Mathlib

/-!
# Erdős #647 — the cube-root certificate theorem (positive lane, upgraded)

Snapshot of the exact statement kernel-verified through the tracked
proof-search pipeline on 2026-07-16.

  problem_version_id  ff19b364-bbac-4dce-9f23-536b593050d5
  episode_id          dddf41d0-69c1-4241-a968-59f469939b8c
  root_statement_hash ce7d1b543d777698025f627cf03d3cf220285dbf7148cd7dc9592cf846a35844
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     f4d867bf-c261-4829-807f-6d35553fec39 (kernel_pass,
                      first try)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `candidate_of_cube_prefix`. Verifying the shift budgets only on
the CUBE prefix — the shifts `k` with `35·(k+2)³ < 1536·(n−k)`, i.e.
`k ≲ 3.53·n^{1/3}` — certifies the FULL Erdős #647 candidate condition
in the Formal Conjectures supremum form:

  `(∀ k, 0<k → k<n → 35(k+2)³ < 1536(n−k) → σ₀(n−k) ≤ k+2)
     → (⨆ m : Fin n, m + σ₀ m) ≤ n+2`.

Every shift beyond the cube prefix is automatically safe by the sharp
divisor bound `35·τ(n−k)³ ≤ 1536·(n−k) ≤ 35·(k+2)³`
(`erdos647_sharp_cube_divisor_bound`, inlined verbatim in the tracked
proof; equality at 2520 checked numerically, uniqueness not yet a
formal claim), whence `τ(n−k) ≤ k+2` by cube-root
monotonicity.

**Supersedes `erdos647_candidate_of_sqrt_prefix`**: at frontier heights
`n ≈ 6×10¹⁷` the finite `native_decide` obligation for a discovered
survivor shrinks from `2√n ≈ 1.6×10⁹` shifts to `≈ 3×10⁶` shifts — a
~520× reduction. The search decision procedure, the formal certificate,
and the negative lane's obstruction window now all live in an
`O(n^{1/3})` prefix.

The tracked proof = the sharp-bound proof (see
`Erdos647_SharpCubeDivisorBound.lean` for the standalone snapshot and
provenance) + the budget bridge (`by_cases` on the prefix condition,
cube-root monotonicity `Nat.pow_le_pow_iff_left` outside it) + the
`ciSup_le` conversion with the `m = 0` edge (`σ₀(0) = 0`). This snapshot
restates it against the repository theorem for readability. -/

theorem erdos647_candidate_of_cube_prefix :
    ∀ n : ℕ, 0 < n →
      (∀ k : ℕ, 0 < k → k < n → 35 * (k + 2) ^ 3 < 1536 * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hn hpre
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk : 35 * (k + 2) ^ 3 < 1536 * (n - k)
    · exact hpre k hk0 hkn hk
    · push_neg at hk
      have hpos : 1 ≤ n - k := by omega
      have hc := erdos647_sharp_cube_divisor_bound (n - k) hpos
      have hcube : (ArithmeticFunction.sigma 0 (n - k)) ^ 3 ≤ (k + 2) ^ 3 := by omega
      exact (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega
