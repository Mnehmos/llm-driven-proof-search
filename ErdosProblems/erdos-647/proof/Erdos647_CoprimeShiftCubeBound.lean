import Mathlib

/-!
# Erdős #647 — the coprime-shift rough bound (residue-sensitive prefix, step 1)

Snapshot of the exact statement kernel-verified through the tracked
proof-search pipeline on 2026-07-16.

  problem_version_id  60ecdd76-548b-4e11-a886-9536f619b320
  episode_id          5b569b20-4c99-4eb3-b840-f4695bf5c60d
  root_statement_hash 61ee7953d42b5d45652fbc550faab747ac17877893e9853f5e3582028f075405
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     72530007-45be-4db1-babe-dc92d6ce267e (kernel_pass,
                      first try)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the dividend hidden inside the cube proof. For shifts `k`
coprime to 2520, no prime in `{2,3,5,7}` can divide `2520N−k` (any such
prime divides `2520N`, hence would divide `k`, contradicting
`gcd(k,2520)=1`), so the shifted value is 11-rough and the rough core
applies at FULL strength:

  `τ(2520N−k)³ ≤ 2520N−k`  —  prefix constant **1**, not `(1536/35)^{1/3} ≈ 3.53`.

A coprime shift needs checking only while `(k+2)³ < n−k`. This is step 1
of the residue-sensitive cube prefix: the general version assigns each
gcd class `g = gcd(k,2520)` the constant `∏_{p ∣ g} c_p` with
`(c₂,c₃,c₅,c₇) = (8, 3, 8/5, 8/7)`, partitioning shifts by which
small-prime valuations `2520N−k` can actually carry. This benefits the
search, the eventual certificate, and gives the arbitrary-block
production theorem its natural partition by gcd class.

The tracked proof inlines `erdos647_rough_cube_bound` verbatim; this
snapshot states it against the repository theorem for readability. -/

theorem erdos647_coprime_shift_cube_bound :
    ∀ (N k : ℕ), 1 ≤ N → 0 < k → k < 2520 * N → Nat.Coprime k 2520 →
      (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤ 2520 * N - k := by
  intro N k hN hk0 hkn hcop
  have hrough : ∀ p : ℕ, p.Prime → p ∣ 2520 * N - k → 11 ≤ p := by
    intro p hpp hpm
    have hple : p ∣ 2520 → False := by
      intro hp2520
      have hpk : p ∣ k := by
        have h1 : p ∣ 2520 * N := Dvd.dvd.mul_right hp2520 N
        have h2 : p ∣ 2520 * N - (2520 * N - k) := Nat.dvd_sub h1 hpm
        rwa [show 2520 * N - (2520 * N - k) = k from by omega] at h2
      have hg : Nat.gcd k 2520 = 1 := hcop
      have hd : p ∣ Nat.gcd k 2520 := Nat.dvd_gcd hpk hp2520
      rw [hg] at hd
      have := Nat.dvd_one.mp hd
      have := hpp.two_le
      omega
    have h2 := hpp.two_le
    by_contra hlt
    push_neg at hlt
    interval_cases p
    · exact hple (by norm_num)
    · exact hple (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact hple (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact hple (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
  have hpos : 1 ≤ 2520 * N - k := by omega
  exact erdos647_rough_cube_bound (2520 * N - k) hpos hrough
