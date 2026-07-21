import Mathlib

/-!
# Erdős #647 — rung5-rung7 coprimality (first factor non-reuse theorem)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16, after 6 kernel_fail iterations
(all on the same symptom — see the Lean lesson below).

  problem_version_id  70b88b83-6ac4-480f-b906-2b31c0befe47
  episode_id          227e1560-c30a-41f3-904e-91716252a014
  outcome             kernel_verified (root_proved), 7th tracked attempt
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `gcd(504N-1, 360N-1) = 1` for every `N ≥ 1` — the first genuine
**factor non-reuse theorem** in the cross-shift terminal-leaf incompatibility
program (five-rung gauntlet audit, 2026-07-16). Proof: the sharp Bezout
identity `5·(504N-1) - 7·(360N-1) = 2` (`erdos647_rung5_rung7_relation`, or
here `heq2 : 5·(504N-1) = 7·(360N-1)+2` re-derived inline) shows any common
divisor `g` of the two cofactors divides `2` (via `g∣5·(504N-1)`,
`g∣7·(360N-1)+2` and `Nat.dvd_add_right`); since `504N-1` is odd (`504N` is
even), `g≠2`, forcing `g=1`.

**Consequence**: no prime factor can simultaneously certify both the rung-5
near-prime demand (`τ(504N-1)≤3`) and the rung-7 near-prime demand
(`τ(360N-1)≤4`) — the two low-divisor shapes are arithmetically independent,
not merely independent in the density-heuristic sense. This is the concrete
instance of the general pattern the audit proposes: "for affine forms `aN-1`
and `cN-1`, their gcd divides `|a-c|` after reduction by `gcd(a,c)`" — here
`5,7 = 504/72, 360/72`.

**Lean lesson (CRITICAL, 6 failed submissions before this one)**: a
multi-line `have h : T := by\n  tac1\n  tac2` block silently mis-scoped in
this pipeline's Lean rendering — the diagnostic showed a correctly-typed
inner term being checked against the OUTER theorem's goal instead of the
`have`'s own goal, with the *identical* "unsolved goals" report persisting
across three different internal-tactic rewrites of the same block. The fix:
eliminate the nested tactic block entirely in favor of pure TERM-mode
`have`s (`heq ▸ h` for transport, `.mp`/`.mpr` for iffs) or single-line
`:= by tac1; tac2` — never a multi-line indented `by` body for a `have`.
`Nat.dvd_sub`'s exact conclusion order was never resolved (its 2-explicit-arg
unconditional form `(h1 : k∣m) → (h2 : k∣n) → k∣(m-n)` typechecks, but
downstream `rw`/`exact` against it kept failing) — abandoned in favor of the
addition-form workaround (`Nat.dvd_add_right`), which has no truncation
ambiguity and is the more robust tool for this shape of argument in ℕ.
-/

theorem erdos647_rung5_rung7_coprime :
    ∀ N : ℕ, 1 ≤ N → Nat.Coprime (504 * N - 1) (360 * N - 1) := by
  intro N hN
  set A := 504 * N - 1 with hA
  set C := 360 * N - 1 with hC
  have heq2 : 5 * A = 7 * C + 2 := by rw [hA, hC]; omega
  have hgA : Nat.gcd A C ∣ A := Nat.gcd_dvd_left A C
  have hgC : Nat.gcd A C ∣ C := Nat.gcd_dvd_right A C
  have hg5A : Nat.gcd A C ∣ 5 * A := Dvd.dvd.mul_left hgA 5
  have hg7C : Nat.gcd A C ∣ 7 * C := Dvd.dvd.mul_left hgC 7
  have hg5A' : Nat.gcd A C ∣ 7 * C + 2 := heq2 ▸ hg5A
  have hg2 : Nat.gcd A C ∣ 2 := (Nat.dvd_add_right hg7C).mp hg5A'
  have hAodd : ¬ (2:ℕ) ∣ A := by rw [hA]; intro hdvd; obtain ⟨c, hc⟩ := hdvd; omega
  have hgor : Nat.gcd A C = 1 ∨ Nat.gcd A C = 2 := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hg2
  rcases hgor with h1 | h2
  · exact h1
  · exact absurd (h2 ▸ hgA) hAodd
