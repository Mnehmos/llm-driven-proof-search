import Mathlib

/-!
# Erdős #647 — shift-16 leaf frontier exclusions (Engine A, milestone 5)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  09b7d945-c408-4929-9f80-450db23a3a14
  episode_id          b16a33ea-da54-45a7-9abf-447badd35748
  root_statement_hash f7d36236fd7154ef697b149783f7d6202d3869ab988a7644b39a3bab0bb71f72
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     a2da90f1-77ff-4f07-9d49-613c60a080a3 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the first genuinely new exclusions produced by the determinant
catalog — congruence rows one CRT level BELOW the 41-class frontier, over
forms that never appeared in the original 13-coefficient sieve.

The shift-16 residual classification
(`Erdos647_Shift16ResidualTermination.lean`, kernel-verified) leaves
exactly two prime-producing leaves on the `M % 8 = 3` branch:

- leaf A: `M = 16Q+11`, forced prime `630Q+433`;
- leaf B: `M = 32R+3`, forced prime `630R+59`.

The determinant catalog (`dossiers/tools/det_catalog.py`) shows these
leaf forms interact with the re-parameterized shift cofactors exactly at
the frontier primes `11, 13, 17, 19`. Because both leaves DEMAND
primality, divisibility by a frontier prime at the (unique, since 630 is
invertible mod each) bad residue kills the leaf:

- leaf A is impossible at `Q ≡ 6 (11)`, `8 (13)`, `9 (17)`, `14 (19)`;
- leaf B is impossible at `R ≡ 6 (11)`, `1 (13)`, `9 (17)`, `12 (19)`.

Factor witnesses (each machine-checked before formalization):
`630(11m+6)+433 = 11(630m+383)`, `630(13m+8)+433 = 13(630m+421)`,
`630(17m+9)+433 = 17(630m+359)`, `630(19m+14)+433 = 19(630m+487)`;
`630(11m+6)+59 = 11(630m+349)`, `630(13m+1)+59 = 13(630m+53)`,
`630(17m+9)+59 = 17(630m+337)`, `630(19m+12)+59 = 19(630m+401)`.

Structure-level corollaries (`shift16LeafA_frontier_exclusion`,
`shift16LeafB_frontier_exclusion`, phrased against the budget-parametric
`LeafType` catalog) live in `Erdos647_LeafTypeFramework.lean`, which
compiles from clean source through the pinned lean-checker toolchain.

These exclusions cut 4/11 + 4/13 + 4/17 + 4/19 (minus CRT overlaps) of
each residual branch's parameter space, and every leaf produced by the
shift-factor framework at any depth admits the same treatment — the
per-leaf exclusion generation is mechanical from the determinant catalog.
They are steering toward the compatibility-graph obstruction, not a
closure claim: outside the excluded residues both leaves remain
realizable (the depth-15/16 witnesses prove compatible transversals
exist through the current finite catalog).
-/

theorem erdos647_shift16_leaf_frontier_exclusions :
    ∀ (Q R : ℕ),
      ((Q % 11 = 6 ∨ Q % 13 = 8 ∨ Q % 17 = 9 ∨ Q % 19 = 14) →
        ¬ Nat.Prime (630 * Q + 433)) ∧
      ((R % 11 = 6 ∨ R % 13 = 1 ∨ R % 17 = 9 ∨ R % 19 = 12) →
        ¬ Nat.Prime (630 * R + 59)) := by
  intro Q R
  constructor
  · intro h hp
    have key : ∀ (p : ℕ), 1 < p → p ∣ 630 * Q + 433 → p < 630 * Q + 433 → False := by
      intro p h1 h2 h3
      rcases hp.eq_one_or_self_of_dvd p h2 with h4 | h4 <;> omega
    rcases h with h | h | h | h
    · obtain ⟨m, rfl⟩ : ∃ m, Q = 11 * m + 6 := ⟨Q / 11, by omega⟩
      exact key 11 (by omega) ⟨630 * m + 383, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, Q = 13 * m + 8 := ⟨Q / 13, by omega⟩
      exact key 13 (by omega) ⟨630 * m + 421, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, Q = 17 * m + 9 := ⟨Q / 17, by omega⟩
      exact key 17 (by omega) ⟨630 * m + 359, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, Q = 19 * m + 14 := ⟨Q / 19, by omega⟩
      exact key 19 (by omega) ⟨630 * m + 487, by ring⟩ (by omega)
  · intro h hp
    have key : ∀ (p : ℕ), 1 < p → p ∣ 630 * R + 59 → p < 630 * R + 59 → False := by
      intro p h1 h2 h3
      rcases hp.eq_one_or_self_of_dvd p h2 with h4 | h4 <;> omega
    rcases h with h | h | h | h
    · obtain ⟨m, rfl⟩ : ∃ m, R = 11 * m + 6 := ⟨R / 11, by omega⟩
      exact key 11 (by omega) ⟨630 * m + 349, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, R = 13 * m + 1 := ⟨R / 13, by omega⟩
      exact key 13 (by omega) ⟨630 * m + 53, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, R = 17 * m + 9 := ⟨R / 17, by omega⟩
      exact key 17 (by omega) ⟨630 * m + 337, by ring⟩ (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, R = 19 * m + 12 := ⟨R / 19, by omega⟩
      exact key 19 (by omega) ⟨630 * m + 401, by ring⟩ (by omega)
