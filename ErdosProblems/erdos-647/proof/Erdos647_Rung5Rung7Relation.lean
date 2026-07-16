import Mathlib

/-!
# Erdős #647 — rung5-rung7 sharp Bezout identity (five-rung gauntlet)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  94bf7925-d131-45bf-a92c-980ae335dd12
  episode_id          ee02d203-8df1-4e28-9ec6-9d870909f52b
  outcome             kernel_verified (root_proved), first tracked attempt
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the sharp reduced-coefficient coupling between the shift-5 cofactor
`504N-1` and the shift-7 cofactor `360N-1` from the sqrt-prefix failure audit
(`dossiers/sqrt-prefix-failure-audit.md`, 2026-07-16): every sampled survivor of
the shift-{1,2,3,4,6,8,12}-filtered search died at one of the five unfiltered
rungs k∈{5,7,9,10,11}, dominated by k=5 (τ(504N-1)≤3) and k=7 (τ(360N-1)≤4).

  `5·(504N-1) - 7·(360N-1) = 2`

since `5·504 = 7·360 = 2520` cancels the `N` term exactly. This is the reduced
Bezout combination — using multipliers `5,7 = 504/gcd(504,360), 360/gcd(504,360)`
— and is dramatically sharper than the raw-coefficient determinant bound from
`erdos647_affine_determinant_interaction` (which, applied with the forms' own
coefficients 504,360, only gives `gcd | 144`, since `504·(-1) - 360·(-1) = -144`).
Feeds directly into `erdos647_rung5_rung7_coprime`.
-/

theorem erdos647_rung5_rung7_relation :
    ∀ N : ℕ, 1 ≤ N → 5 * (504 * N - 1) - 7 * (360 * N - 1) = 2 := by
  intro N hN
  omega
