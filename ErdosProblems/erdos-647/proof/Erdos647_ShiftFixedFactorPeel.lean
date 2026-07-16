import Mathlib

/-!
# Erdős #647 — the fixed-factor peel formula (theory run, priority 4 foundation)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  279537b6-9bc5-46da-9644-7ca46477288e
  episode_id          4aff3eaa-ab45-474c-ad6e-841e020f022e
  root_statement_hash e354413de288df530ac23de40e221787b6ea3dbe758b243a7ce27f26807132c3
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     e04c9288-4663-44fc-aa2d-6b4d928a614a (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the rung anatomy underlying the growing-gauntlet criterion
(`dossiers/growing-gauntlet-criterion.md`). For any shift `k ≤ 2520`,
with `g = gcd(2520, k)`:

  `2520N − k = g · ((2520/g)·N − k/g)`.

Every ladder rung's cofactor form and fixed factor come from this single
identity: `k=5 → 5·(504N−1)`, `k=7 → 7·(360N−1)`, `k=9 → 9·(280N−1)`,
`k=10 → 10·(252N−1)`, `k=11 → 1·(2520N−11)`, `k=13 → 1·(2520N−13)`.
Combined with `erdos647_budget_transfer` it yields each rung's demand
`τ(cofactor) ≤ (B+k)/τ(fixed)`, and with
`erdos647_affine_determinant_interaction` it decides pairwise
independence of any two rungs' cofactor forms mechanically.
-/

theorem erdos647_shift_fixed_factor_peel :
    ∀ (k N : ℕ), 0 < k → k ≤ 2520 → 1 ≤ N →
      2520 * N - k =
        Nat.gcd 2520 k * ((2520 / Nat.gcd 2520 k) * N - k / Nat.gcd 2520 k) := by
  intro k N hk hk2520 hN
  have hgpos : 0 < Nat.gcd 2520 k := Nat.gcd_pos_of_pos_right 2520 hk
  have h1 : Nat.gcd 2520 k ∣ 2520 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd 2520 k ∣ k := Nat.gcd_dvd_right _ _
  have hc : Nat.gcd 2520 k * (2520 / Nat.gcd 2520 k) = 2520 := Nat.mul_div_cancel' h1
  have hk' : Nat.gcd 2520 k * (k / Nat.gcd 2520 k) = k := Nat.mul_div_cancel' h2
  have hexp : Nat.gcd 2520 k * ((2520 / Nat.gcd 2520 k) * N - k / Nat.gcd 2520 k) =
      Nat.gcd 2520 k * ((2520 / Nat.gcd 2520 k) * N) -
        Nat.gcd 2520 k * (k / Nat.gcd 2520 k) :=
    Nat.mul_sub _ _ _
  rw [hexp, ← mul_assoc, hc, hk']
