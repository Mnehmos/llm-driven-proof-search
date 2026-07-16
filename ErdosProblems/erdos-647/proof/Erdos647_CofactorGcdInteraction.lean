import Mathlib

/-!
# Erdős #647 — cross-shift cofactor gcd interaction (leaf-incompatibility brick 1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  45d4f893-f0d5-4cfb-979e-6c8b91fc8c4e
  episode_id          e1018421-2d8b-46dc-af67-9207b5bbb894
  root_statement_hash 14a462d512e80a1199db32661fc1831b6a05dae060b6781d8d1b4563f859b803
  outcome             kernel_verified (root_proved)
  preverification     398f552a-a901-4ad7-844f-46da79600b24 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the generic interaction lemma for the cross-shift terminal-leaf
incompatibility program. Any common divisor `d` of two affine cofactors
`ca·N−1` and `cb·N−1` divides the coefficient difference `ca−cb`, via the
integer linear combination `cb·(ca·N−1) − ca·(cb·N−1) = ca−cb`.

**Why this matters (computational scout, 2026-07-16, scripts
`F:\tmp\cofactor_scout{,2}.py` — steering evidence, not proof):**
instantiating over the 13 verified divisor-shift cofactor forms
`(2520/k)·N−1`, `k ∈ {1,2,3,4,5,6,8,9,10,12,18,20,24}`, plus the
shift-14/15/16 forms `180N−1`, `168N−1`, `315N−2`:

- Every cofactor pair can share a factor at AT MOST ONE prime, and the
  union of possible shared primes across all pairs is exactly
  `{2, 11, 13, 17, 19, 23}` — precisely the frontier-modulus primes
  (`46189 = 11·13·17·19`), the first refinement tier (23), and parity
  (2, only for the odd-coefficient pair 315/105, both even iff N odd).
  For coefficient chains `ca = m·cb` the bound sharpens to
  `gcd ∣ m−1` (e.g. `gcd(2520N−1, (2520/k)N−1) ∣ k−1`).
- **Structural consequence: on the 41 open frontier classes, pairwise
  cofactor interactions are exhausted.** The open classes are exactly the
  all-avoid region where no frontier prime divides any cofactor, and each
  coefficient already absorbs the 2/3/5/7-adic structure (`c·N−1` is
  coprime to every prime dividing `c`), so on surviving classes the
  cofactors are essentially pairwise coprime, and two forced-prime
  terminal leaves can never share their prime for large `N` (a shared
  prime would divide a small coefficient difference).
- **Route implication**: pairwise leaf algebra cannot close the frontier —
  leaf incompatibility must be ≥3-way, must use the prime-chain family
  constraints (N-parity / s-primality coupling), or must be a
  growing-window counting argument. This also structurally explains WHY
  the frontier primes are 11,13,17,19 (they are the only pairwise
  interaction channels, and the residue sieve spent them) and why the
  shift-16 cross-shift compatibility witness succeeded.

One Lean fix from the first verification attempt: the final ℤ→ℕ
divisibility conversion needs the cast equation staged as its own
`have hcast : ((ca−cb:ℕ):ℤ) = (ca:ℤ)−cb := Nat.cast_sub hcbca` and then
`rw [hcast]` inside a `have` proving `(d:ℤ) ∣ ((ca−cb:ℕ):ℤ)`, rather than
attempting to rewrite the ℕ-goal directly with a cast pattern it does not
syntactically contain.
-/

theorem erdos647_cofactor_gcd_interaction :
    ∀ (ca cb N d : ℕ), 1 ≤ N → 1 ≤ cb → cb ≤ ca →
      d ∣ ca * N - 1 → d ∣ cb * N - 1 → d ∣ ca - cb := by
  intro ca cb N d hN hcb hcbca hda hdb
  have hca1 : 1 ≤ ca * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcb1 : 1 ≤ cb * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdaZ : (d:ℤ) ∣ (ca:ℤ) * N - 1 := by
    have := Int.natCast_dvd_natCast.mpr hda
    rwa [Nat.cast_sub hca1, Nat.cast_mul, Nat.cast_one] at this
  have hdbZ : (d:ℤ) ∣ (cb:ℤ) * N - 1 := by
    have := Int.natCast_dvd_natCast.mpr hdb
    rwa [Nat.cast_sub hcb1, Nat.cast_mul, Nat.cast_one] at this
  have hkey : (d:ℤ) ∣ (ca:ℤ) - cb := by
    have h1 : (d:ℤ) ∣ (cb:ℤ) * ((ca:ℤ) * N - 1) := Dvd.dvd.mul_left hdaZ cb
    have h2 : (d:ℤ) ∣ (ca:ℤ) * ((cb:ℤ) * N - 1) := Dvd.dvd.mul_left hdbZ ca
    have h3 : (d:ℤ) ∣ (cb:ℤ) * ((ca:ℤ) * N - 1) - (ca:ℤ) * ((cb:ℤ) * N - 1) := dvd_sub h1 h2
    have h4 : (cb:ℤ) * ((ca:ℤ) * N - 1) - (ca:ℤ) * ((cb:ℤ) * N - 1) = (ca:ℤ) - cb := by ring
    rwa [h4] at h3
  have hcast : ((ca - cb : ℕ) : ℤ) = (ca : ℤ) - cb := Nat.cast_sub hcbca
  have hfinal : (d:ℤ) ∣ ((ca - cb : ℕ) : ℤ) := by rw [hcast]; exact hkey
  exact Int.natCast_dvd_natCast.mp hfinal
