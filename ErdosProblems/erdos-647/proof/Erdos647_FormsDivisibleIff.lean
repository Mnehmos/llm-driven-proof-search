import Mathlib

/-!
# Erdős #647 — Layer C: forms-divisible-iff root-union bridge

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  957fbfea-f283-4f2f-b8c7-06f2f4016679
  episode_id          595511b9-c887-4f79-81fc-b227e02718a3
  root_statement_hash 6c72df181a00ffe6028daff93e0e68b7c340d13f07295a0f3810336ac7fdd21e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the Euclid's-lemma bridge connecting the seven-tuple sieve's
product-of-forms divisibility to the root-union disjunction used to define
`ν`. For a prime `p` and `N ≥ 1`:

  `p ∣ ∏ᵢ formᵢ(N) ↔ ∃ i, formᵢ(N) ≡ 0 (mod p)`

phrased concretely as `p ∣ (210N-1)(315N-1)(420N-1)(630N-1)(840N-1)(1260N-1)(2520N-1)
↔ (210N)%p=1 ∨ (315N)%p=1 ∨ ... ∨ (2520N)%p=1`. This is the key structural
fact letting `multSum(p)` (defined via the actual `BoundingSieve` support —
the product-of-forms image, see `Erdos647_SupportInjective.lean` and
`Erdos647_BoundingSieveInstance.lean`) be computed via the same root-union
residue set already used to define `ν(p)` in `Erdos647_NuAdmissible.lean`:
`multSum(p) = |{N ∈ [1,z] : N mod p is in the root-union set}|`, letting the
`Erdos647_ResidueCountBound.lean` / `Erdos647_ResidueCountLowerBound.lean`
per-residue floor-counting bounds be summed into the `rem(p)` bound needed
for the Selberg sieve's `errSum`.

Proof technique: a helper `key : ∀ c, 0 < c*N → (p ∣ c*N-1 ↔ (c*N)%p=1)`,
proven via `Nat.div_add_mod` bookkeeping (existence direction) and the
`(r+k*d)%d=r` identity (`Nat.add_mul_mod_self_right`, after reassociating
`p*k+1` to `1+k*p` via `ring`) for the reverse direction — avoiding Nat
truncated-subtraction pitfalls entirely by working with `%` instead of
constructing an explicit inverse. The main equivalence is then a 6-deep
nested nested `Nat.Prime.dvd_mul` (Euclid's lemma) case split across the
7-factor product, applying `key` at each of the seven leaves.

Two Lean transport-format bugs fixed (both process, not math — the
underlying tactic proof had already `kernel_pass`'d once via the untracked
`verification.submit` diagnostic pipeline before this tracked submission):
(1) `episode_step`'s `solve` action defaults `proof_format` to
`flat_tactic_sequence`, which re-bases/collapses nesting and destroys
proofs that rely on focus bullets (`·`) or nested `by` blocks — any such
proof must explicitly pass `proof_format: "raw_lean_block"`. (2) even with
`raw_lean_block`, sibling tactics in the *same* outer tactic sequence
(`intro`, `have key`, `constructor`) must all sit at the *same* column —
`raw_lean_block` only strips the common left margin and preserves relative
indentation, it does not re-align siblings, so an accidentally-deeper
`have key := by` line reads as opening a new nested block and orphans
everything after it as a top-level parse error.
-/

theorem erdos647_forms_divisible_iff :
    ∀ (p N : ℕ), p.Prime → 1 ≤ N →
      (p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1) ↔
        ((210*N)%p=1 ∨ (315*N)%p=1 ∨ (420*N)%p=1 ∨ (630*N)%p=1 ∨ (840*N)%p=1 ∨
          (1260*N)%p=1 ∨ (2520*N)%p=1)) := by
  intro p N hp hN
  have key : ∀ c : ℕ, 0 < c*N → (p ∣ c*N-1 ↔ (c*N)%p=1) := by
    intro c hcN
    constructor
    · intro hdvd
      obtain ⟨k, hk⟩ := hdvd
      have h1 : c*N = p*k+1 := by omega
      have h2 : p*k+1 = 1+k*p := by ring
      rw [h1, h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.one_lt]
    · intro hmod
      have h1 : c*N = p*(c*N/p) + (c*N)%p := (Nat.div_add_mod (c*N) p).symm
      rw [hmod] at h1
      exact ⟨c*N/p, by omega⟩
  constructor
  · intro hdvd
    rw [hp.prime.dvd_mul] at hdvd
    rcases hdvd with hd | hd
    · rw [hp.prime.dvd_mul] at hd
      rcases hd with hd | hd
      · rw [hp.prime.dvd_mul] at hd
        rcases hd with hd | hd
        · rw [hp.prime.dvd_mul] at hd
          rcases hd with hd | hd
          · rw [hp.prime.dvd_mul] at hd
            rcases hd with hd | hd
            · rw [hp.prime.dvd_mul] at hd
              rcases hd with hd | hd
              · left; exact (key 210 (by omega)).mp hd
              · right;left; exact (key 315 (by omega)).mp hd
            · right;right;left; exact (key 420 (by omega)).mp hd
          · right;right;right;left; exact (key 630 (by omega)).mp hd
        · right;right;right;right;left; exact (key 840 (by omega)).mp hd
      · right;right;right;right;right;left; exact (key 1260 (by omega)).mp hd
    · right;right;right;right;right;right; exact (key 2520 (by omega)).mp hd
  · intro h
    rcases h with h|h|h|h|h|h|h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((key 210 (by omega)).mpr h) _) _) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 315 (by omega)).mpr h) _) _) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 420 (by omega)).mpr h) _) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 630 (by omega)).mpr h) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 840 (by omega)).mpr h) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 1260 (by omega)).mpr h) _) _
    · exact Dvd.dvd.mul_left ((key 2520 (by omega)).mpr h) _
