import Mathlib

/-!
# Erdős Problem 349 — binary expansion (`exists_finset_sum_two_pow`)

Independent proof of the `research solved` statement `exists_finset_sum_two_pow` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
`FormalConjectures/ErdosProblems/349.lean`, where it carries a `sorry` plus a
`formal_proof using formal_conjectures` link to an external fork
(cepadugato/formal-conjectures, branch `erdos-349-integer-characterization-proof`).

**Proof.** Mathlib's `Finset.Colex` development (built for the Kruskal–Katona theorem)
already proves the sharper fact needed here: `k.bitIndices.toFinset` — the finset of bit
positions of `k` — sums back to `k` via `2^i` (`Finset.sum_toFinset_bitIndices_two_pow`).
The existential is immediate from that single lemma; no induction needs to be
hand-written. (Locating the exact qualified name took more care than the proof
itself: the lemma sits in `Mathlib/Combinatorics/Colex.lean` under a `section Nat`
that opens *after* `namespace Colex` has already closed with `end Colex` — so the
fully qualified name is `Finset.sum_toFinset_bitIndices_two_pow`, not
`Finset.Colex.sum_toFinset_bitIndices_two_pow` as the file's physical layout first
suggests.)

**Status.** Verified standalone in the pinned toolchain
(lean4:v4.32.0-rc1 + mathlib@360da6fa) via `lake env lean`, independent of the
tracked benchmark ledger (recorded there separately once available).
-/

namespace LeanChecker.Erdos349

theorem exists_finset_sum_two_pow (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩

end LeanChecker.Erdos349
