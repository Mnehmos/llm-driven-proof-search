-- Exported from the tracked ledger (proof_export format=lean, episode
-- 844e5846-fc4b-4651-b1dd-9e0735a643ce) — the EXACT module the verifier checked.
-- Statement = exists_finset_sum_two_pow from
-- google-deepmind/formal-conjectures FormalConjectures/ErdosProblems/349.lean,
-- hash 2328323a2b3bbeba5fa2318fbc84fd47675231f738edc38166e21687ced920ed.
-- See ../whitepaper.md for the proof idea and ../evidence.md for the full record.
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (k : ℕ), ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := by
  intro k
  exact ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩
