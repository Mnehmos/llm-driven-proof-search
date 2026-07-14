import Mathlib

/-!
# Erdős #647 — Layer C: the trivial d=1 case of the rem(d) bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  6abde75c-9a06-4d00-bdf8-b7038257ede6
  episode_id          9c5fbf3b-db0c-48c4-971c-9aea1b2a2200
  root_statement_hash af350969b34c717abbd971b3a92c1651c3a634ad3e455256010ce627d1282526
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `erdos647_rem_bound_squarefree` requires `d.primeFactors.Nonempty`,
excluding `d=1` — but `prodPrimes(z).divisors` (the index set
`BoundingSieve.errSum` sums over) always includes `d=1`. This theorem
handles that case directly: since `1 ∣ m` for every `m`, `multSum(1,X) =
X` exactly (the filter is vacuously the whole range), and `ν(1)=1`, so
`rem(1) = multSum(1,X) - ν(1)·X = 0` exactly — contributing `0` to
`errSum` regardless of the weight `muPlus(1)`. Trivial one-line proof via
`Finset.filter_true_of_mem` + `Nat.card_Icc`.
-/

theorem erdos647_rem_bound_one :
    ∀ X : ℕ, (((Finset.Icc 1 X).filter (fun N => (1:ℕ) ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ) - (1:ℝ)/1*X = 0 := by
  intro X
  have heq : (Finset.Icc 1 X).filter (fun N => (1:ℕ) ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)) = Finset.Icc 1 X := by
    apply Finset.filter_true_of_mem
    intro N _
    exact one_dvd _
  rw [heq, Nat.card_Icc]
  simp
