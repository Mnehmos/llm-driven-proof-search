import Mathlib

/-!
# Erdős #647 — Layer C bridging lemma: multSum = raw filter count

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  3bae0c41-ac9c-4bb5-8844-47e670789d48
  episode_id          690ec042-3cbf-4548-9da4-3cee186c01c0
  root_statement_hash 467cad0fe87078a91660e63cbd05740a3d60b66254b0e22014a28ba2863e8227
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: Mathlib's `BoundingSieve.multSum d := ∑ n ∈ support, if d∣n then
weights n else 0` — for our construction (`support` = image of the
injective product-of-seven-forms map, `weights = 1`) — equals the RAW
filter-count form used throughout `erdos647_rem_bound_squarefree` and
its relatives: `((Finset.Icc 1 X).filter (fun N => d∣∏formᵢ(N))).card`.

Proof: `Finset.sum_image` (using injectivity of the product-of-forms map,
`erdos647_support_injective`'s technique inlined) converts the
sum-over-image into a sum over the domain `Finset.Icc 1 X`; then
`Finset.sum_boole` converts the resulting `∑ N, if d∣∏formᵢ(N) then 1
else 0` into the filtered set's cardinality directly.

This is the connecting piece needed before Mathlib's
`BoundingSieve.multSum`/`rem` machinery (which
`siftedSum_le_mainSum_errSum_of_upperMoebius` operates on) can be shown
to match the concrete combinatorial `rem`/`multSum` bounds this campaign
has built. No Lean bugs — landed first try.
-/

theorem erdos647_multSum_eq_filter_card :
    ∀ (X d : ℕ),
      (∑ n ∈ (Finset.Icc 1 X).image (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)), if d ∣ n then (1:ℝ) else 0)
      = (((Finset.Icc 1 X).filter (fun N => d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ) := by
  intro X d
  have hmono : ∀ N1 N2 : ℕ, 1 ≤ N1 → N1 < N2 →
      (210*N1-1)*(315*N1-1)*(420*N1-1)*(630*N1-1)*(840*N1-1)*(1260*N1-1)*(2520*N1-1) <
      (210*N2-1)*(315*N2-1)*(420*N2-1)*(630*N2-1)*(840*N2-1)*(1260*N2-1)*(2520*N2-1) := by
    intro N1 N2 h1 h2
    gcongr <;> omega
  have hinj : Set.InjOn (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)) (Finset.Icc 1 X) := by
    intro N1 hN1 N2 hN2 heq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hN1 hN2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd heq (Nat.ne_of_lt (hmono N1 N2 hN1.1 hlt))
    · exact absurd heq.symm (Nat.ne_of_lt (hmono N2 N1 hN2.1 hgt))
  rw [Finset.sum_image (fun N1 hN1 N2 hN2 heq => hinj hN1 hN2 heq)]
  rw [Finset.sum_boole]
