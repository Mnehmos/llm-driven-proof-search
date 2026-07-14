import Mathlib

/-!
# Erdős #647 — Layer C: residue-class counting LOWER bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  64af298c-bf2a-4f70-8ba4-8b712acdc1f5
  episode_id          2be17ad3-3dcd-4a60-9fe9-4c2957b06251
  root_statement_hash 375e933ad4c6e04d55bd1e004a5c9387b9e75a0ad0bb978fc8d80ee29b4eb323
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: symmetric to `Erdos647_ResidueCountBound.lean`'s upper bound —
for `d>0`, `r<d`, `r≠0`: the number of `N∈[1,X]` with `N≡r (mod d)` is at
least `⌊X/d⌋`. Proven via an EXPLICIT injection `Finset.range(X/d) ↪
filtered set` (`k ↦ r + k·d`), rather than the upper bound's more
abstract `Finset.card_le_card_of_injOn` route — this direction is
naturally phrased as "exhibit enough elements" rather than "no more than
this many."

Combined with the upper bound, this pins `multSum(d)` for the seven-tuple
sieve within a bounded window of the density prediction `ν(d)·X`,
letting `|rem(d)| = |multSum(d) - ν(d)·totalMass|` be bounded for the
already-constructed `BoundingSieve` instance
(`Erdos647_BoundingSieveInstance.lean`).

One Lean fix: initially guessed the wrong lemma name for `(r+k·d)%d=r`
(`omega` also can't close this directly, since it treats the nonlinear
`k·d` term as an opaque atom unrelated to the mod expression) — the
correct name, confirmed via a small standalone diagnostic first, is
`Nat.add_mul_mod_self_right`.
-/

theorem erdos647_residue_count_lower_bound :
    ∀ (d r X : ℕ), 0 < d → r < d → X / d ≤ ((Finset.Icc 1 X).filter (fun N => N % d = r)).card ∨ r = 0 := by
  intro d r X hd hr
  by_cases hr0 : r = 0
  · right; exact hr0
  · left
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hsub : (Finset.range (X/d)).image (fun k => r + k*d) ⊆ (Finset.Icc 1 X).filter (fun N => N % d = r) := by
      intro N hN
      simp only [Finset.mem_image, Finset.mem_range] at hN
      obtain ⟨k, hk, hNeq⟩ := hN
      have hexp : (k+1)*d = k*d + d := by ring
      have h2 : (k+1)*d ≤ X := by
        calc (k+1)*d ≤ (X/d)*d := Nat.mul_le_mul_right d (by omega)
          _ ≤ X := Nat.div_mul_le_self X d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [← hNeq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have hcardimg : ((Finset.range (X/d)).image (fun k => r + k*d)).card = X/d := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range _
      · intro k1 hk1 k2 hk2 heq
        simp only at heq
        have heq' : k1*d = k2*d := by omega
        exact Nat.eq_of_mul_eq_mul_right hd heq'
    calc X/d = ((Finset.range (X/d)).image (fun k => r + k*d)).card := hcardimg.symm
      _ ≤ ((Finset.Icc 1 X).filter (fun N => N % d = r)).card := Finset.card_le_card hsub
