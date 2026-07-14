import Mathlib

/-!
# Erdős #647 — Layer C: support construction validation (product-of-forms map is injective)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  e6331aab-874d-4395-a757-666bcb7e2b13
  episode_id          a3cfd290-eb35-4e8f-b557-f9fa6e1c0c4a
  root_statement_hash 683ca859e07a5245e4f5bd2863e3f684f2ec86d051376c80700001424091e5d5
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `BoundingSieve`'s sieve variable must be `n := ∏ᵢ formᵢ(N)` (the
PRODUCT of the seven forms `{210N-1,...,2520N-1}` at each `N`), not `N`
itself — this is what makes `d ∣ n ⟺ d divides some form` for
squarefree/prime `d`, matching the previously-defined `ν(d)`. This
theorem validates that construction: the map `N ↦ ∏ᵢ formᵢ(N)` is
injective on `[1,X]` (each factor strictly increases in `N` and is
positive there, via `gcongr`, so the product is strictly monotonic and
hence injective), so `support := (Finset.Icc 1 X).image (...)` has card
EXACTLY `X` — no collisions, `totalMass = X` cleanly.

Two Lean fixes: (1) `positivity` cannot handle Nat-truncated-subtraction
positivity facts like `0 < 315*N-1` — `omega` (which has `N≥1` in
context) handles them directly; (2) a stray missing `have` keyword
(`injOn : ... := by` instead of `have injOn : ... := by`) caused a parse
error, since without `have` Lean tries to read `injOn` as an identifier
reference rather than a new binding.
-/

theorem erdos647_support_injective :
    ∀ (X : ℕ), ((Finset.Icc 1 X).image (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))).card = X := by
  intro X
  have hmono : ∀ N1 N2 : ℕ, 1 ≤ N1 → N1 < N2 →
      (210*N1-1)*(315*N1-1)*(420*N1-1)*(630*N1-1)*(840*N1-1)*(1260*N1-1)*(2520*N1-1) <
      (210*N2-1)*(315*N2-1)*(420*N2-1)*(630*N2-1)*(840*N2-1)*(1260*N2-1)*(2520*N2-1) := by
    intro N1 N2 h1 h2
    gcongr <;> omega
  have injOn : Set.InjOn (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)) (Finset.Icc 1 X) := by
    intro N1 hN1 N2 hN2 heq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hN1 hN2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd heq (Nat.ne_of_lt (hmono N1 N2 hN1.1 hlt))
    · exact absurd heq.symm (Nat.ne_of_lt (hmono N2 N1 hN2.1 hgt))
  rw [Finset.card_image_of_injOn injOn, Nat.card_Icc]
  omega
