/-
Erdős Problem #858 — Theorem 1.2 assembly, K* localization (Chojecki 2026).

`frontier maximizer localization`: the frontier cutoff is pinned by the sweep's
monotonicity. If the frontier sum `S = S_N` is strictly increasing on `[1, L1]`
(`S(a−1) < S(a)` for `1 ≤ a ≤ L1`) and strictly decreasing after `L2`
(`S(a) < S(a−1)` for `a > L2`), then any global maximizer `Kmax` (`∀ K, S K ≤ S Kmax`)
satisfies `L1 ≤ Kmax ≤ L2`.

With `L1 = N^{α₂−ε}` (from Lemma 5.7 / the Prop 5.1 increment being `> 0` when
`Φ(u) > 1`, i.e. `u < α₂`) and `L2 = N^{α₂+ε}` (increment `< 0` when `Φ(u) < 1`,
i.e. `u > α₂`), this gives Theorem 5.8's `K*(N) = N^{α₂+o(1)}`.

Proof: if `Kmax < L1`, the increasing step at `a = Kmax+1` gives
`S(Kmax) < S(Kmax+1) ≤ S(Kmax)` (maximality), contradiction; if `Kmax > L2`, the
decreasing step at `a = Kmax` gives `S(Kmax) < S(Kmax−1) ≤ S(Kmax)`, contradiction.
`by_contra` + `push_neg` + the monotone step + `linarith` on the maximality bound.

Kernel-verified via the proofsearch MCP:
  episode bf1b0918-0bbc-4a2f-97e7-9c50b2bdb395,
  problem_version_id 61f22a0b-fc62-4fb5-939c-0bcaa141d242.
Outcome: kernel_verified / root_kernel_verified (2nd submission; multi-line `·`
bullets mis-scope — single-line each).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 476a9a960cc3adbe3154c40fb25bea57e0bb90a889418f5beed6c3980f34e92d.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 K* localization: an increase-then-decrease sweep pins its maximizer
in `[L1, L2]` — with `L1=N^{α₂−ε}`, `L2=N^{α₂+ε}`, `K*(N)=N^{α₂+o(1)}`. `by_contra`
+ monotone step + maximality. -/
theorem erdos858_thm12_kstar_localization :
    ∀ (S : ℕ → ℝ) (L1 L2 Kmax : ℕ),
      (∀ a : ℕ, 1 ≤ a → a ≤ L1 → S (a-1) < S a) →
      (∀ a : ℕ, L2 < a → S a < S (a-1)) →
      (∀ K : ℕ, S K ≤ S Kmax) →
      L1 ≤ Kmax ∧ Kmax ≤ L2 := by
  intro S L1 L2 Kmax hinc hdec hmax
  refine ⟨?_, ?_⟩
  · by_contra h; push_neg at h; have hstep := hinc (Kmax+1) (Nat.le_add_left 1 Kmax) h; simp only [Nat.add_sub_cancel] at hstep; linarith [hmax (Kmax+1), hstep]
  · by_contra h; push_neg at h; linarith [hmax (Kmax-1), hdec Kmax h]

end Erdos858
