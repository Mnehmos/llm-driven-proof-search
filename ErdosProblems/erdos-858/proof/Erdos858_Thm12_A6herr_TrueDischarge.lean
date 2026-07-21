/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 herr TRUE discharge (Chojecki 2026).

`A6 herr TRUE discharge`: bridges `#174`'s mass-normalized aggregation output to
the ACTUAL `herr` hypothesis the A6 capstone (`#160`) needs. `#174` produces
`∀η,∀ᶠK,∀N,|A_N−W_KN|≤η·mass_N` (mass-normalized, all-`N`); `#160` wants
`∀ε,∀ᶠK,∀ᶠN,|A_N−W_KN|≤ε` (bare, eventual-`N`). The bridge is the generic
mass-normalized-to-bare-eventual engine (`#140`) plus the total-mass limit
`Σ_{a∈(⌊N^s⌋,⌊N^t⌋]}1/a / log N → t−s`, derived here from the interval harmonic
mass limit (`#99`) and the harmonic-diff identity.

Proof: `Σ1/a = harmonic⌊N^t⌋−harmonic⌊N^s⌋` eventually (for `N>1`, where
`⌊N^s⌋≤⌊N^t⌋` by `Nat.floor_mono`+`Real.rpow_le_rpow_of_exponent_le`); transport
`#99` at `(t,s)` along this eventual equality (`Tendsto.congr'`) to get the mass
limit; apply `#140` directly.

Kernel-verified via the proofsearch MCP:
  episode d7eb1e7c-d758-4e0c-93bd-c6c31ee85fec,
  problem_version_id 208aacc6-d046-4b6d-9f4f-1505b5e8d077.
Outcome: kernel_verified / root_kernel_verified (3rd submission — 1st: `heq.symm`
invalid on a `Filter.Eventually` wrapper [not `Eq`], needs `heq.mono (fun N h =>
h.symm)` to flip the pointwise equality under the eventually; that fix ALSO
surfaced a genuine 2nd bug, not cascading: the `A` function passed to `#140` was
missing its outer `/Real.log N` — only each per-term `f(...)/a` was divided,
not the whole sum — fixed by wrapping `A`'s lambda body in the missing division).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 52d150ad5fad82f53a0477ad6b318d76657b5348b0e53f86caa4a50af20aef39.

**Lean lessons**: (1) `Filter.Eventually` (`∀ᶠ`) is not `Eq` — flipping a
pointwise-equality-under-eventually needs `.mono (fun x h => h.symm)`, not
`.symm` directly (which fails with "Invalid field notation" since the wrapper
type isn't the constant-headed form field projection needs). (2) A type mismatch
diagnostic that *looks* like a paren/beta-reduction display quirk (near-identical
expected/actual with subtly different grouping) can be a REAL structural bug —
here, a missing outer normalization wrapper on one component function — not
merely a rendering artifact of a cascading failure. Always diff the two shown
types term-by-term before assuming "just a display issue."
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 herr TRUE discharge: `#140` (mass-normalized→bare-eventual)
applied with the mass limit derived from `#99`+harmonic-diff, converting `#174`'s
mass-normalized `hAgg` into A6's actual `herr` hypothesis. -/
theorem erdos858_thm12_a6_herr_true :
    ∀ (f : ℝ → ℝ) (s t : ℝ), s ≤ t →
      (∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
        0 ≤ L → Filter.Tendsto mass Filter.atTop (nhds L) →
        (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
      (∀ (x y : ℝ), Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ)^x⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^y⌋₊ : ℝ))/Real.log (N:ℝ)) Filter.atTop (nhds (x - y))) →
      (∀ m n : ℕ, m ≤ n → (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
      (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)|
        ≤ η * ((∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ))) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ (N : ℕ) in Filter.atTop,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε := by
  intro f s t hst h140 h99 hharmdiff hAgg ε hε
  have heq : ∀ᶠ (N:ℕ) in Filter.atTop, (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1:ℝ)/(a:ℝ)) / Real.log (N:ℝ) = ((harmonic ⌊(N:ℝ)^t⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^s⌋₊ : ℝ)) / Real.log (N:ℝ) := by filter_upwards [Filter.eventually_gt_atTop (1:ℕ)] with N hN1; have hNR : (1:ℝ) < (N:ℝ) := (by exact_mod_cast hN1); have hfloormono : ⌊(N:ℝ)^s⌋₊ ≤ ⌊(N:ℝ)^t⌋₊ := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (le_of_lt hNR) hst); rw [hharmdiff ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ hfloormono]
  have heq' : ∀ᶠ (N:ℕ) in Filter.atTop, ((harmonic ⌊(N:ℝ)^t⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^s⌋₊ : ℝ)) / Real.log (N:ℝ) = (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1:ℝ)/(a:ℝ)) / Real.log (N:ℝ) := heq.mono (fun N h => h.symm)
  have hmasslim : Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1:ℝ)/(a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (t - s)) := (h99 t s).congr' heq'
  exact h140 (fun N => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ)/Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) (fun K N => (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)) (fun N => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, (1:ℝ)/(a:ℝ)) / Real.log (N:ℝ)) (t - s) (by linarith) hmasslim hAgg ε hε

end Erdos858
