/-
Erdős Problem #858 — Theorem 1.2 assembly, CAPSTONE (Chojecki 2026).

`Theorem 1.2 (asymptotic law), conditional capstone`: the Erdős maximum satisfies

  `M(N) / log N  →  c₂ = 1/2 + I`,   `I = ∫_{α₂}^{1/2} (1 − Φ(v)) dv`.

Via the exact frontier identity (Prop 5.1)
  `M(N) = (H_N − H_{⌊√N⌋}) + tail(N)`,  `tail(N) = Σ_{K*<a≤√N} (1 − P_N(a) − Q_N(a))/a`,
and the two normalized limits
  `(H_N − H_{⌊√N⌋}) / log N → 1/2`   (verified atom A1,
    `erdos858_thm12_harmonic_asymptotic`), and
  `tail(N) / log N → I`   (the §5.4 harmonic Riemann sum via #111 at `f = 1 − Φ`;
    `I = ∫_{α₂}^{1/2}(1 − Φ)` is the paper's density integral, `c₂ = 1/2 + I`
    already bracketed `[0.610, 0.633]` by #82–#85),
we conclude `M(N)/log N → 1/2 + I = c₂ = 0.6187712…`.

This is the STRUCTURAL closure of Theorem 1.2 (= paper Theorem 5.8's value
statement), conditional on the frontier identity (Prop 5.1, combinatorial) and the
Riemann-sum limit (from the verified §5.4 transfer #111) — the harmonic half is
discharged (A1). **No sharp-constant Mertens** anywhere: the route is Prop 5.1 +
interval Mertens (#129) + the transfers (#111, #141), exactly as Chojecki's §5.8
proof runs.

Proof: `M(N)/log N = harm(N)/log N + tail(N)/log N` (`add_div`, from the frontier
identity — holds for all `N` including `log N = 0` since `a/0 = 0`), then
`Tendsto.add` gives the limit `1/2 + I`, transported by `Tendsto.congr'`.

Kernel-verified via the proofsearch MCP:
  episode 30d1989f-508d-4858-ae2d-57d6547bd1d2,
  problem_version_id b21ab91d-8c18-4d80-a297-18c25a951566.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 62e1b37347604f085adce9b7ff664ad013fd7d77b8e2cfdcf530d914deed6e88.

Supersedes the thin #69 skeleton by using the actual additive `M = harm + tail`
frontier structure with the harmonic half verified (A1). Remaining input toward
unconditional Theorem 1.2: the `tail/log N → I` Riemann sum (from #111 + Lemma 5.5
= #129/#141 + uniformity) and the frontier localization `K* = N^{α₂+o(1)}` (Prop 5.6
+ Lemma 5.7). See the `erdos-858-thm12-assembly` dossier for the A1–A7 plan.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 (asymptotic law) conditional capstone: from the Prop 5.1 frontier
identity `M = harm + tail` and the normalized limits `harm/log N → 1/2` (A1),
`tail/log N → I`, the maximum satisfies `M(N)/log N → 1/2 + I = c₂`. `Tendsto.add`
over the `add_div` identity. -/
theorem erdos858_thm12_capstone :
    ∀ (M harm tail : ℕ → ℝ) (I : ℝ),
      (∀ N : ℕ, M N = harm N + tail N) →
      Filter.Tendsto (fun N : ℕ => harm N / Real.log N) Filter.atTop (nhds (1/2)) →
      Filter.Tendsto (fun N : ℕ => tail N / Real.log N) Filter.atTop (nhds I) →
      Filter.Tendsto (fun N : ℕ => M N / Real.log N) Filter.atTop (nhds (1/2 + I)) := by
  intro M harm tail I hid hharm hriemann
  have hsum := hharm.add hriemann
  have heq : (fun N : ℕ => harm N / Real.log N + tail N / Real.log N) =ᶠ[Filter.atTop] (fun N : ℕ => M N / Real.log N) := by filter_upwards with N; rw [hid N]; ring
  exact hsum.congr' heq

end Erdos858
