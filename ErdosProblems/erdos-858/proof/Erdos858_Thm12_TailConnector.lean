/-
Erdős Problem #858 — Theorem 1.2 assembly, tail → I connector (Chojecki 2026).

`tail Riemann connector`: the frontier tail converges to the density integral `I`.
Decomposing

  `tail(N) = riemann(N) + swap(N)`

with
  `riemann(N) = (Σ_{K*<a≤√N}(1−Φ(u_a))/a)/log N → I = ∫_{α₂}^{1/2}(1−Φ)`
    (interval log-harmonic transfer A6 at `f = 1−Φ`, limit identified with `∫_s^t f`
     via the affine change of variables), and
  `swap(N) = (Σ (Φ(u_a) − R_N(a))/a)/log N → 0`
    (uniform Lemma 5.5, `R_N → Φ` uniformly over the bounded total mass),

we get `tail(N) → I`. This is the last input of the Theorem 1.2 capstone A7
(`M = harm + tail`, `harm/log N → 1/2`, `tail/log N → I ⟹ M/log N → c₂`), isolating
the two analytic leaves (interval transfer, uniform swap) as the connector's
hypotheses.

Proof: `Tendsto.add` (`riemann + swap → I + 0`), `add_zero`, transported to `tail`
by `funext` on the decomposition.

Kernel-verified via the proofsearch MCP:
  episode 21edb22f-4959-472d-9d2d-5283339f614b,
  problem_version_id 1418d657-61c1-4050-b9d5-802ec9cdec5b.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 21931556496205d22a28149cb8653e33560b044053d41fb470808df359d62976.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 tail connector: `tail = riemann + swap`, `riemann → I`, `swap → 0`
⟹ `tail → I`. Ties the A6 interval transfer (`riemann → I`) and the uniform
Lemma 5.5 (`swap → 0`) to the A7 capstone's tail input. `Tendsto.add`+`add_zero`+`funext`. -/
theorem erdos858_thm12_tail_connector :
    ∀ (tail riemann swap : ℕ → ℝ) (I : ℝ),
      (∀ N : ℕ, tail N = riemann N + swap N) →
      Filter.Tendsto riemann Filter.atTop (nhds I) →
      Filter.Tendsto swap Filter.atTop (nhds 0) →
      Filter.Tendsto tail Filter.atTop (nhds I) := by
  intro tail riemann swap I hdecomp hr hs
  have heq : tail = (fun N => riemann N + swap N) := funext hdecomp
  rw [heq]
  have h := hr.add hs
  rwa [add_zero] at h

end Erdos858
