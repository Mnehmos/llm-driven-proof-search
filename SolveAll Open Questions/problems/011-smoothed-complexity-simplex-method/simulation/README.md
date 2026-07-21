# Simulation layer — smoothed simplex pivot counts

> **NON-RIGOROUS. Simulation evidence only.** This directory proves nothing.
> It is entirely separate from the kernel-verified Lean layer in
> [`../proof/`](../proof/), which is the campaign's only rigorous content. The
> layering convention (rigorous / Monte Carlo / formalization, each labeled by
> what it establishes) mirrors `F:\Github\Benjamini-Hochberg Procedure`.

## What this is

[`smoothed_simplex_pivot_counts.py`](smoothed_simplex_pivot_counts.py) runs the
actual textbook dense primal simplex method (Dantzig entering rule, min-ratio
leaving rule, first-index tie-breaks) on small random LPs under the Gaussian
smoothed perturbation model, and reports the observed pivot count as a function
of `n` (variables), `m` (constraints), and `σ` (noise level). It is meant to
give a concrete, reproducible feel for the phenomenon the Lean layer's
building block (Milestone 1, the Gaussian anti-concentration bound) is one
foundational piece of.

## Honest deviations from the problem's literal setup

These are documented in full in the script's module docstring. In brief:

1. **Not the `Sm_R` supremum.** The problem's `Sm_R(m,n,σ)` is a *sup* over an
   adversarial base instance `(Ā,b̄,c̄)`. This samples *typical* random base
   instances instead (intractable to search the adversarial sup), so it does
   **not** estimate `Sm_R` — only illustrates typical-instance behavior.
2. **Anchored `b̄ = ones(m)` with margin, not folded into the norm ball.**
   Normalizing the whole triple to `‖(Ā,b̄,c̄)‖ ≤ 1` crushes `b̄` to near-zero,
   making the origin infeasible under almost any noise (an artifact of the norm
   ball, not the pivot phenomenon). We normalize `Ā`, `c̄` individually and
   anchor `b̄ = ones(m)` so the origin is feasible with margin 1. This does not
   satisfy `‖(Ā,b̄,c̄)‖ ≤ 1` literally.
3. **Standard-form `x ≥ 0`** (the problem allows a general polyhedron).
4. **No phase-1**; trials where noise makes the origin infeasible (`some
   b_i < 0`) are skipped and counted, not silently dropped. An iteration cap
   catches any non-terminating run and reports it as an anomaly.

## Results (seed 20260717, 200 trials/cell)

Reproduce: `python smoothed_simplex_pivot_counts.py` (writes
`smoothed_simplex_pivot_counts_results.csv`; progress to stderr). Locked deps:
Python 3.12, NumPy 2.2.

| (n, m) | σ=1 | σ=0.3 | σ=0.1 | σ=0.03 | σ=0.01 |
|---|---|---|---|---|---|
| (5, 10)  | 3.11 † | 3.08 | 2.79 | 2.88 | 2.97 |
| (10, 20) | 9.40 † | 7.05 | 7.20 | 7.42 | 7.00 |
| (20, 40) | — ‡ | 17.25 | 20.49 | 23.22 | 22.00 |

Mean pivots per cell. † few feasible trials (noise σ=1 on the margin-1 anchor
makes the origin infeasible in most trials — `n=5`: 37/200 feasible; `n=10`:
5/200). ‡ `n=20, σ=1`: 0/200 feasible (with `m=40` constraints each
`1 + N(0,1)`, `P(all positive) ≈ 2⁻⁴⁰`), honestly reported as no data rather
than fabricated. All well-sampled cells: 0 iteration-cap anomalies.

## What the numbers qualitatively show (and don't)

- Mean pivot count grows **roughly linearly in `n`** (≈3 → ≈7 → ≈21 as
  `n = 5 → 10 → 20`) and is **strikingly stable across `σ`** over two orders
  of magnitude (0.01 → 1 where feasible). That stability is the qualitative
  signature of *mild* smoothed behavior — the phenomenon that motivates the
  whole research program, and consistent with (though in no way a proof of)
  a near-linear-in-`n` pivot count.
- This says **nothing** about the open question, which is about the *worst
  case over adversarial base instances* and the *exact asymptotic order in
  `m, n, σ`* — neither of which a typical-instance simulation at three tiny
  sizes can address. The tail behavior in `σ` (the `σ^{-3/2}` / `σ^{-2}`
  factors in the real upper bounds) only shows up at scales and adversarial
  configurations far beyond this illustrative sweep.
