# Attack plan — Erdős #647 (living)

> Last updated 2026-07-13. This is the working plan of record; it changes as
> results land. Completed milestones move to the whitepaper's campaign log.

## Guiding constraint (proven, not vibes)

The **all-avoid obstruction** (Hughes) and our extension of it to
Theorem-2 chain forms mean: no finite pile of congruence arguments closes
the 41 open residue classes. Progress on the *theorem itself* must come
from analytic estimates (density bounds) or from a genuinely new leaf type
nobody has found yet. Sub-AP/congruence work is therefore frozen except
where a specific new leaf type appears.

## Track 1 — the density-bound program (ACTIVE)

Target: a machine-checked `|C(x)| ≪ x/(log x)⁷` (Hughes–Kitamura Theorem 3),
via Mathlib's Selberg sieve (`Mathlib.NumberTheory.SelbergSieve`).

- **Layer A — quantitative Mertens.**
  - ✅ *Part 1 done* (kernel-verified exact identity, problem `d584666d`):
    `∑_{p≤x} 1/p = θ(x)/(x log x) + ∫_{(2,x]} (log t+1)/(t² log²t)·θ(t) dt`.
  - ✅ *Part 2a done* (kernel-verified main-term antiderivative, problem
    `781d4876`): `∫_2^x (log t+1)/(t log²t) dt = (log log x − 1/log x) −
    (log log 2 − 1/log 2)` — the `θ(t)=t` idealization, carrying the
    double-log growth, via FTC on `F(t) = log log t − 1/log t`.
  - ✅ *Part 2b error bounds done*: both convergent error integrals from
    `Chebyshev.theta_ge` (`θ(t) ≥ (t−1)log 2 − log(t+2) − 2√t·log t`) are
    kernel-verified — `log(t+2)` term (problem `8bf294a3`,
    `erdos647_mertens_error_log`, ≤ `1 + 1/log 2`) and `2√t·log t` term
    (problem `d804be62`, `erdos647_mertens_error_sqrt`, ≤ `2√2(1+1/log 2)`,
    2026-07-13).
  - **Part 2b assembly (next):** combine the four pieces — main-term
    antiderivative (`781d4876`), weight integral (`1fc1ab2d`), and the two
    error bounds above — into the full inequality
    `∑_{p≤x} 1/p ≥ log 2 · log log x − C` with an explicit `C`. This is
    pure bookkeeping (`linarith`/`nlinarith` combination of already-proven
    pieces plus the Part 1 identity), not new analysis.
- **Layer B — Selberg optimization step.** Mathlib diagonalizes the Λ² main
  term (`mainSum_lambdaSquared_eq_sum_mul_sum_sq`) but lacks the classical
  optimal-weight bound `mainSum ≤ 1/∑_{l≤z} (selbergTerms l)⁻¹`. Formalize
  it (Cauchy–Schwarz / completing-the-square on the diagonalized form).
- **Layer C — the 7-tuple application.** Instantiate `BoundingSieve` for
  families A/B (`n=8s+8` / `n=16s+8` with their 7 forms): define ν(p) =
  (residues killed)/p, prove admissibility `0 < ν(p) < 1` (root-union sizes
  1,2,4,6 for p = 2,3,5,7 per Hughes–Kitamura), bound `errSum` by level
  truncation, and combine with Layers A+B for the final bound.
- Fallback if a layer stalls: a weaker exponent (`x/(log x)^k`, k < 7, using
  fewer forms) is still a first-of-its-kind artifact; take the partial win
  and iterate.

## Track 2 — harden the record

- Stand up a local `LeanChecker`-style replay of the [proof/](proof/)
  snapshots (as erdos-291/-1052 have), removing the "environment is the
  only witness" caveat in evidence.md.
- Formalize the **all-avoid obstruction itself** in Lean (currently prose +
  Hughes's markdown). This would make the campaign's central negative
  result machine-checked too, and sharpen exactly which argument classes
  it excludes.

## Track 3 — upstream

- The Mertens work (Layer A) and the Selberg optimization step (Layer B)
  are Mathlib-shaped, problem-independent lemmas. Once stable, prepare
  them for upstream contribution (see `erdos-ecosystem-contribution-path`:
  formal-conjectures / Mathlib PR conventions, CLA gate).

## Parking lot (ideas not currently worth their cost)

- More sub-AP closures / more refinement primes: unbounded grind, cannot
  close the frontier (all-avoid). Only revisit with a new leaf type.
- Witness search below 6.16×10¹⁷: excluded by published computation;
  above it: no feasible strategy — density bounds are the honest
  substitute.
- Shift-7 classification (the one shift outside the clean 13): low value,
  likely no frontier effect.
