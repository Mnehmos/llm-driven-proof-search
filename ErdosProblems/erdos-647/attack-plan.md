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
  - ✅ *Part 2b assembly DONE* (kernel-verified, problem `15d4503a`,
    `erdos647_mertens_assembly`, 2026-07-14): combines all six pieces above
    into the full unconditional inequality
    `∀ x≥2, log2·loglog(x) − (1/2 + log2·loglog2 + (1+1/log2)·(1+2√2)) ≤
    ∑_{p≤x} 1/p`. **Layer A (quantitative Mertens) is now fully complete.**
- **Layer B — Selberg optimization step (scoped 2026-07-14, corrected
  target formula).** Mathlib's `mainSum_lambdaSquared_eq_sum_mul_sum_sq`
  diagonalizes `s.mainSum (lambdaSquared w) = ∑_l (selbergTerms l)⁻¹ · y_l²`
  where `y_l := ∑_{d: l∣d} ν(d)·w(d)`. **Corrected target** (the earlier
  note above had the reciprocal backwards): the constrained minimum over
  `w` with `w 1 = 1` is `1 / ∑_l selbergTerms(l)` — NOT
  `1/∑(selbergTerms l)⁻¹`. Derivation: Möbius inversion turns the
  constraint `w 1 = 1` into `∑_l μ(l)·y_l = 1` (via `ν.IsMultiplicative`
  giving `ν 1 = 1`, plus the Möbius indicator identity
  `ArithmeticFunction.coe_moebius_mul_coe_zeta : μ * ζ = 1`); then Sedrakyan
  /Titu/Engel's-form Cauchy–Schwarz, **already in Mathlib** as
  `Finset.sq_sum_div_le_sum_sq_div s f hg : (∑ f i)²/∑ g i ≤ ∑ f i²/g i`
  (`Mathlib.Algebra.Order.BigOperators.Ring.Finset`), applied with
  `f l = μ(l)·y_l`, `g l = selbergTerms l`, gives the universal lower bound
  `1/∑ selbergTerms(l) ≤ mainSum(lambdaSquared w)` for every valid `w`.
  Two remaining pieces: (i) the abstract constrained-Cauchy-Schwarz lemma
  (self-contained, no SelbergSieve dependency — attempted via verification
  tool same session); (ii) the harder half — exhibiting the EXPLICIT
  optimal `w` (via Möbius-inverting `y_l = μ(l)·selbergTerms(l)/∑selbergTerms`
  back to `w`) that achieves equality, needed to actually USE this as an
  upper bound on `siftedSum` (the universal lower bound alone doesn't
  bound anything from above — need one concrete witness).
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
