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
- ✅ **Layer B COMPLETE (2026-07-14).** Mathlib's
  `mainSum_lambdaSquared_eq_sum_mul_sum_sq` diagonalizes
  `s.mainSum (lambdaSquared w) = ∑_l (selbergTerms l)⁻¹ · y_l²` where
  `y_l := ∑_{d: l∣d} ν(d)·w(d)`. The constrained minimum over `w` with
  `w 1 = 1` is `1 / ∑_l selbergTerms(l)`. Four kernel-verified pieces:
  `erdos647_selberg_engel_bound` (universal lower bound, via Mathlib's
  existing `Finset.sq_sum_div_le_sum_sq_div` Cauchy-Schwarz/Sedrakyan
  lemma), `erdos647_moebius_sum_indicator` + `erdos647_moebius_swap_inversion`
  (Möbius-inversion machinery for sums over multiples in a squarefree
  divisor lattice), and `erdos647_selberg_optimal_weight` (FINAL ASSEMBLY,
  kernel_pass first try): explicitly constructs `w` via Möbius-inverting
  the target `y_l := μ(l)·selbergTerms(l)/∑selbergTerms`, proves `w 1 = 1`,
  and shows `mainSum(lambdaSquared w) = 1/∑selbergTerms` exactly — matching
  the universal lower bound, so this is genuinely the constrained minimum,
  not just an upper bound. Combined with Mathlib's
  `siftedSum_le_mainSum_errSum_of_upperMoebius`, the Selberg sieve bound
  `siftedSum ≤ totalMass/∑selbergTerms + errSum(lambdaSquared w)` is now
  fully available. Snapshots: `proof/Erdos647_SelbergEngelBound.lean`,
  `proof/Erdos647_MoebiusIndicator.lean`,
  `proof/Erdos647_MoebiusSwapInversion.lean`,
  `proof/Erdos647_SelbergOptimalWeight.lean`.
- **Layer C — the 7-tuple application (research finding 2026-07-14: the
  exact 7-tuple is NOT publicly derivable — see below before attempting).**
  Instantiate `BoundingSieve` for families A/B (`n=8s+8` / `n=16s+8` with
  their 7 forms): define ν(p) = (residues killed)/p, prove admissibility
  `0 < ν(p) < 1`, bound `errSum` by level truncation, combine with Layers
  A+B for the final bound.
  - **Blocker**: Hughes's paper attributes the seven-form Theorem's PROOF
    to an unpublished companion manuscript (`HughesChains`), absent from
    his public repo/Lean sources (checked `docs/theorem_map.md` and
    `lean/` — only the unrelated 12-coefficient mod-46189 certificate
    exists there). No ground-truth source for the exact 7 linear forms.
  - **My reconstruction attempt is DISPROVEN — do not reuse.** Naively
    substituting `s=315N-1` (from `2520|n`) into the base forms
    `s,2s+1,4s+3,8s+7` plus adjoined shifts {3,6,12} gives
    `{210N-1,315N-1,420N-1,630N-1,840N-1,1260N-1,2520N-1}` —
    `(2520/k)N-1` for `k∈{1,2,3,4,6,8,12}`. Checked directly: primes
    3,5,7 divide EVERY one of these 7 coefficients (structurally, since
    no `k` in that set shares a factor with 5 or 7), forcing root-union
    size 0 for p=3,5,7 — contradicting the paper's claimed sizes 2,4,6.
    Insight: those claimed sizes equal `min(p-1,7)`, the MAXIMUM possible
    for an admissible 7-tuple — meaning the true construction needs
    N-coefficients that are UNITS mod 2,3,5,7 (opposite of `2520/k`,
    which is built to be divisible by them). Full reasoning in campaign
    memory (`erdos-647-campaign-state.md`).
  - **Next steps**: either locate `HughesChains` via arXiv/other search
    (not yet tried), or independently derive a fresh admissible 7-tuple
    from this campaign's own proven Theorem stage2 forms — genuinely new
    sieve-theoretic design work; spot-check admissibility numerically
    (Python/native_decide) BEFORE any Lean submission attempt.
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
