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
- **Layer C — the 7-tuple application. IN PROGRESS, own independent
  construction confirmed valid (2026-07-14).** Hughes's paper attributes
  the seven-form Theorem's proof to an unpublished companion manuscript
  (`HughesChains`, no arXiv ID) absent from his public repo — no
  ground-truth source exists for his exact construction. This campaign
  built and VERIFIED its own instead, grounded entirely in already-proven
  campaign theorems (Stage 1 `2520|n`, Stage 2 prime-chain families, and
  the prior pure-prime shift-3/6/12 classifications):
  the seven-tuple `{210N-1,315N-1,420N-1,630N-1,840N-1,1260N-1,2520N-1}`
  = `(2520/k)N-1` for `k∈{1,2,3,4,6,8,12}`.
  - **Admissibility, kernel-verified**: `gcd` of all 7 coefficients is
    `105=3·5·7`, so every form is `≡-1 mod {3,5,7}` identically —
    root-union size 0 at those three primes (`erdos647_seventuple_admissible_small_primes`,
    `native_decide`), meaning 3,5,7 are structurally EXCLUDED from the
    sieve's active prime set (`BoundingSieve` requires `ν(p)>0` for
    included primes). At p=2: root-union size exactly 1 (matches Hughes's
    claimed value — the only one that does, since his p=3,5,7 claims of
    2,4,6 don't match this construction and can't, given the gcd fact).
    At every prime p>7: proven UNIFORMLY (not case-by-case) that
    root-union size is between 1 and 7
    (`erdos647_seventuple_admissible_general`, via `ZMod p` field
    inverses for existence + cancellation for uniqueness). Snapshot
    `proof/Erdos647_SevenTupleAdmissibility.lean`.
  - ✅ **ν function DONE (2026-07-14)**: `erdos647_nu_admissible` defines
    `ν := ArithmeticFunction.prodPrimeFactors (fun q => rootUnionCount(q)/q)`
    (always multiplicative for free via Mathlib's constructor) and proves
    `0<ν(p)<1` for every prime `p∉{3,5,7}`, combining both admissibility
    theorems above. This supplies all three `BoundingSieve` `nu`-related
    structure fields. Snapshot `proof/Erdos647_NuAdmissible.lean`. The
    analytic core of Layer C is done.
  - ✅ **THE FULL BoundingSieve INSTANCE IS BUILT (2026-07-14)**:
    `erdos647_boundingSieve_instance` constructs a complete, concrete
    `BoundingSieve` for every level `z`, with `support` = the injective
    product-of-seven-forms map, `prodPrimes` = the squarefree product of
    admissible primes ≤z, `weights=1`, `totalMass=z`, and `ν` fully
    admissible — all six structure fields discharged from this campaign's
    own results. Snapshot `proof/Erdos647_BoundingSieveInstance.lean`.
  - ✅ **Residue counting bounds DONE (2026-07-14)**: both
    `erdos647_residue_count_bound` (upper, `≤ X/d+1`) and
    `erdos647_residue_count_lower_bound` (lower, `≥ X/d` for `r≠0`) are
    kernel-verified. Snapshots `proof/Erdos647_ResidueCountBound.lean`,
    `proof/Erdos647_ResidueCountLowerBound.lean`.
  - ✅ **Forms-divisible-iff bridge DONE (2026-07-14)**:
    `erdos647_forms_divisible_iff` proves `p ∣ ∏formᵢ(N) ↔` (some
    `formᵢ(N)≡0 mod p`), via a 6-deep `Nat.Prime.dvd_mul` (Euclid's lemma)
    case split plus a `key` helper (`p∣c·N-1 ↔ (c·N)%p=1`, via
    `Nat.div_add_mod` bookkeeping). This connects `multSum(p)` (defined via
    the actual product-of-forms support) to the same root-union residue
    set already used to define `ν(p)`, letting the residue-counting bounds
    above be summed into `rem(p)`. Snapshot
    `proof/Erdos647_FormsDivisibleIff.lean`. Two transport-format lessons
    recorded there (episode_step `solve`'s `proof_format` must be
    `raw_lean_block` for bullet-heavy proofs, and even then sibling
    top-level tactics must share one column).
  - ✅ **rem(p) BOUND DONE for prime d (2026-07-14)**: `erdos647_rem_bound`
    proves `|multSum(p,X) - ν(p)·X| ≤ rootUnionCount(p)` for every prime
    `p` and level `X` — the first genuine per-prime `errSum` piece,
    combining the forms-divisible-iff bridge with both residue-counting
    bounds via a disjoint `Finset.biUnion` decomposition. Snapshot
    `proof/Erdos647_RemBound.lean`. Two new Lean lessons recorded there:
    `positivity`/`field_simp`/`simp` can hit max recursion depth when the
    context has `set`-introduced huge local defs (fix: `clear_value` right
    after `set`, forcing later tactics to go through the equation
    hypothesis instead of unfolding); and chained type ascriptions
    `(e : T1 : T2)` are a parse error, not automatic double-casting.
  - **Confirmed by reading Mathlib's `SelbergSieve.lean` source directly**
    (2026-07-14): `BoundingSieve.errSum muPlus := ∑ d ∈ divisors
    prodPrimes, |muPlus d| * |rem d|` — sums over EVERY divisor of
    `prodPrimes(z)`, not just primes, so the composite-`d` extension is
    genuinely required (not an optional refinement) before `errSum` can
    be bounded. `rem d := multSum d - nu d * totalMass` with `multSum d :=
    ∑ n∈support, if d∣n then weights n else 0` — confirms
    `erdos647_rem_bound`'s construction (weights=1, support=image of
    product-of-forms map) matches Mathlib's definition exactly.
  - ✅ **CRT card-product formula DONE (2026-07-14)**: `erdos647_crt_card_two`
    proves, for coprime `p,M` and residue sets `Sp⊆[0,p)`, `T⊆[0,M)`, that
    `|{r<p·M : r%p∈Sp ∧ r%M∈T}| = |Sp|·|T|` exactly — a general CRT
    counting fact (`Finset.card_bij` + `Nat.chineseRemainder` +
    `Nat.modEq_and_modEq_iff_modEq_mul`), the combinatorial engine for
    `rootUnionCount(d)=∏_{p∣d}rootUnionCount(p)` on squarefree `d`.
    Snapshot `proof/Erdos647_CrtCardTwo.lean`.
  - ✅ **Squarefree divisibility characterization DONE (2026-07-14)**:
    `erdos647_squarefree_dvd_iff` proves `d∣m ↔ ∀p∈d.primeFactors, p∣m`
    for squarefree `d` (via Mathlib's `Finset.prod_primes_dvd` +
    `Nat.prod_primeFactors_of_squarefree`). This is the bridge that lets
    `erdos647_forms_divisible_iff` (prime-only) generalize to composite
    squarefree `d`. Snapshot `proof/Erdos647_SquarefreeDvdIff.lean`.
  - ✅ **General n-ary CRT card-product formula DONE (2026-07-14)**:
    `erdos647_crt_card_finset` generalizes `erdos647_crt_card_two` from 2
    moduli to an arbitrary `Finset` of primes — `|{r<∏(t) : ∀p∈t,
    r%p∈S(p)}| = ∏_{p∈t}|S(p)|` — by `Finset.induction_on`, peeling one
    prime at a time and applying the 2-modulus case as the inductive
    step. Kernel-verified FIRST TRY. Snapshot `proof/Erdos647_CrtCardFinset.lean`.
  - ✅ **rem(d) BOUND DONE for composite squarefree d (2026-07-14)**:
    `erdos647_rem_bound_squarefree` generalizes `erdos647_rem_bound` from
    prime `p` to any squarefree `d` with `d.primeFactors.Nonempty` —
    `|multSum(d,X) - ν(d)·X| ≤ rootUnionCount(d)`, kernel-verified FIRST
    TRY on the tracked pipeline (after 3 verification-tool iterations
    fixing a genuine double-mod-layer gap and two harmless-but-erroring
    redundant `simp` calls). This is THE key missing piece before
    `BoundingSieve.errSum` (which sums over EVERY divisor of
    `prodPrimes(z)`) can be bounded — the structural/combinatorial core
    of Layer C's error-term analysis is now complete. Snapshot
    `proof/Erdos647_RemBoundSquarefree.lean`.
  - **Remaining for the final numeric theorem**: sum
    `erdos647_rem_bound_squarefree` (plus the `d=1` trivial case, where
    `rem(1)=0` exactly) over `prodPrimes(z).divisors` weighted by the
    Selberg `λ_d²` structure (`lambdaSquared`, from
    `Mathlib.NumberTheory.SelbergSieve`) to get the actual `errSum` used
    by `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`; this
    needs a bound on `|lambdaSquared w d|` for Layer B's specific optimal
    weight `w` (not yet established — `erdos647_selberg_optimal_weight`
    proves the mainSum value but not a pointwise weight bound); combine
    with Layer B's `erdos647_selberg_optimal_weight` + Layer A's
    `erdos647_mertens_assembly`, choosing an optimal `z=z(x)`, for the
    final `x/(log x)^7`-shaped bound. This remaining step is genuine new
    analytic content (a weight-boundedness argument), not just assembly.
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
