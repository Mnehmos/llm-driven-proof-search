# Attack plan — Erdős #647 (living)

> Last updated 2026-07-14. This is the working plan of record; it changes as
> results land. Completed milestones move to the whitepaper's campaign log.

## HEADLINE STATUS (2026-07-14)

**Main term solved. Error term structurally unresolved. The desired
`x/(log x)^7` density theorem does NOT yet follow from the verified
bounds.** The main-term growth chain for `L` is complete and solid
(`erdos647_L_eq_prod` + `erdos647_seventuple_rootcount_eq_seven` + `erdos647_nu_eq_seven_div_p`
+ `erdos647_nu_sum_ge_seven_mertens` + `erdos647_L_ge_exp_nu_sum` ⟹
`L≳(log z)^7`). The capstone `erdos647_selberg_sieve_bound_conditional`
is real and kernel-verified, but its `errSum` term is bounded via a
crude pointwise estimate summed over an UNRESTRICTED divisor set —
Mathlib's `SelbergSieve.level` is vestigial (never used to truncate
`lambdaSquared`'s support), so this bound is plausibly exponential in
`π(z)`, reproducing the "Legendre explosion" already ruled out for a
cruder shortcut. **Do not attempt the final numeric assembly until this
is resolved** — see the "⚠⚠ CRITICAL DIAGNOSTIC" bullet under Layer C
below for full detail and the two candidate resolutions.

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
  - ✅ **`d=1` trivial case DONE (2026-07-14)**: `erdos647_rem_bound_one`
    proves `rem(1)=0` exactly (multSum(1,X)=X since `1∣` everything,
    `ν(1)=1`). Snapshot `proof/Erdos647_RemBoundOne.lean`.
  - **Remaining for the final numeric theorem**: sum
    `erdos647_rem_bound_squarefree` (plus `erdos647_rem_bound_one` for
    `d=1`) over `prodPrimes(z).divisors` weighted by the
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
  - ⚠ **Confirmed (2026-07-14): the pure Legendre/Möbius sieve (`muPlus :=
    μ` instead of Selberg's `lambdaSquared w`) is NOT a viable shortcut**,
    despite `|μ(d)|≤1` being trivial. `errSum(μ) ≤
    Σ_{d|prodPrimes(z)}rootUnionCount(d) ≤ 8^π(z)` (since `rootUnionCount`
    is multiplicative, `≤7` at each prime) — EXPONENTIAL in `π(z)`, the
    classical Legendre "combinatorial explosion" that historically forces
    `z=O(log x)` and only an `x/log x`-type bound. Selberg's
    variance-minimized weight is genuinely load-bearing for the `(log
    x)^7` exponent; there is no way to route around its magnitude bound.
  - ✅ **SELBERG WEIGHT MAGNITUDE BOUND DONE (2026-07-14)**:
    `erdos647_selberg_weight_bound` proves `|w(d)| ≤ selbergTerms(d)/ν(d)`
    for Layer B's explicit optimal weight `w` (from
    `erdos647_selberg_optimal_weight`), for every `d ∈
    prodPrimes.divisors`. Genuine new analytic derivation (reindex the
    defining Möbius-inversion sum via `l'=d·e`, use multiplicativity +
    `μ(e)²=1` to collapse to `μ(d)·(selbergTerms(d)/L)·∑selbergTerms(e)`,
    bound the inner sum by `L`). Caught and fixed a sign error in an
    earlier hand-derivation (`w(d)` is NOT `≥0`, it alternates sign with
    `μ(d)` — only the absolute-value bound holds) before formalizing.
    Snapshot `proof/Erdos647_SelbergWeightBound.lean`. This was the
    genuine open research gap flagged at the end of the prior session —
    now closed.
  - ✅ **λ² aggregate bound DONE (2026-07-14)**: `erdos647_lambdaSquared_bound`
    proves `|lambdaSquared(w)(d)| ≤ (∑_{d1∣d}selbergTerms(d1)/ν(d1))²`
    given the pointwise bound (generic in `w`, reusable). Snapshot
    `proof/Erdos647_LambdaSquaredBound.lean`.
  - ✅ **rootUnionCount(d) ≤ 7^ω(d) DONE (2026-07-14)**:
    `erdos647_rootUnionCount_le` proves the explicit numeric growth bound
    for squarefree admissible `d` (combines `crt_card_finset` + inlined
    per-prime admissibility, `∏≤7 ≤ 7^ω(d)`). Snapshot
    `proof/Erdos647_RootUnionCountLe.lean`.
  - ✅ **ν bridging lemma DONE (2026-07-14)**: `erdos647_nu_eq_prod`
    confirms the raw combinatorial `ν(d):=rootUnionCount(d)/d` used by
    `rem_bound_squarefree` equals `∏_{p∣d}ν(p)` — the SAME quantity the
    abstract `SelbergSieve` framework's `s.nu` computes (via
    `ArithmeticFunction.prodPrimeFactors_apply`'s unfolding). Confirms
    the `rem`-bound theorems and the Selberg weight/`lambdaSquared`
    bounds are talking about the same `ν` for a shared instance. Snapshot
    `proof/Erdos647_NuEqProd.lean`.
  - ✅ **multSum bridging lemma DONE (2026-07-14)**:
    `erdos647_multSum_eq_filter_card` confirms Mathlib's
    `BoundingSieve.multSum` (sum-over-support indicator, for our
    support/weights choice) equals the raw filter-count form used
    throughout the `rem`-bound theorems. Snapshot
    `proof/Erdos647_MultSumEqFilterCard.lean`.
  - ✅ **Multiplicative sum-over-divisors identity DONE (2026-07-14)**:
    `erdos647_divisor_sum_prod_one_add` proves, for a `Finset t` of distinct
    primes and any `f:ℕ→ℝ`, `∑_{d1∣∏t} ∏_{p∈d1.primeFactors} f(p) =
    ∏_{p∈t}(1+f(p))` — combined with `selbergTerms_apply`
    (`selbergTerms(d1)/ν(d1) = ∏_{p∈d1.primeFactors}(1-ν(p))⁻¹`), this gives
    the CLOSED FORM `∑_{d1∣d} selbergTerms(d1)/ν(d1) =
    ∏_{p∈d.primeFactors}(1+(1-ν(p))⁻¹)` that
    `erdos647_lambdaSquared_bound`'s bound needs made concrete/summable.
    Kernel-verified first-try on the tracked pipeline after 3 verification-tool
    rounds. Snapshot `proof/Erdos647_DivisorSumProdOneAdd.lean`. Lessons: an
    ambiguous no-argument `rw [Finset.prod_insert ...]` silently picked the
    wrong of two structurally-different `∏x∈insert p t',...` occurrences
    (fixed with explicit `conv_lhs`/`conv_rhs`); a `simp only [...,
    Nat.mem_divisors]` that already fully unfolds a goal makes a later
    redundant `rw [Nat.mem_divisors]` fail (same "already unfolded" trap as
    `RemBoundSquarefree`); `Dvd.intro p rfl` fails when the two sides aren't
    syntactically equal under Nat mul-commutativity (need `⟨p, by ring⟩`);
    `Nat.Coprime.dvd_of_dvd_mul_left` wants its coprimality hypothesis with
    the dividing element first, requiring a `.symm` flip.
  - ✅ **Concrete closed form for the abstract SelbergSieve divisor sum
    DONE (2026-07-14)**: `erdos647_divisor_sum_selbergTerms_div_nu` proves,
    for any `s:SelbergSieve` and `d∈s.prodPrimes.divisors`,
    `∑_{d1∣d} selbergTerms(d1)/ν(d1) = ∏_{p∈d.primeFactors}(1+(1-ν(p))⁻¹)`
    — combining `erdos647_divisor_sum_prod_one_add` (inlined, since
    cross-submission references don't work) with Mathlib's
    `selbergTerms_apply` and `nu_pos_of_dvd_prodPrimes`. This makes
    `erdos647_lambdaSquared_bound`'s bound fully concrete. Kernel-verified
    FIRST TRY on both the untracked pre-check and the tracked pipeline.
    Snapshot `proof/Erdos647_DivisorSumSelbergTermsDivNu.lean`.
  - ✅ **Conditional termwise errSum bound DONE (2026-07-14)**:
    `erdos647_errSum_conditional_bound` proves, for any `s:SelbergSieve`
    and weight `w` satisfying the Selberg pointwise magnitude bound,
    `errSum(lambdaSquared w) ≤ ∑_{d∣prodPrimes}
    (∏_{p∈d.primeFactors}(1+(1-ν(p))⁻¹))²·|rem d|` — combining
    `erdos647_lambdaSquared_bound` + `erdos647_divisor_sum_selbergTerms_div_nu`
    (both inlined). Deliberately leaves `|rem d|` abstract/generic (not
    tied to this campaign's own construction), decoupling the
    errSum-bounding wiring (done, reusable for any `SelbergSieve`) from
    bounding `|rem d|` itself (already done separately via
    `erdos647_rem_bound_squarefree`/`_one` for our own instance) — the
    final numeric assembly substitutes the latter into the former inside
    one self-contained submission. Kernel-verified FIRST TRY on both the
    untracked pre-check and the tracked pipeline. Snapshot
    `proof/Erdos647_ErrSumConditionalBound.lean`.
  - 🏆 **CAPSTONE: full conditional Selberg sieve bound DONE (2026-07-14)**:
    `erdos647_selberg_sieve_bound_conditional` proves, for ANY
    `s:SelbergSieve`, `siftedSum ≤ totalMass/L + ∑_{d∣prodPrimes}
    (∏_{p∈d.primeFactors}(1+(1-ν(p))⁻¹))²·|rem d|` where
    `L=∑_{l∣prodPrimes}selbergTerms(l)` — combining the ENTIRE Layer B
    optimal-weight construction, its magnitude bound, Mathlib's
    upper-Moebius sieve inequality, and the errSum aggregate bound into
    ONE ~400-line theorem. Deliberately leaves `|rem d|` abstract so the
    wiring is fully generic/reusable; the campaign's own construction
    (`rem_bound_squarefree`/`_one` + `rootUnionCount_le`) substitutes in
    directly at the final numeric-assembly step. Kernel-verified FIRST
    TRY on both the untracked pre-check (~22s Lean CPU time) and the
    tracked pipeline — zero new Lean bugs, built by carefully sharing
    the `D`/`L`/`y`/`w` local definitions between the (previously
    separate) optimal-weight and weight-bound arguments rather than
    re-deriving or risking a syntactic w-mismatch. Snapshot
    `proof/Erdos647_SelbergSieveBoundConditional.lean`. **Only remaining
    step for the final `x/(log x)^7` theorem**: inline this campaign's
    own seven-tuple `BoundingSieve` instance as a concrete `s`, substitute
    the concrete `rem`/`rootUnionCount` bounds, tie `L`'s growth rate to
    Layer A's `erdos647_mertens_assembly`, and choose `z=z(x)` optimally.
  - ✅ **L Euler-product closed form DONE (2026-07-14)**: `erdos647_L_eq_prod`
    proves `L := ∑_{l∣prodPrimes} selbergTerms(l) = ∏_{p∈prodPrimes.
    primeFactors}(1-ν(p))⁻¹` — combining Mathlib's own `sum_divisors_
    selbergTerms_eq_selbergTerms_mul_nu_inv` (at `d:=prodPrimes`) with
    `selbergTerms_apply` and cancelling the `ν(prodPrimes)` factor. This
    is what a Mertens-type product estimate needs to act on directly to
    get `L`'s growth rate as a function of the level `z`. Kernel-verified
    (1 fix: `mul_right_comm` instead of a non-adjacent `mul_comm` to
    bring the cancelling `ν(prodPrimes)`/`ν(prodPrimes)⁻¹` factors
    together). Snapshot `proof/Erdos647_LEqProd.lean`.
  - 🔑 **NEW STRUCTURAL FACT: rootUnionCount(p)=7 exactly, p>7,p≠11
    DONE (2026-07-14)**: `erdos647_seventuple_rootcount_eq_seven`
    sharpens the earlier "between 1 and 7" bound to an EXACT value for
    all but ONE exceptional prime — verified numerically first (Python,
    primes to 300), then formalized via pairwise non-collision of the 7
    coefficients' ZMod-p roots (21 pairwise-difference non-divisibility
    facts, each via `native_decide` on a concrete `primeFactors⊆
    {2,3,5,7,11}` check) combined into a 7-way disjoint-union cardinality.
    This is what a Mertens-type growth-rate estimate needs: `ν(p)~7/p`
    (not just `∈[1/p,7/p]`) to get `L~(log z)^7`, matching the target
    exponent. Snapshot `proof/Erdos647_RootCountEqSeven.lean`. Hit and
    fixed the SAME `set`-without-`clear_value` whnf-timeout class as
    `erdos647_rem_bound` — now a confirmed 3rd instance; the lesson
    generalizes to any proof combining several `set`-bound `Finset.filter`
    locals via multiple downstream `have`s.
  - ✅ **Our concrete ν(p) = 7/p exactly DONE (2026-07-14)**:
    `erdos647_nu_eq_seven_div_p` is the direct corollary of the exact
    rootUnionCount fact, unfolding our own `ν` (from
    `erdos647_nu_admissible`) via `ArithmeticFunction.prodPrimeFactors_apply`
    down to `rootUnionCount(p)/p = 7/p` for `p>7, p≠11`. Snapshot
    `proof/Erdos647_NuEqSevenDivP.lean`. This is the exact per-prime
    density needed to drive the Mertens-type growth-rate estimate for
    `L=∏(1-ν(p))⁻¹ ~ (log z)^7`.
  - ✅ **Mertens-type lower bound on ∑ν(p) DONE (2026-07-14)**:
    `erdos647_nu_sum_ge_seven_mertens` proves, for `z≥11`,
    `7·∑_{p≤z,Prime}1/p − 7·(1/2+1/3+1/5+1/7+1/11) ≤ ∑_{p≤z,Prime}ν(p)`
    — split at `p>11` via `Finset.sum_filter_add_sum_filter_not`, exact
    substitution `ν(p)=7/p` on the `p>11` part, the `p≤11` part (⊆
    `{2,3,5,7,11}`) dropped as a nonneg correction bounded by an explicit
    constant. This is the first piece feeding into a full Mertens-type
    growth-rate estimate for `L~(log z)^7`, combined with
    `erdos647_mertens_assembly`'s lower bound on `∑1/p` and
    `-log(1-x)≥x`. Snapshot `proof/Erdos647_NuSumGe.lean`.
  - ✅ **Generic log L ≥ ∑ν(p) bound DONE (2026-07-14)**:
    `erdos647_L_ge_exp_nu_sum` proves, for ANY `s:SelbergSieve`,
    `∑_{p∈prodPrimes.primeFactors}ν(p) ≤ log L` (via `Real.log_prod` +
    the elementary `-log(1-x)≥x`). Fully generic, combines directly with
    `erdos647_nu_sum_ge_seven_mertens` (once instantiated with our own
    construction) to get `log L ≥ 7·loglog(z)−C`, i.e. `L≳(log z)^7` —
    the target growth rate. Snapshot `proof/Erdos647_LGeExpNuSum.lean`.
  - ⚠⚠ **CRITICAL DIAGNOSTIC (2026-07-14): the errSum bound chain may not
    be tight enough — genuine open question, not yet resolved.** Mathlib's
    `SelbergSieve.level` field is declared but VESTIGIAL — grepped the
    whole file: `lambdaSquared` and every downstream theorem
    (`mainSum_lambdaSquared_eq_sum_mul_sum_sq`,
    `siftedSum_le_mainSum_errSum_of_upperMoebius`) sum over
    `prodPrimes.divisors` unrestricted, never truncating `w`'s support to
    `d≤level` as classical Selberg theory requires for error-term control.
    `erdos647_selberg_optimal_weight` (Layer B) has no such truncation
    either. The pointwise bound `|w(d)|≤selbergTerms(d)/ν(d)` used in
    `errSum_conditional_bound` discards the `μ(d)`-sign cancellation the
    real optimal weight has, and `∑_{d|prodPrimes(z)}(∏(1+(1-ν(p))⁻¹))²·
    7^ω(d)` unrestricted is plausibly EXPONENTIAL in `π(z)` (`~29^π(z)`)
    — reproducing the "Legendre explosion" already ruled out for the pure
    Möbius shortcut, just smuggled back in via a bound too weak to see
    Selberg's actual cancellation. **Two possible resolutions, neither
    attempted yet**: (a) rebuild Layer B's optimal-weight construction
    with an explicit level-`y` truncation (`w(d):=0` for `d>y`) —
    substantial rework of every Layer B theorem; (b) find a sharper
    direct bound on `∑_d|lambdaSquared(w)(d)|·|rem(d)|` using `w`'s
    actual signed structure, not just `|w(d)|≤...`. **Do not force the
    final numeric assembly by plugging the unrestricted errSum bound into
    the Mertens growth rate without resolving this first** — the L/main-
    term growth-rate chain (`nu_sum_ge_seven_mertens`+`L_ge_exp_nu_sum`+
    Layer A Mertens) is solid and complete; only the error-term side needs
    this rework.
  - ✅ **errSum REPAIR, Milestone A piece 1/N DONE (2026-07-14):
    `erdos647_lambdaSquared_support_sq`** proves the generic mechanism
    that fixes the critical errSum defect: `(∀d,R<d→w d=0) → ∀d,
    R*R<d→lambdaSquared(w)(d)=0` — a level-truncated weight automatically
    gives a level-truncated `lambdaSquared`, converting the errSum bound
    from "over all `2^π(z)` divisors" to "over integers `≤R²`". Fully
    generic, no Lean bugs. Snapshot
    `proof/Erdos647_LambdaSquaredSupportSq.lean`. **Still needed for the
    full repair** (Milestone A remainder): actually construct a
    truncated optimal weight `w_R` (restricted-divisor-set Möbius
    inversion, `w_R(1)=1`, `mainSum(lambdaSquared w_R)=1/L_R`) — see the
    level-truncation repair plan under the CRITICAL DIAGNOSTIC headline
    at the top of this file.
  - ✅ **errSum REPAIR, Milestone C piece DONE (2026-07-14):
    `erdos647_selberg_coeff_bound`** proves the uniform coefficient
    bound `1+(1-ν(p))⁻¹≤4` for every admissible prime — simpler than
    planned, since `ν(p)≤7/p≤7/11<2/3` uniformly for ALL primes `p>7`
    (any prime `p>7` is automatically `≥11`), no need for the exact
    `ν(11)=6/11` value or a `p=11` case split. Needed for either errSum
    repair route (level truncation or a sharper signed bound). Snapshot
    `proof/Erdos647_SelbergCoeffBound.lean`.
  - 📚 **Independent research pass completed (2026-07-14, task
    `w7x3bu4fp`)**: a deep-research workflow independently re-verified
    the errSum diagnosis against Mathlib's raw source (CONFIRMED:
    `level` is genuinely inert) and against classical sieve texts
    (CONFIRMED: hard support truncation `λ(d)=0` for `d>z` is the
    standard classical technique, not a shortcut — quote from Rutgers
    notes, "since we have the freedom to choose λ, we'll insist that λ
    is supported on only small numbers: λ(n)=0, if n>z"). **Open gap
    surfaced**: the exact quantitative relationship between the sifting
    level `z` (which primes are active) and the weight-support
    truncation `R`/level-of-distribution `D` (Tao's 254A notes: these
    are TWO independent parameters, `D` is not simply derived from `z`)
    was not pinned to a clean primary source — do not assume `R=z^A` or
    any specific normalization without re-deriving it directly from the
    log-moment tail bound below. Secondary unconfirmed risk flagged:
    Granville–Koukoulopoulos–Maynard (arXiv:1606.06781) show bare
    non-smoothed cutoff weights can misbehave for a *different* (linear,
    not λ²-quadratic) weight object — applicability to this campaign's
    construction is unresolved, not a confirmed blocker.
  - ✅ **errSum REPAIR, Milestone A/B piece DONE (2026-07-14):
    `erdos647_selberg_log_moment`** proves the log-moment identity
    `∑_{d∣prodPrimes} selbergTerms(d)·log(d) = L·∑_{p∣prodPrimes}
    ν(p)·log(p)` for any `SelbergSieve` — the key fact needed to show a
    level-truncated denominator `L_R := ∑_{d∣prodPrimes,d≤R}
    selbergTerms(d)` retains `L`'s growth rate: since `log d>log R` for
    `d>R>1` and `selbergTerms≥0`, `∑_{d>R}selbergTerms(d) ≤
    (1/log R)·∑_{d>R}selbergTerms(d)·log(d) ≤ (L/log R)·∑_pν(p)log(p)`,
    giving `L_R ≥ L·(1−[∑_pν(p)log p]/log R)`. Proof: combined
    `Finset.induction_on` over an abstract prime `Finset`, using the
    per-prime identity `selbergTerms(p)=(1+selbergTerms(p))·ν(p)`. Two
    bugs, both the same self-referential-rewrite pattern seen repeatedly
    this campaign — most notably `rw [hkey]` (where `hkey`'s own RHS
    still contains the LHS pattern being rewritten) corrupted BOTH sides
    of a goal at once, confirmed by reading the exact post-`kernel_fail`
    unsolved-goals diagnostic (a spurious `ν(p)²` cross term appeared);
    fixed with `conv_lhs => rw [hkey]` to scope the rewrite. Snapshot
    `proof/Erdos647_SelbergLogMoment.lean`. **Still needed for the full
    Milestone A/B repair**: the actual level-truncated weight
    construction `w_R` (restricted-divisor-set Möbius inversion,
    `w_R(1)=1`, `mainSum(λ²w_R)=1/L_R`), combined with
    `erdos647_lambdaSquared_support_sq`'s support bound and this
    log-moment tail estimate, to get a complete truncated-Selberg-sieve
    bound with a controlled error term.
  - ⚠ **Important environment-constraint finding**: `erdos647_boundingSieve_instance`'s
    statement is `∀ z, Nonempty BoundingSieve` — it proves EXISTENCE only,
    not a nameable value with accessible fields, and cross-submission
    references don't work anyway (each tracked submission compiles
    independently). This means the eventual final numeric theorem cannot
    "load" a previously-built instance; it must either (a) construct the
    instance inline within one giant self-contained submission alongside
    everything else, or (b) stay in fully elementary/combinatorial terms
    (as `rem_bound_squarefree`, `nu_eq_prod`, `multSum_eq_filter_card`
    already do) and only reach for the abstract `SelbergSieve` API
    (`selberg_weight_bound`, `lambdaSquared_bound`,
    `siftedSum_le_mainSum_errSum_of_upperMoebius`) via GENERIC lemmas
    parameterized over an abstract `s`, never a named concrete instance —
    exactly the pattern already used for every Selberg-specific theorem
    built this session. Route (b) is what's been followed throughout;
    the final assembly will still need a single large, carefully-staged
    submission, but every individual piece it draws on is independently
    pre-verified.
  - **Remaining for the final numeric theorem**: combine
    `erdos647_lambdaSquared_bound` (instantiated with
    `erdos647_selberg_weight_bound`'s pointwise bound) with
    `erdos647_rem_bound_squarefree`/`erdos647_rem_bound_one` and
    `erdos647_rootUnionCount_le` to bound `errSum(lambdaSquared w) =
    Σ_d |lambdaSquared w d|·|rem d|`; combine with
    `siftedSum_le_mainSum_errSum_of_upperMoebius` +
    `erdos647_selberg_optimal_weight` (mainSum value) + Layer A's
    `erdos647_mertens_assembly`, choosing an optimal `z=z(x)` balancing
    main term vs error term, for the final `x/(log x)^7`-shaped bound.
    This remaining step is now genuinely "assembly" (combining proven
    pieces + an explicit growth-rate/summability estimate for
    `∑_{d|prodPrimes(z)} selbergTerms(d)/ν(d)`-type sums), not open
    research — though the growth-rate estimate itself still needs care.
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
