# Attack plan — Erdős #647 (living)

> Last updated 2026-07-16. This is the working plan of record; it changes as
> results land. Completed milestones move to the whitepaper's campaign log.

## HEADLINE STATUS (2026-07-16)

**The concrete global density theorem is kernel-verified.** The bounded
candidate set, exact `n = 2520N` reindexing, seven-shift coprimality bridge,
promoted concrete sieve, truncated optimal weight, polynomial error,
denominator lower bound, dyadic parameter choice, large-range estimate, and
finite-range closure now compose to
`|C(X)| ≤ K * X / (log X)^7` for every natural `X`, with an explicit effective
constant `K`. A clean replay from source compiled all 42 transitive campaign
modules plus `family2-classifications.lean` in the pinned environment.
The Erdős problem itself remains open: this density theorem neither produces
nor excludes a larger candidate.

**The campaign is active again on the original existence question.** The new
target is individual/eventual impossibility, not another fixed-dimensional
density estimate: prove that every `n > 24` has some positive shift `k < n`
with `σ₀(n-k) > k+2`. The global maximum is now kernel-verified to be
*equivalent* to all of its pointwise shift budgets. The entire interval
`25 ≤ n ≤ 84` is closed by exact computation, so every remaining hypothetical
candidate is formally above `84`, divisible by `2520`, and in one of the two
four-prime families. The short-window variant has likewise been reduced
exactly to fixed-depth survivor infinitude.

One analytic correction is now part of the proof record. The earlier
Chebyshev/Mertens lower bound is valid, but its leading coefficient is
`log 2`; after multiplying by seven it is too weak to yield a seventh power
of `log z`. The final proof instead establishes the elementary finite Euler
product bound
`∑_{n≤z} 1/n ≤ ∏_{p≤z}(1-1/p)⁻¹` using divisibility by `z!`. Combined with the
exact seven roots away from the deleted small primes and their exact Euler
factor loss `77/16`, this gives
`(16/77)^7 * (log z)^7 ≤ L`. Thus the final exponent is not resting on the
insufficient Mertens coefficient.

The repaired optimal weight has hard support `d≤R`, its `lambdaSquared` has
support `d≤R²`, its coefficients are bounded by `16^ω(d)`, and the concrete
seven-form remainder is bounded by `7^ω(d)`, giving
`errSum≤(R²+1)^8`. The verified moment estimate permits `R=(2z)^20`; dyadic
`z=2^k` absorbs this polynomial error into the required logarithmic scale.

## Guiding constraint (proven, not vibes)

The **all-avoid obstruction** (Hughes) and our extension of it to
Theorem-2 chain forms mean: no finite pile of congruence arguments closes
the 41 open residue classes. Progress on the *theorem itself* must come
from analytic estimates (density bounds) or from a genuinely new leaf type
nobody has found yet. Sub-AP/congruence work is therefore frozen except
where a specific new leaf type appears.

## Track 1 — the density-bound program (COMPLETE)

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
- **Layer C — the 7-tuple application. COMPLETE through the global density
  theorem (2026-07-15).** Hughes's paper attributes
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
  - ✅ **Historical remaining step, now resolved (2026-07-15)**: sum
    `erdos647_rem_bound_squarefree` (plus `erdos647_rem_bound_one` for
    `d=1`) over `prodPrimes(z).divisors` weighted by the
    Selberg `λ_d²` structure (`lambdaSquared`, from
    `Mathlib.NumberTheory.SelbergSieve`) to get the actual `errSum` used
    by `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`; this
    required a bound on `|lambdaSquared w d|` for a level-truncated optimal
    weight. The later truncation repair establishes `16^ω(d)`, and the
    concrete remainder gives `7^ω(d)`, producing
    `errSum≤(R²+1)^8`. The final main-term exponent uses the elementary
    Euler-product lower bound described in the headline, and the dyadic
    parameter assembly is complete.
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
    constant. This is valid Mertens-type infrastructure, but the available
    Chebyshev lower bound has leading coefficient `log 2`, so this route alone
    does not prove the required seventh power. Snapshot
    `proof/Erdos647_NuSumGe.lean`.
  - ✅ **Generic log L ≥ ∑ν(p) bound DONE (2026-07-14)**:
    `erdos647_L_ge_exp_nu_sum` proves, for ANY `s:SelbergSieve`,
    `∑_{p∈prodPrimes.primeFactors}ν(p) ≤ log L` (via `Real.log_prod` +
    the elementary `-log(1-x)≥x`). Fully generic and still useful, but the
    campaign's concrete seventh-power lower bound now comes from the stronger
    factorial/Euler-product argument. Snapshot
    `proof/Erdos647_LGeExpNuSum.lean`.
  - ✅ **HISTORICAL CRITICAL DIAGNOSTIC (2026-07-14), RESOLVED
    2026-07-15.** Mathlib's
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
    Selberg's actual cancellation. The chosen resolution was to rebuild
    Layer B's optimal-weight construction
    with an explicit level-`y` truncation (`w(d):=0` for `d>y`) —
    substantial rework of every Layer B theorem. The resulting hard support
    and coefficient bounds give the polynomial error stated below. Separately,
    the main-term exponent is supplied by the new elementary Euler-product
    lower bound, not by the insufficient-coefficient Mertens chain.
  - ✅ **errSum REPAIR, Milestone A piece 1/N DONE (2026-07-14):
    `erdos647_lambdaSquared_support_sq`** proves the generic mechanism
    that fixes the critical errSum defect: `(∀d,R<d→w d=0) → ∀d,
    R*R<d→lambdaSquared(w)(d)=0` — a level-truncated weight automatically
    gives a level-truncated `lambdaSquared`, converting the errSum bound
    from "over all `2^π(z)` divisors" to "over integers `≤R²`". Fully
    generic, no Lean bugs. Snapshot
    `proof/Erdos647_LambdaSquaredSupportSq.lean`. The required truncated
    optimal weight `w_R` is now constructed below (2026-07-15).
  - ✅ **errSum REPAIR, Milestone A/B piece 2/N DONE (2026-07-14):
    `erdos647_selberg_L_tail_bound`** proves the growth-preservation
    step built directly on `erdos647_selberg_log_moment`:
    `∑_{d∣prodPrimes,d>R} selbergTerms(d) ≤ L·(∑_pν(p)log p)/log R` for
    any `R>1`. Combined with the trivial split `L=L_R+tail`, this gives
    `L_R ≥ L·(1−[∑_pν(p)log p]/log R)` — i.e. the level-truncated
    denominator `L_R` retains `L`'s `≳(log z)^7` growth once `R` is
    large enough. Zero Lean bugs, kernel-verified FIRST TRY on both
    pre-check and tracked pipeline — the first repair-sequence piece
    with no verification-tool round trip. Snapshot
    `proof/Erdos647_SelbergLTailBound.lean`. The `w_R` construction is
    now complete below; **for the final normalization** (choosing
    `R=R(z)`): per the deep-research finding,
    do not assume `R=z^A`, derive the balance directly from this bound
    once the error-side growth rate is known.
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
    `proof/Erdos647_SelbergLogMoment.lean`. The formerly missing
    level-truncated weight construction is now complete in
    `erdos647_selberg_optimal_weight_truncated` below.
  - ✅ **errSum REPAIR, Milestone A construction DONE (2026-07-15):
    `erdos647_selberg_optimal_weight_truncated`** proves that for every
    `SelbergSieve s` and `R≥1` there is a weight `w_R` with `w_R(1)=1`,
    hard support `w_R(d)=0` for `d>R`, and exact diagonal value
    `mainSum(lambdaSquared w_R)=1/L_R`, where
    `L_R=∑_{l∣prodPrimes,l≤R}selbergTerms(l)`. The decisive construction
    keeps Möbius inversion over the full divisor lattice but sets the
    target diagonal data to zero outside `l≤R`; nonzero terms in `w_R(d)`
    therefore force `d∣l'≤R`. Together with
    `erdos647_lambdaSquared_support_sq`, this gives
    `lambdaSquared(w_R)(d)=0` for `d>R²`; together with
    `erdos647_selberg_L_tail_bound`, it preserves the main denominator's
    growth. Kernel-verified through proof-search MCP in 2 tracked attempts
    (the first exposed two filtered-Finset elaboration errors; the second
    passed). Snapshot `proof/Erdos647_SelbergOptimalWeightTruncated.lean`,
    episode `333d528d-3032-47b6-ba2e-fa5ae42da41f`.
  - ✅ **Truncated optimal weight coefficient bound DONE (2026-07-15):
    `erdos647_selberg_optimal_weight_truncated_bound`** strengthens the
    construction with `|w_R(d)|≤selbergTerms(d)/ν(d)` on every primorial
    divisor. Reindexing leaves a filtered positive cofactor sum; the fact
    `d·e≤R → e≤R` embeds it into `L_R`. Kernel-verified first tracked
    attempt. Snapshot
    `proof/Erdos647_SelbergOptimalWeightTruncatedBound.lean`, episode
    `445e255c-cc28-443c-bcf5-a883543784da`.
  - ✅ **Numeric lambda coefficient bound DONE (2026-07-15):
    `erdos647_lambdaSquared_card_bound`** combines the pointwise weight
    estimate with the uniform prime factor bound
    `1+(1-ν(p))⁻¹≤4` to prove
    `|lambdaSquared(w)(d)|≤16^ω(d)`. Kernel-verified in 2 tracked
    attempts. Snapshot `proof/Erdos647_LambdaSquaredCardBound.lean`,
    episode `cf8a89b5-0e9e-4b70-babf-ebffe3b4d954`.
  - ✅ **Polynomial hard-truncated errSum bound DONE (2026-07-15):
    `erdos647_errSum_truncated_polynomial`** proves
    `errSum(lambdaSquared w)≤(R²+1)^8` from hard support `d≤R²`, the
    `16^ω(d)` coefficient bound, and the `7^ω(d)` remainder bound. The
    elementary core is `112^ω(d)≤128^ω(d)≤d^7` for squarefree `d`, since
    `2^ω(d)≤d`; fewer than `R²+1` integers survive. This is the formal
    resolution of the exponential divisor-lattice defect. Kernel-verified
    first tracked attempt. Snapshot
    `proof/Erdos647_ErrSumTruncatedPolynomial.lean`, episode
    `312120f0-82e4-49d8-a0a5-022822683064`.
  - ✅ **Prime log-moment upper bound DONE (2026-07-15):**
    `erdos647_prime_log_div_identity` proves by Abel summation that
    `∑_{p≤x}log(p)/p=θ(x)/x+∫θ(t)/t²`; then
    `erdos647_prime_log_div_upper` combines Mathlib's
    `θ(t)≤log(4)t` with `∫dt/t=log(x/2)` to obtain
    `∑_{p≤x}log(p)/p≤log(4)(1+log(x/2))`. Thus
    `∑ν(p)log p=O(log z)` and the `L_R` tail condition only requires
    polynomial `R(z)`. Snapshots `proof/Erdos647_PrimeLogDivIdentity.lean`
    and `proof/Erdos647_PrimeLogDivUpper.lean`; episodes
    `fbf2047c-f3aa-4a54-9529-8ab7ecdd81e5` and
    `e7e66b7f-45ad-4031-8dbc-c3c4af9d9717`.
  - ✅ **Half-denominator invariant DONE (2026-07-15):
    `erdos647_selberg_L_truncated_ge_half`** packages the log-moment tail
    estimate into the exact form needed downstream:
    `∑ν(p)log p≤log(R)/2 → L_R≥L/2`. Kernel-verified in 2 tracked
    attempts. Snapshot `proof/Erdos647_SelbergLTruncatedGeHalf.lean`,
    episode `d2c798f6-9476-4029-b72d-71ac9c898c14`.
  - ✅ **The `R=(2z)^20` log-moment choice DONE (2026-07-15):
    `erdos647_parameter_R20_moment` proves, for every real `z≥2`,
    `7·log(4)·(1+log(z/2))≤log((2z)^20)/2`. This formally certifies
    the numerical slack `7·log(4)<10` needed to feed the seven-form prime
    moment estimate into the half-denominator invariant. Kernel-verified
    in 3 tracked attempts and independently rechecked. Snapshot
    `proof/Erdos647_ParameterR20Moment.lean`, episode
    `c7a9a71b-13be-4c5a-ab86-953c8d7e76c1`.
  - ✅ **Explicit polynomial error for `R=(2z)^20` DONE (2026-07-15):
    `erdos647_parameter_error_polynomial` proves over natural numbers
    that `z≥1` implies
    `((((2z)^20)^2+1)^8)≤2^328·z^320`. Thus the former asymptotic
    notation `(R²+1)^8=O(z^320)` now has a concrete effective constant.
    Kernel-verified in 3 tracked attempts and independently rechecked.
    Snapshot `proof/Erdos647_ParameterErrorPolynomial.lean`, episode
    `668f3e3f-190e-4b7d-9e23-c111482e2534`.
  - ✅ **Dyadic integer `z=z(X)` bracket DONE (2026-07-15):
    `erdos647_dyadic_parameter_bracket` proves that every nonzero natural
    `X` admits `k` with `(2^k)^400≤X<(2·2^k)^400`. Taking `z=2^k`
    gives the exact integer substitute for `z≈X^(1/400)`, using
    `k=Nat.log (2^400) X`. Kernel-verified in 2 tracked attempts and
    independently rechecked. Snapshot
    `proof/Erdos647_DyadicParameterBracket.lean`, episode
    `cd7d60ab-82d3-4288-9b58-da5f3553a257`.
  - ✅ **Exact `X^(4/5)` error absorption encoding DONE (2026-07-15):
    `erdos647_error_absorption_power` proves that
    `E≤2^328·z^320` and `z^400≤X` imply
    `E^5≤2^1640·X^4`. This is the fractional estimate in a form using
    only natural-number powers, so it composes directly with the dyadic
    bracket. Kernel-verified on the first tracked attempt and independently
    rechecked. Snapshot `proof/Erdos647_ErrorAbsorptionPower.lean`,
    episode `88f161ad-0233-4381-aded-09f76a861a90`.
  - ✅ **Dyadic error absorbed at the `X/k^7` scale DONE (2026-07-15):
    `erdos647_dyadic_error_log_scale` proves that
    `(2^k)^400≤X` and `E≤2^328·(2^k)^320` imply
    `E·k^7≤2^328·X`. Since `log(2^k)=k·log 2`, this is the exact
    algebraic form needed to absorb the polynomial error into an
    `X/(log z)^7` main bound. Kernel-verified in 2 tracked attempts and
    independently rechecked. Snapshot
    `proof/Erdos647_DyadicErrorLogScale.lean`, episode
    `52f39da0-0c91-4381-ba6b-6763044014e1`.
  - ✅ **Real-log error bridge DONE (2026-07-15):
    `erdos647_dyadic_error_real_log` turns `E·k^7≤2^328·X`
    into the direct bound
    `E≤2^328·(log 2)^7·X/(log(2^k))^7` for `k>0`, using the exact
    identity `log(2^k)=k·log 2`. Thus the parameter/error component is
    now closed all the way to the analytic denominator used in the
    density theorem. Kernel-verified on the first tracked attempt and
    independently rechecked. Snapshot
    `proof/Erdos647_DyadicErrorRealLog.lean`, episode
    `a4646056-f6af-462c-be5f-1fee2bd03727`.
  - ✅ **Generic two-parameter sieve assembly DONE (2026-07-15):
    `erdos647_two_parameter_sieve_assembly` proves that the truncated
    main-sum identity `mainSum=1/L_R`, `L_R≥L/2`, and
    `errSum≤(R²+1)^8` imply
    `siftedSum≤2·totalMass/L+(R²+1)^8`. This lands assembly stage 2 and
    confirms there is no further analytic algebra hidden between the
    repaired components and the concrete instance. Kernel-verified on
    the first tracked attempt and independently rechecked. Snapshot
    `proof/Erdos647_TwoParameterSieveAssembly.lean`, episode
    `47248be9-ad01-4c85-a333-1bade2673bfc`.
  - ✅ **Exposed two-parameter concrete seven-form witness DONE
    (2026-07-15):** `erdos647_boundingSieve_exposed` separates the
    candidate range `X` from the active-prime level `z` and returns exact
    equations for `support`, `prodPrimes`, unit `weights`, `totalMass=X`,
    and the multiplicative `nu`. This removes the earlier opaque
    `Nonempty BoundingSieve` interface. Kernel-verified on the first
    tracked attempt and independently rechecked. Snapshot
    `proof/Erdos647_BoundingSieveExposed.lean`, episode
    `76254e7f-c4ca-45e2-a029-26697df01c16`.
  - ✅ **Core concrete field audit DONE (2026-07-15):** four new theorems
    verify the representation-sensitive chain: exposed support/weights
    give the exact raw `multSum`; exposed fields rewrite `s.rem(d)` to the
    raw remainder; squarefree `prodPrimeFactors` `nu(d)` equals the raw
    CRT density; and the raw remainder/root-count estimates assemble to
    `|s.rem(d)|≤7^ω(d)`. All landed on their first tracked attempts and
    passed independent replay. Snapshots
    `proof/Erdos647_MultSumFieldAudit.lean`,
    `proof/Erdos647_RemFieldAudit.lean`,
    `proof/Erdos647_NuFieldAudit.lean`, and
    `proof/Erdos647_RemBoundFieldAssembly.lean`; episodes
    `3c2ce9c0-6e0b-4bd8-9b52-8e6464a32d64`,
    `e95b56da-6d95-43eb-85c5-ea2ae9c128be`,
    `a8a19a21-345a-4e96-a656-1206b8947f16`, and
    `161e04d9-7439-4866-b5d7-483d1cb4b0c7`.
  - ✅ **Survivor field and candidate-count transport DONE
    (2026-07-15):** `erdos647_siftedSum_field_audit` identifies
    `siftedSum` exactly with the number of parameters whose seven-form
    product is coprime to `prodPrimes`; `erdos647_candidate_finset_le_siftedSum`
    then embeds any bounded candidate Finset satisfying that coprimality
    condition. Both landed on their first tracked attempts and passed
    independent replay. Snapshots
    `proof/Erdos647_SiftedSumFieldAudit.lean` and
    `proof/Erdos647_CandidateFinsetBridge.lean`.
  - ✅ **Family-B parity obstruction found and repaired (2026-07-15):**
    the original modulus includes `2`, so every odd parameter has
    `2 ∣ 315N-1` and is rejected. This exactly conflicts with the allowed
    Family B branch, where `315N-1` is twice a prime. The obstruction is
    kernel-verified by `erdos647_odd_parameter_rejected_by_two`, and
    `erdos647_boundingSieve_exclude_two` constructs an otherwise identical
    concrete sieve with `2,3,5,7` excluded. The support, weights, mass, and
    `nu` are unchanged, so the large-prime dimension remains seven.
    Snapshots `proof/Erdos647_OddParameterRejectedByTwo.lean` and
    `proof/Erdos647_BoundingSieveExcludeTwo.lean`.
  - ✅ **Candidate-specific repaired-modulus coprimality DONE
    (2026-07-15):** `erdos647_repaired_modulus_candidate_coprime` proves
    that the campaign's exact shift-classification shape—six prime forms
    and `315N-1` prime or twice a prime—implies coprimality with the
    repaired active-prime product whenever `z<157N`. This handles Family A
    and Family B uniformly. Snapshot
    `proof/Erdos647_RepairedModulusCandidateCoprime.lean`.
  - ✅ **Shift-classification bundle DONE (2026-07-15):**
    `erdos647_shift_outputs_to_seven_forms` converts the verified outputs at
    shifts `1,2,3,4,6,8,12` under `n=2520N` into the exact seven-form bundle,
    including the shift-8 `prime ∨ 2·prime` disjunction. Snapshot
    `proof/Erdos647_ShiftOutputsToSevenForms.lean`.
  - ✅ **Explicit exceptional parameter band DONE (2026-07-15):**
    `erdos647_small_parameter_band_card` proves that the complement of
    `z<157N` inside `[1,X]` has at most `z` elements. Thus the candidate
    bridge's only range loss is an explicit additive term far below the
    existing `z^320` sieve error. Snapshot
    `proof/Erdos647_SmallParameterBand.lean`.
  - ✅ **Final set-theoretic candidate interface DONE (2026-07-15):**
    `erdos647_candidate_finset_le_siftedSum_add_z` combines the exact
    survivor audit, repaired-modulus coprimality hypothesis, and exceptional
    band into the directly consumable inequality
    `(C.card:ℝ)≤s.siftedSum+z`. Snapshot
    `proof/Erdos647_CandidateBridgeAddZ.lean`.
  - ✅ **Repaired-denominator finite correction DONE (2026-07-15):**
    `erdos647_nu_small_prime_values` verifies `nu(2)=1/2` and
    `nu(3)=nu(5)=nu(7)=0`; `erdos647_prime_sum_exclude_small` then proves
    that the repaired active-prime `nu` sum is exactly the old all-prime
    sum minus `1/2`. Thus deleting `2` changes only the effective constant,
    not the seven-dimensional logarithmic exponent. Snapshots
    `proof/Erdos647_NuSmallPrimeValues.lean` and
    `proof/Erdos647_PrimeSumExcludeSmall.lean`.
  - ✅ **Repaired logarithmic denominator assembly DONE (2026-07-15):**
    `erdos647_repaired_prod_primeFactors` aligns the modulus factors with
    the active Finset, and `erdos647_repaired_logL_lower` proves that any
    old all-prime lower bound `B` yields `log L≥B-1/2` for the repaired
    Euler product. The parity repair therefore needs no new exponent or
    parameter certification. Snapshots
    `proof/Erdos647_RepairedProdPrimeFactors.lean` and
    `proof/Erdos647_RepairedLogLLower.lean`.
  - ✅ **Concrete-to-analytic structure adapter DONE (2026-07-15):**
    `erdos647_boundingSieve_to_selbergSieve` promotes any concrete
    `BoundingSieve` to a `SelbergSieve` at every natural level `R≥1`, while
    preserving the complete underlying sieve definitionally. This closes
    the structure-level transport needed to apply the generic truncated
    Selberg theorems to the parity-repaired instance. Snapshot
    `proof/Erdos647_BoundingToSelberg.lean`.
  - ✅ **Candidate/analytic handoff DONE (2026-07-15):**
    `erdos647_candidate_two_parameter_assembly` transports
    `(C.card:ℝ)≤s.siftedSum+z` and `s.totalMass=X` through the generic
    two-parameter sieve inequality. The stronger
    `erdos647_direct_candidate_density_assembly` also folds in the upper
    Möbius argument, truncated main-sum identity, half-denominator bound,
    and polynomial error directly, yielding
    `C.card≤2X/L+(R²+1)^8+z`. Snapshots
    `proof/Erdos647_CandidateTwoParameterAssembly.lean` and
    `proof/Erdos647_DirectCandidateDensityAssembly.lean`.
  - ✅ **Shift outputs to repaired coprimality DONE (2026-07-15):**
    `erdos647_shift_outputs_repaired_coprime` composes the seven verified
    shift-output shapes under `n=2520N` directly with the repaired modulus.
    It covers the shift-8 `prime ∨ 2·prime` branch without family casework.
    Snapshot `proof/Erdos647_ShiftOutputsRepairedCoprime.lean`.
  - ✅ **Original variable to seven-form parameter reindexing DONE
    (2026-07-15):** `erdos647_candidate_reindex_2520` gives an exact
    cardinality-preserving bijection between bounded `n` satisfying
    `2520∣n` and bounded parameters `N≤x/2520`, for an arbitrary candidate
    predicate. No counting constant is lost in passing to the seven-form
    support. Snapshot `proof/Erdos647_CandidateReindex2520.lean`.
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
  - ✅ **Final numeric density theorem COMPLETE (2026-07-15)**: the repaired
    concrete witness, bounded candidate `Finset`, exact reindexing, shift
    classifications, survivor transport, truncated optimal weight, concrete
    remainder, polynomial error, elementary denominator lower bound, dyadic
    parameters, and finite-range closure are assembled in
    `proof/Erdos647_ConcreteAsymptoticDensity.lean`. The global theorem has an
    explicit effective constant and was replayed from a clean source state.
- Fallback if a layer stalls: a weaker exponent (`x/(log x)^k`, k < 7, using
  fewer forms) is still a first-of-its-kind artifact; take the partial win
  and iterate.

## Track 2 — existence closure (ACTIVE)

Target: prove `∀ n, 24 < n → ¬Candidate n`, equivalently show that every such
`n` has a failed shift budget.

- ✅ **Shift-depth interface DONE (2026-07-15):**
  `full_max_implies_shift_budgets` converts the global `ciSup` condition into
  `σ₀(n-k)≤k+2` for every `0<k<n`. `SurvivesThrough n D` packages the first
  `D` budgets, and `not_full_max_of_depth_failure` makes any explicit failure
  a direct contradiction. The main bridge is tracked as problem
  `11379956-bdc3-4ed9-bef3-3e373c8e85c2`, episode
  `3061458d-df2c-4e48-b05d-76b48209a2f6`, outcome `kernel_verified`.
  Snapshot `proof/Erdos647_ShiftDepthInterface.lean`.
- ✅ **Exact converse and finite band DONE (2026-07-16):**
  `full_max_iff_shift_budgets` identifies the global maximum with all positive
  budgets (episode `8bc57f29-adcc-467d-b986-3e060b2d2e3c`). A second tracked
  theorem gives an explicit failed shift for every `25 ≤ n ≤ 84` (episode
  `88a8417d-715f-4d93-aad6-6317e8f1be80`). Consequently every hypothetical
  candidate has `84 < n`; composing the earlier modular and prime-chain
  results proves `2520 ∣ n` and membership in one of the two exact four-prime
  families. Snapshots `proof/Erdos647_FiniteBandClosure.lean` and
  `proof/Erdos647_CandidateStructuralReduction.lean`.
- ✅ **Short-window adapter DONE (2026-07-16):**
  `window_iff_shift_budgets` converts each short-window maximum into the
  finite budgets through depth `k-1` (episode
  `74fbfc4b-da2f-467c-9d44-d02b6eeb28f4`). Thus the third Formal Conjectures
  `sorry` is isolated to the new-mathematics statement that the survivor set
  is infinite at every fixed depth. Snapshot
  `proof/Erdos647_WindowShiftInterface.lean`.
- ✅ **Formal Conjectures predicate compatibility DONE (2026-07-15):**
  `CandidateBound` is definitionally the same maximum expression; the bounded
  candidate Finsets are extensionally equal, and the global density theorem is
  restated over the exact Formal Conjectures set. Both sides compile in their
  independently pinned toolchains. This fills none of the research-open
  `sorry`s. Snapshot `proof/Erdos647_FormalConjecturesCompatibility.lean`.
- **Growing-depth objective:** seek a function `D(n)→∞` and prove that every
  sufficiently large `n` fails one budget with `k≤D(n)`. A fixed finite list
  of congruences cannot suffice because of the all-avoid obstruction.
- **Direct chain objective:** extend the verified shift classifications beyond
  `1,2,3,4,6,8,12` and force an incompatible factorization. Shift `9` is now
  sharpened: its square branch is impossible; its prime, `3·prime`, and
  `9·prime` branches force exact residue classes modulo `3`, `9`, and `27`.
  This is not a closure: explicit parameters survive shifts `1..9` through the
  `3·prime` branch and first fail at shift `10`. The next useful target is a
  uniform interaction between shifts `9` and `10`, not more bounded census.
- **Witness lane:** use computation only to identify structural patterns or a
  genuine counterexample above the established frontier. Finite absence is
  never presented as eventual nonexistence.

## Track 3 — harden the record

- Stand up a local `LeanChecker`-style replay of the [proof/](proof/)
  snapshots (as erdos-291/-1052 have), removing the "environment is the
  only witness" caveat in evidence.md.
- Formalize the **all-avoid obstruction itself** in Lean (currently prose +
  Hughes's markdown). This would make the campaign's central negative
  result machine-checked too, and sharpen exactly which argument classes
  it excludes.

## Track 4 — upstream

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
