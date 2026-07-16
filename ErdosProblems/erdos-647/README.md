# Erdős #647 — global density theorem verified; existence problem open

**Problem ([erdosproblems.com/647](https://www.erdosproblems.com/647),
Erdős–Selfridge, OPEN):** is there any `n > 24` with
`max_{m<n}(m + τ(m)) ≤ n + 2`?

This folder contains a complete Lean proof of the effective global density
estimate

```text
|C(X)| ≤ K · X / (log X)^7
```

for the bounded set of Erdős #647 candidates, with an explicit constant `K`.
It also contains an independent machine-checked rederivation of the modular
frontier, what we believe is the first machine-checked proof of Hughes's
Theorem 2, the repaired level-truncated Selberg machinery, and the complete
candidate-to-sieve assembly.

**The original problem remains open.** Density zero does not imply emptiness.
The active continuation now targets individual candidates: a kernel-verified
[shift-depth interface](proof/Erdos647_ShiftDepthInterface.lean) reduces
nonexistence to finding one failed budget `σ₀(n-k)>k+2` for each `n>24`.

## Start here

| file | what it is |
|---|---|
| [whitepaper.md](whitepaper.md) | full problem narrative and completed density proof architecture |
| [THEOREM-CATALOG.md](THEOREM-CATALOG.md) | theorem inventory and final assembly map |
| [attack-plan.md](attack-plan.md) | completed density program and remaining existence directions |
| [evidence.md](evidence.md) | tracked episode evidence plus the clean repository replay |
| [dossiers/](dossiers/README.md) | complete 319-episode export archive and indexes |
| [credit.md](credit.md) | attribution, AI disclosure, and honest limits |
| [proof/](proof/) | 172 Lean files containing 456 actual theorem declarations and five helper lemmas (461 theorem/lemma declarations total) |

## Headline results — 2026-07-16

1. **Global seventh-power density theorem.**
   [`boundedCandidates_density_global`](proof/Erdos647_ConcreteAsymptoticDensity.lean)
   proves the displayed bound for every natural `X`. The proof includes the
   bounded candidate `Finset`, exact `n=2520N` reindexing, concrete
   seven-form sieve, truncated optimal weights, polynomial error control,
   denominator growth, dyadic parameters, and finite-range closure.

2. **The analytic obstruction was repaired explicitly.** Hard support
   `d≤R` gives `lambdaSquared(w)(d)=0` above `R²`; the coefficient and
   remainder bounds give `errSum≤(R²+1)^8`. The final seventh-power
   denominator uses an elementary factorial/Euler-product comparison. The
   earlier valid Chebyshev/Mertens theorem has leading coefficient `log 2`
   and is not used to overclaim the exponent.

3. **Hughes's Theorem 2 formalized.** Every candidate lies in one of two exact
   four-prime constellations. The three stages are
   [Stage 1/2](proof/Erdos647_Thm2_Stage12.lean),
   [Stage 4](proof/Erdos647_Thm2_Stage4.lean), and
   [Stage 8](proof/Erdos647_Thm2_Stage8.lean).

4. **Independent frontier replication.** The 41 open residue classes modulo
   46189 were reproduced from scratch using a tighter 48-survivor base sieve,
   with every sieve row derived from a classification theorem.

5. **Forty-eight new sub-AP closures.** This line was deliberately frozen once
   the all-avoid obstruction showed that bounded congruence trees cannot close
   the frontier.

6. **Complete machine export archive.** All 321 related episodes
   are exported in redacted JSON, full Markdown dossier, and structured
   training JSON forms under
   [dossiers/exports/](dossiers/exports/README.md). Of these, 312 report
   `KERNEL_VERIFIED`; the archive deliberately retains three unfinished,
   three gave-up, and one budget-exhausted trajectory for audit completeness.
   The terminal composition is separately identified as a clean source replay
   rather than invented as an additional tracked episode.

7. **Existence campaign has an exact first reduction.**
   [`Erdos647_FiniteBandClosure.lean`](proof/Erdos647_FiniteBandClosure.lean)
   certifies a failed shift for every `25 ≤ n ≤ 84`. Combining this with the
   recovered divisibility theorem gives
   [`candidate_gt84_and_dvd2520`](proof/Erdos647_CandidateStructuralReduction.lean):
   every hypothetical candidate has `84 < n` and `2520 ∣ n`. The same assembly
   places it in one of the two verified four-prime families. This is a strict
   reduction of the open problem, not a solution.

8. **Formal Conjectures predicate compatibility checked.**
   [`Erdos647_FormalConjecturesCompatibility.lean`](proof/Erdos647_FormalConjecturesCompatibility.lean)
   mirrors the exact open-file expression, proves the candidate predicates
   definitionally equivalent, proves the bounded Finsets extensionally equal,
   and restates the density theorem over that exact set. The Formal Conjectures
   module independently compiles the matching API in its own pinned toolchain.
   This compatibility result fills none of its three research-open `sorry`s.

9. **The open variants now have exact interfaces.** The global maximum is
   equivalent to all positive shift budgets, and the short-window maximum is
   equivalent to the corresponding finite set of budgets. Thus the main
   theorem is reduced to producing one failed shift for every `n > 84`, while
   the infinite-window variant is reduced to infinitude of fixed-depth
   survivor sets. Window sizes at most two are now proved unconditionally; the
   first open size, `k=3`, is equivalent to infinitude of Sophie Germain
   primes, including a direct statement over the exact Formal Conjectures
   window expression. The limit variant is exactly an eventual failed-shift
   theorem with arbitrarily large excess. Prime powers prove its sequence is
   unbounded along `n=2^B+1`, but do not prove convergence.

10. **Shift refinement now has a general induction framework.**
    [`Erdos647_ShiftFactorFramework.lean`](proof/Erdos647_ShiftFactorFramework.lean)
    packages the common arithmetic behind every later shift: peel any known
    coprime factor from a divisor-count budget, specialize to a prime power,
    bound the cofactor's number of distinct prime factors, and identify the
    unique next `p`-adic exceptional lift as a congruence class. The
    prime-power peel and modular-lift cores are independently tracked
    `kernel_verified`. Concrete shifts now supply only their affine
    factorization, parity/family information, and the finite enumeration of
    exceptional digits. This is the intended route forward—not an indefinite
    list of unrelated shift calculations.

11. **Shifts 14–16 stress-test the framework.**
    [`Erdos647_Shift14Refined.lean`](proof/Erdos647_Shift14Refined.lean) and
    [`Erdos647_Shift15Refined.lean`](proof/Erdos647_Shift15Refined.lean)
    give tracked 7-adic and 5-adic frontiers. Shift 16 then combines the same
    API with the two prime-chain families and a 2-adic split; its source chain
    compiles and its strongest even-parameter core independently returned
    `kernel_pass`. These are validation cases for the abstraction, not a new
    commitment to advance one shift at a time.

12. **The shift-9/10 closure route was tested and ruled out exactly.** Shift
    10's square branch is impossible and its two remaining branches have exact
    residue restrictions. Nevertheless, the tracked witness
    `N=6,970,590`, `n=17,565,886,800` satisfies every budget through shift 10
    and all seven density forms are prime; it first fails at shift 11. See
    [`Erdos647_Shift910Frontier.lean`](proof/Erdos647_Shift910Frontier.lean)
    and the kernel-verified
    [`Erdos647_Shift10FrontierWitness.lean`](proof/Erdos647_Shift10FrontierWitness.lean).
    A deeper tracked witness
    [`Erdos647_Shift12FrontierWitness.lean`](proof/Erdos647_Shift12FrontierWitness.lean)
    has `N=244,692,464,302`, satisfies **every** budget through shift 12 and
    all seven prime forms, then first fails at shift 13. Any direct closure
    must therefore use a structural induction or a genuinely growing depth.
    The new
    [`Erdos647_Shift13Refined.lean`](proof/Erdos647_Shift13Refined.lean)
    starts that next layer: a hypothetical survivor's shift-13 value has at
    most three distinct prime factors, and its 13-adic branch reduces outside
    one exceptional residue to a cofactor with at most seven divisors.

13. **Every candidate now has an exact finite power-prefix certificate.**
    [`Erdos647_RoughPowerBound.lean`](proof/Erdos647_RoughPowerBound.lean)
    proves `τ(m)^r ≤ m` whenever every prime divisor of `m` is at least
    `2^r`. [`Erdos647_GenericLocalPowerBound.lean`](proof/Erdos647_GenericLocalPowerBound.lean)
    promotes arbitrary verified local prime-power inequalities—using either
    natural constants or exact integral numerator/denominator pairs—to global
    divisor-power bounds. [`Erdos647_GenericPowerPrefix.lean`](proof/Erdos647_GenericPowerPrefix.lean)
    converts any `A·τ(m)^r ≤ C·m` bound into a finite shift-prefix theorem,
    its excess-shift converse, and a certificate for the exact Formal
    Conjectures supremum predicate.

14. **The cube prefix is sharpened by the exact `gcd(k,2520)` class.**
    [`Erdos647_ShiftGcdClass.lean`](proof/Erdos647_ShiftGcdClass.lean)
    proves `gcd(2520N-k,2520)=gcd(k,2520)`.
    [`Erdos647_GcdClassCubeBound.lean`](proof/Erdos647_GcdClassCubeBound.lean)
    then proves `35·τ(2520N-k)^3 ≤ C(k)(2520N-k)`, with the exact normalized
    local constants `(c₂,c₃,c₅,c₇)=(8,3,8/5,8/7)`.

15. **The global shift family is exactly equivalent to an arbitrary-block
    prefix family.**
    [`Erdos647_ArbitraryBlockPowerPrefix.lean`](proof/Erdos647_ArbitraryBlockPowerPrefix.lean)
    gives each positive shift unique coordinates `k=block·q+s`,
    `0<s≤block`, and proves an iff—not merely an implication—between all
    shift budgets and the corresponding local power-prefix cells. Its
    candidate corollary uses the exact Formal Conjectures expression.

16. **Finite prefix checks have an executable, kernel-sound certificate
    format.**
    [`Erdos647_FactorizationCertificate.lean`](proof/Erdos647_FactorizationCertificate.lean)
    checks supplied distinct prime powers, exact products, divisor counts,
    and complete required-shift coverage. A successful batch plus a global
    divisor-power bound certifies the full candidate predicate; Lean checks
    the data instead of trusting an external factorization oracle.

17. **The growing-gauntlet novelty seam is isolated exactly.**
    [`Erdos647_PairwiseCoprimeBlockNovelty.lean`](proof/Erdos647_PairwiseCoprimeBlockNovelty.lean)
    proves that a pairwise-coprime block of values greater than one produces
    one distinct prime per cell, new relative to any avoided finite catalog.
    If those primes all divide a positive host `H`, then
    `2^block.card ≤ H`. Deriving the block and host hypotheses uniformly from
    candidacy remains open.

18. **A fourth-root prefix is now available.**
    [`Erdos647_FourthPowerDivisorBound.lean`](proof/Erdos647_FourthPowerDivisorBound.lean)
    proves `τ(n)^4 ≤ 19680n` for every positive `n`. Consequently, for a
    fixed candidate only shifts satisfying `(k+2)^4 < 19680(n-k)` require
    explicit checking.

19. **The finite prefix is compressed again, and the three bounds are combined.**
    [`Erdos647_FifthPowerDivisorBound.lean`](proof/Erdos647_FifthPowerDivisorBound.lean)
    proves `τ(n)^5 ≤ 147700800n`.
    [`Erdos647_HybridPowerPrefix.lean`](proof/Erdos647_HybridPowerPrefix.lean)
    requires an explicit check only where the sharp cubic, fourth-power, and
    fifth-power tests all remain inconclusive. This is a stronger finite
    certificate for each fixed `n`, not a uniform exclusion.

20. **Every sufficiently large candidate escapes every fixed prime catalog.**
    [`Erdos647_FiniteCatalogEscape.lean`](proof/Erdos647_FiniteCatalogEscape.lean)
    constructs a bounded shift whose value has a prime factor outside any
    prescribed finite catalog; the theorem is stated directly for the Formal
    Conjectures candidate expression. The primorial specialization in
    [`Erdos647_PrimorialCandidateEscape.lean`](proof/Erdos647_PrimorialCandidateEscape.lean)
    produces a prime larger than any fixed cutoff. Thus a hypothetical
    candidate must keep introducing primes; no fixed catalog can contain its
    entire shift structure.

21. **Large-prime non-reuse no longer needs pairwise-coprime shifted values.**
    [`Erdos647_ShiftDifferenceNovelty.lean`](proof/Erdos647_ShiftDifferenceNovelty.lean)
    proves that any common divisor of `n-k₁` and `n-k₂` divides
    `k₂-k₁`. Consequently selected factors larger than a block's width are
    automatically distinct. The smooth-number alternative in
    [`Erdos647_SmoothLargePrimeFactor.lean`](proof/Erdos647_SmoothLargePrimeFactor.lean)
    and its block assembly in
    [`Erdos647_BlockLargePrimeNovelty.lean`](proof/Erdos647_BlockLargePrimeNovelty.lean)
    turn sufficiently large budgeted shifts into an injective family of large
    primes, with the usual exponential bound if a common host is available.

22. **Subset products now feed an exact CRT re-entry certificate.**
    [`Erdos647_PrimeProductDichotomy.lean`](proof/Erdos647_PrimeProductDichotomy.lean)
    and
    [`Erdos647_TSubsetProductDichotomy.lean`](proof/Erdos647_TSubsetProductDichotomy.lean)
    isolate when a product of selected large primes is below `n`.
    [`Erdos647_CRTReentryExclusion.lean`](proof/Erdos647_CRTReentryExclusion.lean)
    then uses `h=n mod ∏Pᵢ` as a new shift and proves the exact candidate
    sandwich `2^|I| ≤ τ(n-h) ≤ h+2`. Hence `h+2<2^|I|` is a
    kernel-checkable non-candidacy certificate.

23. **The no-reentry branch has a conditional second-layer catalog.**
    [`Erdos647_LargePrimeCofactor.lean`](proof/Erdos647_LargePrimeCofactor.lean)
    peels a square-scale prime and transfers the budget to its cofactor.
    [`Erdos647_NonsmoothCofactorException.lean`](proof/Erdos647_NonsmoothCofactorException.lean)
    proves that at most one square-small cofactor can contain a prime larger
    than the block width under the no-cross-product hypothesis. Together with
    [`Erdos647_TwoExceptionalIndices.lean`](proof/Erdos647_TwoExceptionalIndices.lean),
    [`Erdos647_SmoothCofactorBound.lean`](proof/Erdos647_SmoothCofactorBound.lean),
    and
    [`Erdos647_SecondLayerCatalogAssembly.lean`](proof/Erdos647_SecondLayerCatalogAssembly.lean),
    this leaves at least `W-2` controlled, `W`-smooth cofactors satisfying
    `qᵢ≤W^((1+i)/2)`. Cofactor gcd and repetition constraints are recorded in
    [`Erdos647_CofactorGapRigidity.lean`](proof/Erdos647_CofactorGapRigidity.lean).
    This is the current structural frontier, not a contradiction.

24. **Rungs 5, 7, 9, and 10 form a coprimality clique.**
    [`Erdos647_Rung5Rung7Relation.lean`](proof/Erdos647_Rung5Rung7Relation.lean)
    first proves the exact identity `5(504N-1)-7(360N-1)=2`, and
    [`Erdos647_Rung5Rung7Coprime.lean`](proof/Erdos647_Rung5Rung7Coprime.lean)
    combines it with parity. The stronger
    [`Erdos647_RungCofactorsPairwiseCoprime.lean`](proof/Erdos647_RungCofactorsPairwiseCoprime.lean)
    supplies six subtraction-free Bézout identities and proves that
    `504N-1`, `360N-1`, `280N-1`, and `252N-1` are pairwise coprime for
    `N≥1`. Consequently the four shifts always supply four distinct prime
    factors. The same module also proves that the 5-adic escape depths attached
    to rungs 5 and 10 cannot both be positive, deleting their joint exceptional
    branch from the base-gauntlet state space. This is a concrete cross-rung
    non-reuse theorem, but it does not
    yet produce the global failed shift needed to close the existence
    declaration.

## Verification snapshot

- Pinned environment:
  `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- Complete density dependency replay: 42 modules plus
  `proof/campaign/family2-classifications.lean`, exit code 0
- No `sorry`, `admit`, or added axiom in the final assembly
- Portable source contains 456 actual theorem declarations and five top-level
  lemma declarations across 172 Lean files; including 47 definitions (45
  public and two private helpers) gives 508 declarations. These are source
  declarations, not 503 independent tracked discoveries.
- The 2026-07-16 power-prefix/block/certificate batch contains 31 theorem
  declarations in nine modules. Twenty-three roots were independently
  tracked `kernel_verified`; the remaining eight are source-compiled helpers.
- The later large-prime, CRT re-entry, and second-layer continuation contributes
  30 additional tracked roots. Direct proof-search export confirms all 30 are
  `KERNEL_VERIFIED` in the pinned environment; their full, public-summary,
  and training artifacts are included in the 319-episode archive.
- None of these results closes a Formal Conjectures declaration. All three
  research-open `sorry`s remain explicit.
- Generated `.olean` files are not committed

No new witness and no disproof are claimed. What changed is substantial but
logically different: the full `X/(log X)^7` density theorem is now
machine-checked.
