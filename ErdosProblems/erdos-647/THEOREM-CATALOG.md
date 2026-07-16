# Erdős #647 — complete kernel-verified theorem catalog

> **Living inventory. Problem OPEN; global density theorem verified.** Last
> updated 2026-07-16.
>
> This catalogs the kernel-checked and source-replayed theorem families produced by the Erdős
> #647 campaign. The portable source currently has 467 actual theorem
> declarations and five top-level helper lemmas across 178 Lean files (472
> theorem/lemma declarations total). Each tracked row carries the
> `problem_version_id` — the authoritative lookup key in the
> tracked pipeline — plus the exact root statement and, where recorded, the
> statement hash and episode id. **Original Formal Conjectures closure remains
> `0/3`.** Nothing here resolves the open problem; this is the machine-checked
> scaffolding *around* it.
>
> **What is portable vs. internal.** The committed `.lean` files are the
> simplest portable formal artifact: they check against Mathlib without this
> project's database. The repository now also publishes the complete exports
> for all 331 related episodes—redacted public summaries, full
> Markdown proof dossiers, and structured training JSON—under
> [dossiers/exports/](dossiers/exports/README.md). The IDs alone still are not
> an external database API; the committed exports are what makes the audit
> material public.
>
> Full Lean source is in [proof/](proof/), with the five original modular
> families consolidated under [proof/campaign/](proof/campaign/).
> The `root_statement_hash` in each row lets anyone confirm they are checking the
> exact statement claimed.
>
> Pinned environment for the whole campaign:
> `environment_hash = 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`,
> `import_manifest = ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]`.
> Fidelity basis: `unsafe_dev_attestation` → outcomes are `kernel_verified`
> (never "certified" — statements were authored in-project, not imported from a
> neutral catalog). See [credit.md](credit.md) for attribution and limits.

## Final density assembly (repository-level kernel replay)

The campaign now contains a complete source-level composition of the
seven-dimensional upper-bound sieve. This composition was replayed from a
clean state in the pinned environment: 42 transitive campaign modules plus
`proof/campaign/family2-classifications.lean`, exit code 0. It is a repository
kernel replay rather than a single tracked proof-search episode.

| source | role |
|---|---|
| [`proof/Erdos647_ConcreteCandidateBridge.lean`](proof/Erdos647_ConcreteCandidateBridge.lean) | bounded candidate set, large/small split, exact parameter reindexing, survivor bridge |
| [`proof/Erdos647_ConcretePromotedSieve.lean`](proof/Erdos647_ConcretePromotedSieve.lean) | concrete repaired `BoundingSieve` and promoted `SelbergSieve` |
| [`proof/Erdos647_ConcreteR20Density.lean`](proof/Erdos647_ConcreteR20Density.lean) | concrete `R=(2z)^20` candidate-density inequality |
| [`proof/Erdos647_PrimeEulerProductLower.lean`](proof/Erdos647_PrimeEulerProductLower.lean) | elementary harmonic-sum/finite-Euler-product lower bound |
| [`proof/Erdos647_ConcreteDenominatorLower.lean`](proof/Erdos647_ConcreteDenominatorLower.lean) | `(16/77)^7 (log z)^7 ≤ L` for the concrete denominator |
| [`proof/Erdos647_ConcreteR20LogDensity.lean`](proof/Erdos647_ConcreteR20LogDensity.lean) | concrete `X/(log z)^7` estimate |
| [`proof/Erdos647_ConcreteAsymptoticDensity.lean`](proof/Erdos647_ConcreteAsymptoticDensity.lean) | dyadic parameter assembly, explicit large-range bound, and global finite-range closure |
| [`proof/Erdos647_FormalConjecturesCompatibility.lean`](proof/Erdos647_FormalConjecturesCompatibility.lean) | exact predicate/Finset compatibility and density restatement for the Formal Conjectures expression |
| [`proof/Erdos647_ShiftDepthInterface.lean`](proof/Erdos647_ShiftDepthInterface.lean) | post-density existence interface: global maximum implies every shift budget; one failure excludes candidacy |
| [`proof/Erdos647_FiniteBandClosure.lean`](proof/Erdos647_FiniteBandClosure.lean) | exact failed-shift certificate for every `25 ≤ n ≤ 84` |
| [`proof/Erdos647_CandidateStructuralReduction.lean`](proof/Erdos647_CandidateStructuralReduction.lean) | every candidate is above `84`, divisible by `2520`, and in one of the two four-prime families |
| [`proof/Erdos647_WindowShiftInterface.lean`](proof/Erdos647_WindowShiftInterface.lean) | exact short-window / fixed-depth-shift equivalence for the infinite-window variant |
| [`proof/Erdos647_Shift9Refined.lean`](proof/Erdos647_Shift9Refined.lean) | removes the shift-9 square branch and attaches exact residue restrictions |
| [`proof/Erdos647_Shift910Frontier.lean`](proof/Erdos647_Shift910Frontier.lean) | exact two-family × shift-9 × shift-10 residue/parity frontier |
| [`proof/Erdos647_Shift10FrontierWitness.lean`](proof/Erdos647_Shift10FrontierWitness.lean) | exact seven-prime witness surviving shifts 1–10 and failing shift 11 |
| [`proof/Erdos647_Shift12FrontierWitness.lean`](proof/Erdos647_Shift12FrontierWitness.lean) | exact seven-prime witness surviving shifts 1–12 and failing shift 13 |
| [`proof/Erdos647_Shift13Refined.lean`](proof/Erdos647_Shift13Refined.lean) | prime-factor-cardinality and first 13-adic refinement of the shift-13 branch |
| [`proof/Erdos647_ShiftFactorFramework.lean`](proof/Erdos647_ShiftFactorFramework.lean) | generic coprime/prime-power budget peel, cofactor prime-factor bound, and next-adic modular lift |
| [`proof/Erdos647_Shift14Refined.lean`](proof/Erdos647_Shift14Refined.lean) | exact two-layer 7-adic stress test of the generic framework |
| [`proof/Erdos647_Shift15Refined.lean`](proof/Erdos647_Shift15Refined.lean) | exact two-layer 5-adic stress test, with one residual class modulo 125 |
| [`proof/Erdos647_Shift16Refined.lean`](proof/Erdos647_Shift16Refined.lean) | family-sensitive 2-adic stress test and explicit residual branch |
| [`proof/Erdos647_LimitShiftInterface.lean`](proof/Erdos647_LimitShiftInterface.lean) | exact eventual-shift-excess form of the limit variant, plus an unbounded prime-power subsequence |
| [`proof/Erdos647_InfiniteWindowFrontier.lean`](proof/Erdos647_InfiniteWindowFrontier.lean) | unconditional window depths below two and exact depth-two/Sophie-Germain infinitude equivalence |
| [`proof/Erdos647_RoughPowerBound.lean`](proof/Erdos647_RoughPowerBound.lean) | generic rough `r`-power divisor bound |
| [`proof/Erdos647_GenericLocalPowerBound.lean`](proof/Erdos647_GenericLocalPowerBound.lean) | generic local constants and exact finite numerator/denominator products |
| [`proof/Erdos647_GenericPowerPrefix.lean`](proof/Erdos647_GenericPowerPrefix.lean) | generic prefix, excess-shift converse, and exact candidate bridge |
| [`proof/Erdos647_ShiftGcdClass.lean`](proof/Erdos647_ShiftGcdClass.lean) | exact transport of the `2520` gcd class from `k` to `2520N-k` |
| [`proof/Erdos647_GcdClassCubeBound.lean`](proof/Erdos647_GcdClassCubeBound.lean) | exact class-sensitive cube bound and candidate prefix |
| [`proof/Erdos647_ArbitraryBlockPowerPrefix.lean`](proof/Erdos647_ArbitraryBlockPowerPrefix.lean) | exact arbitrary-block prefix equivalence and coordinate injectivity |
| [`proof/Erdos647_FactorizationCertificate.lean`](proof/Erdos647_FactorizationCertificate.lean) | executable factorization/batch checker and end-to-end candidate soundness |
| [`proof/Erdos647_PairwiseCoprimeBlockNovelty.lean`](proof/Erdos647_PairwiseCoprimeBlockNovelty.lean) | conditional prime novelty and shared-host exponential bound |
| [`proof/Erdos647_FourthPowerDivisorBound.lean`](proof/Erdos647_FourthPowerDivisorBound.lean) | `τ(n)^4≤19680n` and fourth-root candidate prefix |
| [`proof/Erdos647_FifthPowerDivisorBound.lean`](proof/Erdos647_FifthPowerDivisorBound.lean) | `τ(n)^5≤147700800n` and fifth-root candidate prefix |
| [`proof/Erdos647_HybridPowerPrefix.lean`](proof/Erdos647_HybridPowerPrefix.lean) | hybrid cube/fourth/fifth-power prefix assembled directly over the candidate predicate |
| [`proof/Erdos647_SmoothLargePrimeFactor.lean`](proof/Erdos647_SmoothLargePrimeFactor.lean) | smooth-number power bound and extraction of a prime factor larger than the block width |
| [`proof/Erdos647_ShiftDifferenceNovelty.lean`](proof/Erdos647_ShiftDifferenceNovelty.lean) | exact shift-gap gcd transport, large-factor non-reuse, injectivity, and shared-host growth |
| [`proof/Erdos647_BlockLargePrimeNovelty.lean`](proof/Erdos647_BlockLargePrimeNovelty.lean) | block budgets plus smoothness escape produce distinct large primes |
| [`proof/Erdos647_FiniteCatalogEscape.lean`](proof/Erdos647_FiniteCatalogEscape.lean) | every sufficiently large exact candidate escapes any fixed finite prime catalog |
| [`proof/Erdos647_PrimorialCandidateEscape.lean`](proof/Erdos647_PrimorialCandidateEscape.lean) | primorial specialization of finite-catalog escape with the matching shift budget |
| [`proof/Erdos647_PrimeProductDichotomy.lean`](proof/Erdos647_PrimeProductDichotomy.lean) | pair-product re-entry or at most one square-small coordinate |
| [`proof/Erdos647_TSubsetProductDichotomy.lean`](proof/Erdos647_TSubsetProductDichotomy.lean) | general `t`-subset product re-entry or fewer than `t` power-small coordinates |
| [`proof/Erdos647_CRTReentryExclusion.lean`](proof/Erdos647_CRTReentryExclusion.lean) | CRT remainder re-entry, divisor-count sandwich, and exact candidate exclusion certificate |
| [`proof/Erdos647_LargePrimeCofactor.lean`](proof/Erdos647_LargePrimeCofactor.lean) | square/power-scale large-prime cofactor reduction and shifted divisor budget |
| [`proof/Erdos647_CofactorGapRigidity.lean`](proof/Erdos647_CofactorGapRigidity.lean) | cofactor gcds and repeated odd cofactors are rigidly bounded by shift gaps |
| [`proof/Erdos647_CofactorLargePrimeNovelty.lean`](proof/Erdos647_CofactorLargePrimeNovelty.lean) | second-layer primes larger than the block width are distinct across cofactors |
| [`proof/Erdos647_SmoothCofactorBound.lean`](proof/Erdos647_SmoothCofactorBound.lean) | explicit size bound for a smooth cofactor under its doubled divisor budget |
| [`proof/Erdos647_NonsmoothCofactorException.lean`](proof/Erdos647_NonsmoothCofactorException.lean) | at most one square-small cofactor can carry a new large prime under no-cross-pair exclusion |
| [`proof/Erdos647_TwoExceptionalIndices.lean`](proof/Erdos647_TwoExceptionalIndices.lean) | deleting the two one-element exceptional catalogs leaves at least `W−2` indices |
| [`proof/Erdos647_SecondLayerCatalogAssembly.lean`](proof/Erdos647_SecondLayerCatalogAssembly.lean) | conditional assembly of a `W−2`-sized catalog of controlled smooth cofactors |

Terminal statement:

```lean
theorem boundedCandidates_density_global (X : ℕ) :
    ((boundedCandidates X).card : ℝ) ≤
      globalDensityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7
```

The earlier quantitative Mertens theorem remains valid infrastructure, but
its available leading coefficient is `log 2`, so it is not used to claim the
seventh-power denominator. The final proof obtains that exponent through the
factorial/Euler-product argument above. The density result does not resolve
existence or nonexistence of a larger candidate.

## Proof-source coverage & full episode index

**The portable, publicly-verifiable artifact is the committed Lean source**, not
any id. Anyone can check a committed `.lean` file against Mathlib with `lake` —
no access to this project's database required.

Committed Lean source:

- 178 `.lean` files under [proof/](proof/), containing 467 actual theorem
  declarations and five top-level helper lemmas (472 declarations total).
- Five consolidated modular families under
  [proof/campaign/](proof/campaign/), plus individual analytic, truncation,
  candidate-transport, and final-assembly modules in the parent directory.

Export and reproduction material:

- [dossiers/episode-index.tsv](dossiers/episode-index.tsv) maps all 331 related
  problem/episode pairs.
- [dossiers/exports/manifest.tsv](dossiers/exports/manifest.tsv) records the
  outcome, fidelity, environment, statement hash, timestamps, and step count.
- [dossiers/exports/](dossiers/exports/README.md) contains all three export
  formats for every episode.

## Tally by family

| # | Family | Count | What it establishes |
|---|---|---|---|
| 1 | Sieve counting certificates | 9 | the mod-46189 survivor count (48) + 6 CRT refinement tiers + the 45-class frontier, as kernel-checked `Finset` cardinalities |
| 2 | Shift classification theorems | 14 | for each shift `k`, any candidate forces `(n−k)/k` into an explicit prime / prime-power / small-multiple form |
| 3 | Bridging-closure theorems | ~26 | each sieve row *derived from* its classification theorem — the sieve is proven, not just computed |
| 4 | Residue closures (frontier 45→41) | 4 | four of the open residue classes closed unconditionally (direct-full-value + single-overlap) |
| 5 | Novel sub-AP congruence closures | 48 | original-search sub-cell closures (mod 46189·p), unconditional for all N; 37 enumerated below with full data |
| 6 | Theorem 2 (prime-chain reduction) | 3 | first machine-checked proof: every candidate is `8s+8` or `16s+8` with four forced primes |
| 7 | Layer A (quantitative-Mertens infra) | 5 | Abel-summation identity and explicit analytic bounds; valid infrastructure, though the final seventh-power proof uses the stronger Euler-product route |
| 8 | Level-truncated Selberg repair and assembly | 36 | hard support, polynomial error, denominator preservation, parameter certification, and concrete candidate transport |
| 9 | Post-density existence and variant frontier | 49 | generic shift-factor/adic induction, shifts 9–16 as concrete frontiers and stress tests, exact depth witnesses, the eventual-excess limit interface, and the depth-two/Sophie-Germain equivalence |
| 10 | Power-prefix, block, and certificate architecture | 31 | arbitrary-power local-factor products, exact block reindexing, executable factorization batches, fourth-root compression, and the conditional novelty/shared-host seam |
| 11 | Large-factor novelty, CRT re-entry, and second-layer catalogs | 69 | fifth/hybrid prefix compression, finite-catalog escape, `t`-subset product alternatives, CRT exclusion, the conditional smooth-cofactor catalog, and the four-rung clique with a sharp depth-five candidate boundary |
| | **Selected-family subtotal** | **not additive** | The exact repository-wide count is 472 theorem/lemma declarations; family rows are publication groupings and may overlap. |

---

## Family 1 — sieve counting certificates

Kernel-verified `native_decide` cardinalities. The base sieve (48 survivors
of `Finset.range 46189`) is tighter than the published 96-survivor sieve; each
refinement multiplies the survivor count by the prime tier via CRT.

| problem_version_id | statement (abbrev.) | value |
|---|---|---|
| `200bce1c` | `((Finset.range 46189).filter <13-coeff sieve × {11,13,17,19}>).card` | 48 |
| `a001e7c1` | refined to prime 23, over `Finset.range 1062347` | 528 = 48×11 |
| `4d2b7ec1` | refined to prime 29, over `Finset.range 1339481` | 768 = 48×16 |
| `83fb9810-de02-4278-943e-60335ffc1bb5` | refined to prime 31, over `Finset.range 1431859` | 864 = 48×18 |
| `b4196b16-744d-4785-8120-65810da7d73c` | refined to prime 37, over `Finset.range 1708993` | 1152 = 48×24 |
| `2f28d8d4-2f9f-413c-8d4e-408196b7b59d` | refined to prime 41, over `Finset.range 1893749` | 1344 = 48×28 |
| `c0f6a321-8b28-47c8-9aed-dbc735171c73` | refined to prime 43, over `Finset.range 1986127` | 1440 = 48×30 |
| `b9083710` | `((Finset.range 46189).filter <base ∧ 180-row ∧ 3 pair-exclusions>).card` — the mod-46189 open frontier | 45 |
| `9da16855` | base-48 explicit residue set (used to reconstruct the open list) | — |

The 23/29/31/37/41/43 tiers compose by CRT: combined mod-46189·23·29·31·37·41·43
frontier = 48·11·16·18·24·28·30.

---

## Family 2 — shift classification theorems

For each shift `k ∣ 2520` (plus the reusable characterization lemma), a
necessary condition on any Erdős-647 candidate. Proof template: shift-bound
extraction (`BddAbove`/`ciSup`) + a `p`-adic decomposition of `n−k` +
`isMultiplicative_sigma.map_mul_of_coprime`.

| problem_version_id | shift | forced form of `(n−k)/k` |
|---|---|---|
| `fb7d4bf8` | — | characterization lemma: `2≤r → σ₀ r ≤ 3 → r prime ∨ r = p²` (reusable) |
| `00cfc756` | 1 | `n−1` prime ∨ p² |
| `87ea1d9a` | 2 | prime |
| `323c4801` | 3 | prime (Kitamura's condition) |
| `14a21b69` | 4 | prime |
| `e4397627` | 5 | prime ∨ p² ∨ 5·prime |
| `245e963a` | 6 | prime |
| `0f8dcd94` | 8 | prime ∨ 2·prime |
| `8ed738c7` | 9 | prime ∨ p² ∨ 3·prime ∨ 9·prime |
| `6c5dcfd9` | 10 | prime ∨ p² ∨ 5·prime |
| `b9c90e1d` | 12 | prime |
| `1710efdc-06be-413b-a278-ccac732b032c` | 18 | prime ∨ p² ∨ 3·prime ∨ 9·prime |
| `5a643568-2af3-4bbd-a435-af77a4d0d7e1` | 20 | prime ∨ p² ∨ 5·prime ∨ **exactly 125** (genuine exception at n=2520) |
| `5df5a27e-8f13-47b1-93ab-f7c4bc2ec94b` | 24 | prime ∨ p² ∨ 2·prime ∨ 4·prime |

(Original shift-5 problem `dbd105e7` was found malformed — its budget cannot
force the stated conclusion — and is permanently retired; `e4397627` is the
corrected replacement. The prime-chain base {1,2,3,4,6} being all-prime is what
Theorem 2, Family 6, builds on.)

---

## Family 3 — bridging-closure theorems

Each proves a *sieve row* directly from its classification theorem
(`∀ n N ℓ, … → coeff·N % ℓ ≠ 1`), so the modular reduction rests on proofs, not
on trusting a `native_decide` predicate count. Proven at two bounds: `ℓ ≤ 19`
(legacy) and `ℓ ≤ 29` (current, subsuming, and backing the 23/29 refinement
tiers).

**ℓ ≤ 19 (8):** `de35e7ec` (coeff-2520), `8a65bb51` (1260), `dfb82405` (840),
`ddc951c3` (630), `c0565e84` (420), `efc75f5f` (315), `b542e676` (280),
`a62e9824` (252).

**ℓ ≤ 29 (13):** `90c306f4`, `3aa31e38`, `7f68e7f0`, `e6345707`, `c3337705`
(pure-prime coeffs 2520/1260/840/630/420); `ec6ecc6a`, `9bd67f4d`, `5ba4356c`
(near-prime 315/280/252); `84df59dc` (coeff-210, shift-12);
`b1b996c8-f277-466a-b0ae-991d30979e72` (coeff-105, shift-24);
`b0d5b386-efb0-4e05-b949-1d03f1731356` (coeff-140, shift-18);
`9c93a1d6-97b9-49f8-a05f-a0d813a1428d` (coeff-126, shift-20);
`7e6d5dde` (coeff-504, shift-5).

Every kernel-verified shift classification (1,2,3,4,5,6,8,9,10,12,18,20,24) now
has its sieve row backed by a genuine bridging-closure proof.

---

## Family 4 — residue closures (frontier 45 → 41)

Four of the open mod-46189 residue classes closed unconditionally, matching
Hughes's own 41-class frontier, re-derived and re-proven fresh here.

| problem_version_id | residue `N ≡` (mod 46189) | technique |
|---|---|---|
| `e8e7b8cd-2383-4225-ba89-f96c4534d903` | 39325 | direct-full-value (modulus 2584=2³·17·19, k=16) |
| `15bdd8f4-d89b-49df-a075-4ac84348d87b` | 41470 | single-overlap (modulus 3553=11·17·19, k=11; first `ZMod 8` argument) |
| `49ae1aa9-8f21-4c23-8f93-f37b447bba05` | 40612 | single-overlap (modulus 4199=13·17·19, k=13) |
| `fa7e0a1f-446a-4d01-8074-e7f12ff43ece` | 26884 | single-overlap (modulus 14535=3²·5·17·19, k=45, 11-leaf tree, ~400 lines, passed cold) |

---

## Family 5 — novel sub-AP congruence closures

Original-search sub-cell closures: each excludes `N ≡ r (mod 46189·p)` for one
extra prime `p ∈ {23,29,31,37,41,43}`, **unconditionally for all N** (Hughes's
"6549 sub-AP" species, independently discovered against our own frontier). All
of the form `∀ n N, 84 < n → shift-bound ≤ n+2 → n = 2520N → N % <modulus> = r → False`.
These are sub-cell closures — they do **not** shrink the base-46189 41-class
count (only Family 4 does). 48 total; 37 enumerated here with full data (moduli:
1062347=46189·23, 1339481=46189·29, 1431859=46189·31, 1708993=46189·37,
1893749=46189·41, 1986127=46189·43).

| problem_version_id | modulus | residue r | statement_hash |
|---|---|---|---|
| `9eb4d9b1-2edc-402a-84b9-80c85c27d11a` | 1431859 | 29601 | `c179f131…` |
| `ab996bb5-d9ce-463c-bdb2-fd7b2f4cab1c` | 1062347 | 10582 | `9c952feb…` |
| `294db365-edcd-4c8a-8f4a-cf7ac89895c1` | 1339481 | 32032 | `f3db25fa…` |
| `13cf46f3-13a5-40d9-b8a6-b010eefcab3b` | 1062347 | 24310 | `9c5678c1…` |
| `f11c6255-c5f9-4e95-aa97-63afa2c0e7b3` | 1708993 | 2574 | `d683c8de…` |
| `1308a898-34ac-4444-bc00-f061a876db3f` | 1062347 | 1287 | `1287a14f…` |
| `9477f6c0-a2be-4837-acbf-0b9a1cd60504` | 1431859 | 32461 | `bf122e74…` |
| `664b8f85-f684-405a-86dc-6f5242286163` | 1339481 | 28457 | `b9dc13d1…` |
| `8f7fc915-07d0-4171-9881-02872e14ca51` | 1431859 | 28028 | `8d461524…` |
| `7783f62a-9235-4e77-994e-ea1038abaa44` | 1339481 | 24310 | `4b4c36f4…` |
| `e2c9f240-2206-419e-820f-ee44cefa3c4e` | 1062347 | 18733 | `9f1b9190…` |
| `28152863-aeff-42ba-956f-7bf6d4c4fe2a` | 1708993 | 17160 | `684daf31…` |
| `30251d63-ac66-4c98-bf91-9718ace76a80` | 1062347 | 12155 | `a4f5583f…` |
| `13709089-8e64-4f50-81cd-6bd58c30586e` | 1893749 | 4862 | `b1dcffe5…` |
| `e9718f9f-9f2b-40a3-9f6e-31ba71506eca` | 1708993 | 1287 | `4c197004…` |
| `90b3cc66-f603-4e1a-8f1f-2dc5c71bd7d0` | 1062347 | 17017 | `748d2514…` |
| `2b72c7ce-18ff-4e6b-bc1d-874d054815d6` | 1339481 | 9009 | `1781ba1d…` |
| `e4cc4dbf-224c-4b40-aec1-890ffe4ebbed` | 1986127 | 13013 | `5b165a6f…` |
| `6fbb46d1-4dd4-4546-9239-181867d6f2fd` | 1062347 | 44187 | `d7a78f38…` |
| `b374b2c1-4b3d-428b-8c37-2e97999feb95` | 1062347 | 24453 | `cac30a64…` |
| `023da32c-dd05-40eb-a7db-91a57910529e` | 1062347 | 21164 | `d915c762…` |
| `9dc80f26-a25f-4e19-b4ae-e86651849fef` | 1893749 | 18733 | `a2638963…` |
| `97992573-31bf-4f3a-8e14-a2e46be3ed57` | 1339481 | 12584 | `1df1a8d1…` |
| `04f9df4b-c6d8-42ee-a033-be5080fc14cf` | 1431859 | 10582 | `3b18811c…` |
| `c5812bfb-b227-47c7-8288-78447cf9eb9f` | 1431859 | 6149 | `8bb7ad7a…` |
| `9fd6bd75-4c14-431c-aed4-51d45d1fcb84` | 1431859 | 1716 | `aa784b85…` |
| `40ffae3f-bd5a-4689-b0fd-dd0159395459` | 1986127 | 36608 | `3cf46364…` |
| `5de45935-3e0e-4b4e-97cc-204e7e4dd684` | 1986127 | 24310 | `85143702…` |
| `6abe383e-9487-42ab-8e4f-cdce2297921e` | 1339481 | 18733 | `82f6b86a…` |
| `79dd3f80-370f-4845-af21-5d9cdb231b9b` | 1062347 | 17160 | `cb883b6d…` |
| `1c3943cc-8275-4ec3-876b-d8afb8f9a984` | 1431859 | 5291 | `7b65ad9a…` |
| `ec4c6432-4e72-49ca-a1bb-cf6b9ad65aa3` | 1062347 | 37752 | `b0ef5801…` |
| `c8536661-ba27-42be-92f5-1dbd8d2e8b07` | 1431859 | 31603 | `4c3c83dc…` |
| `a0b6d6ba-a7c2-4cfc-b0d0-ae4f9759766a` | 1708993 | 28028 | `ecd24886…` |
| `727c78de-d147-4509-951d-8d2da6f25638` | 1986127 | 20306 | `19bd4868…` |
| `8f5efd8d-77c2-415a-bdb2-07f832fc414c` | 1062347 | 8151 | `9b784a8a…` |
| `9a615fba-bb1c-4fba-ad67-b78c3dccdaf9` | 1339481 | 35321 | `1c3438a4…` |

Earlier wave-1 sub-AP closures (not re-listed above with full hashes; recorded
in the campaign ledger): `3f98ba86` (5291/×23), `d037ea2a` (36608/×23),
`a109a5af` (13442/×29), `4b799f58` (24453/×29), `02d5a4a3` (9009/×43),
`40988498` (18733/×37, the k=7 discovery closure), and the F-wave
`82b78dec`/`1a283efe`/`32706bae`/`61612470`/`0822d882`. Full residue/modulus
data for any of these is recoverable via `problem_list` or `proof_export`.

**Structural note (proven, not just observed):** these closures — and the whole
congruence-tree technique — provably cannot resolve the 41-class frontier, by
Hughes's "all-avoid obstruction" (each (shift, prime) pair excludes ≤ 1 residue
class mod p; CRT recombines survivors). This campaign extended that negative
result to Theorem 2's prime-chain forms as well. See
[whitepaper.md](whitepaper.md) §3.2 and §3.4.

---

## Family 6 — Theorem 2 (prime-chain reduction)

First machine-checked proof of Hughes's Theorem 2 (paper-sketch only, absent
from his Lean tree). Three composable stages; chaining them gives the two
admissible 4-prime constellations. Full snapshots in [proof/](proof/);
legacy headline summaries in
[dossiers/public-summaries.md](dossiers/public-summaries.md), with the complete
archive under [dossiers/exports/](dossiers/exports/README.md).

| problem_version_id | statement | hash |
|---|---|---|
| `1987e20c-6d03-4882-8c20-d0495744d9e9` | `∀ n, 24<n → σ₀(n−1)≤3 → σ₀(n−2)≤4 → ∃ q, q.Prime ∧ n=2q+2 ∧ (n−1).Prime` | `4b5752c6…` |
| `52ff69c0-e7f5-443c-9cc1-14da17c92dd4` | `∀ q, 13≤q → q.Prime → (2q+1).Prime → σ₀(2q−2)≤6 → ∃ p, p.Prime ∧ q=2p+1` | `f940625c…` |
| `513c65fa-b031-479b-aa97-7d39091e7587` | `∀ p, 7≤p → p.Prime → (2p+1).Prime → σ₀(4p−4)≤10 → ∃ s, s.Prime ∧ (p=2s+1 ∨ p=4s+1)` | `068b74eb…` |

Chained: **family A** `n=8s+8` with `s, 2s+1, 4s+3, 8s+7` all prime; **family B**
`n=16s+8` with `s, 4s+1, 8s+3, 16s+7` all prime.

---

## Family 7 — Layer A (quantitative-Mertens infrastructure)

Toward a machine-checked Brun/Selberg-sieve density bound (`|C(x)| ≪ x/(log x)⁷`).
Mathlib has the Selberg sieve core but no quantitative Mertens theorem; this
family builds it. Full snapshots are in [proof/](proof/); the complete episode
archive is in [dossiers/exports/](dossiers/exports/README.md).

| problem_version_id | statement | hash |
|---|---|---|
| `d584666d-e50d-488d-b459-5d1265a3aadd` | Mertens identity: `∑_{p≤x} 1/p = θ(x)/(x log x) + ∫_{(2,x]} (log t+1)/(t²log²t)·θ(t)` | `9802976a…` |
| `781d4876-55c9-4c3c-9420-602b508771be` | main-term antiderivative: `∫_2^x (log t+1)/(t log²t) = (loglog x − 1/log x) − (loglog 2 − 1/log 2)` | `513062ca…` |
| `1fc1ab2d-de49-4660-8d7c-8aefeb853a73` | weight integral: `∫_2^x (log t+1)/(t²log²t) = 1/(2log2) − 1/(x log x)` | `a9a3ca28…` |
| `89b0e678-f69b-427d-9e71-9523856a7cab` | power-law comparison: `∫_2^x t⁻² = 1/2 − 1/x` | `cd03a308…` |
| `8bf294a3-c882-4588-9894-e2fbc8ee0edf` | log(t+2) error bound: `∫_2^x (log t+1)log(t+2)/(t²log²t) ≤ 1 + 1/log2` (first analytic inequality) | `935fe429…` |

**In progress** (see [attack-plan.md](attack-plan.md)): the `2√t·log t` error
bound, then assembly into `∑_{p≤x} 1/p ≥ log2·loglog x − C`; then Layers B
(Selberg optimization) and C (7-tuple application).

---

## Family 8 — level-truncated Selberg repair

This family repairs the error-term defect caused by Mathlib's vestigial
`SelbergSieve.level`: the campaign now constructs a genuinely supported weight,
rather than summing an unrestricted error over every divisor of the primorial.

| problem_version_id | statement | hash |
|---|---|---|
| `4fad80bd-e331-441f-bf57-4c6aed41c4aa` | `∀ s R, 1≤R → ∃ w, w 1=1 ∧ (∀d, R<d → w d=0) ∧ mainSum(lambdaSquared w)=1/∑_{l∣prodPrimes,l≤R}selbergTerms(l)` | `4f1a4ce8…` |
| `481f490b-672c-4b2a-9f08-f630a371c606` | same supported optimal weight, strengthened with `∀d∣prodPrimes, |w d|≤selbergTerms(d)/ν(d)` | `594f3ced…` |
| `fe23498c-ad0b-4c9a-97e1-93e38a1c32b2` | pointwise weight bound + prime factor bound `≤4` imply `|lambdaSquared(w)(d)|≤16^ω(d)` | `71060def…` |
| `684cb8cf-bf0c-44e2-abec-7d0b7a0f5f28` | hard support plus `16^ω(d)`/`7^ω(d)` bounds imply `errSum≤(R²+1)^8` | `3c1e46fb…` |
| `34305a84-6663-460a-a0e8-006337c85838` | Abel identity `∑_{p≤x}log(p)/p=θ(x)/x+∫θ(t)/t²` | `a35ce467…` |
| `b6aa3391-d6b7-4f3b-bc08-9a73261ecf4d` | `∑_{p≤x}log(p)/p≤log(4)(1+log(x/2))` | `ff777997…` |
| `e8710139-6736-43ff-a7d3-efa7a852e365` | `∑ν(p)log p≤log(R)/2 → L_R≥L/2` | `2ccac8ea…` |
| `d6c321da-fb33-46c9-b1eb-114a339d01b8` | `z≥2 → 7log(4)(1+log(z/2))≤log((2z)^20)/2` | `7ed86d0c…` |
| `c64e7c8d-088b-4dc2-814f-a98bebd7dd7c` | `z≥1 → ((((2z)^20)^2+1)^8)≤2^328·z^320` | `1f78e550…` |
| `9f1f4f3c-7665-4fc6-8d71-0a6120ae145e` | `X≠0 → ∃k, (2^k)^400≤X<(2·2^k)^400` | `cfe2b3be…` |
| `3544e7da-c8a9-4feb-844f-91be241dee92` | `E≤2^328z^320 ∧ z^400≤X → E^5≤2^1640X^4` | `c02c2ab4…` |
| `e74ace30-3fd0-4192-aea1-1f0f348f6e9b` | `(2^k)^400≤X ∧ E≤2^328(2^k)^320 → E·k^7≤2^328X` | `7a390489…` |
| `23d21971-6676-40d0-99cb-556e22be189b` | `k>0 ∧ E·k^7≤2^328X → E≤2^328(log2)^7X/(log(2^k))^7` | `1d46a1c9…` |
| `372fc2d3-227e-4104-ac93-6657f6fd8538` | `mainSum=1/L_R ∧ L_R≥L/2 ∧ errSum≤(R²+1)^8 → siftedSum≤2M/L+(R²+1)^8` | `2670a2ea…` |
| `6a01ac1e-442e-4f1b-a2d8-dc4935d8cfd1` | exposed two-parameter seven-form `BoundingSieve` witness with exact support/prodPrimes/weights/totalMass/nu fields | `30424491…` |
| `640009dd-0b98-48b7-930a-c83c6e19c8ae` | exposed support and unit weights imply `s.multSum(d)` equals the raw seven-form filter count | `148469e0…` |
| `874897f7-1348-4cd2-ab74-bbc93ebb2920` | exposed fields and concrete `nu(d)` rewrite `s.rem(d)` to the raw remainder | `c9b20538…` |
| `21676a9b-32f0-497b-a903-cacd52211606` | for squarefree `d`, exposed `prodPrimeFactors` density equals the raw CRT density | `a0d0f134…` |
| `776de7d6-9710-427e-a3fe-29ad9be73f50` | raw remainder/root-count bounds plus exposed fields imply `|s.rem(d)|≤7^ω(d)` | `dad741f9…` |
| `dd9707c4-da49-47f6-8c3f-223bd9fef756` | exposed support and unit weights identify `s.siftedSum` with the exact seven-form coprime survivor count | `f689cbc5…` |
| `8057d050-084d-49ef-8be3-91be624a6e36` | for `z≥2`, every odd `N` is rejected by the original active prime `2` | `318baf88…` |
| `96815907-c5f3-4be5-9e6b-15b1812c118d` | finite-prime rebase constructs the same concrete sieve with `2,3,5,7` excluded | `0dd01bfe…` |
| `3821e6ae-7ce0-40eb-913e-1a39e33e62b7` | any bounded coprime candidate Finset has real cardinality at most `s.siftedSum` | `6ef9f3e6…` |
| `d1d08312-eea8-443a-9ff2-78f6c63d0014` | six prime forms plus the shift-8 `prime ∨ 2·prime` branch and `z<157N` imply coprimality with the repaired modulus | `3d8f14ca…` |
| `cc5eabec-9ba7-4b38-9f8a-482998d707af` | the exceptional parameter band `157N≤z` inside `[1,X]` has cardinality at most `z` | `fd551191…` |
| `20e17129-58dd-46aa-9a9f-d35e0d97c96b` | candidate coprimality for `z<157N` plus the exact survivor audit imply `C.card≤siftedSum+z` | `091284a0…` |
| `7851c193-5d39-4302-a93f-a474a2ffa6c8` | concrete density values are `ν(2)=1/2` and `ν(3)=ν(5)=ν(7)=0` | `057a47bc…` |
| `35439d12-2f15-43bd-81ce-2eabea637710` | deleting `2,3,5,7` changes the prime `ν` sum by exactly `1/2` | `7a62fdd6…` |
| `dd157db4-78e2-4285-8069-b6ce4ee14526` | prime factors of the repaired modulus equal its defining active-prime Finset exactly | `efe8ee4f…` |
| `ce61fdf7-5644-428c-a1ac-f3c7b3b9a5e1` | an all-prime lower bound `B` implies repaired Euler-product `log L≥B−1/2` | `090c8da3…` |
| `e84e00c6-17b8-43e4-a832-b40909cb576a` | shift outputs at `1,2,3,4,6,8,12` under `n=2520N` imply the exact seven-form primality bundle | `2fbfb68c…` |
| `a1095c68-7d6f-4e6a-91ad-894d73d35863` | every `BoundingSieve` promotes to a definitionally identical `SelbergSieve` at any natural level `R≥1` | `fcaef0ed…` |
| `04896a5d-4423-44dc-ac03-424f8fba0689` | `C.card≤siftedSum+z`, `totalMass=X`, and the two-parameter sieve bound imply `C.card≤2X/L+(R²+1)^8+z` | `185531de…` |
| `9ad9f4e4-11d4-4f40-89f9-39c3c990b7fa` | direct candidate-density assembly from main-sum, half-denominator, and polynomial-error hypotheses | `c15e88b4…` |
| `5570a9ac-16d7-42ad-9c06-7a2a16e5d30d` | shift outputs at `1,2,3,4,6,8,12` imply coprimality with the parity-repaired seven-form modulus | `243afd8a…` |
| `74892f8f-6612-4031-a686-23ba5be359dd` | exact predicate-generic reindexing from bounded `n` with `2520∣n` to bounded seven-form parameters `N` | `106d8dda…` |

Snapshots: [truncated weight](proof/Erdos647_SelbergOptimalWeightTruncated.lean),
[strengthened weight](proof/Erdos647_SelbergOptimalWeightTruncatedBound.lean),
[lambda coefficient](proof/Erdos647_LambdaSquaredCardBound.lean),
[polynomial errSum](proof/Erdos647_ErrSumTruncatedPolynomial.lean),
[prime moment identity](proof/Erdos647_PrimeLogDivIdentity.lean), and
[prime moment upper bound](proof/Erdos647_PrimeLogDivUpper.lean), and
[half-denominator bound](proof/Erdos647_SelbergLTruncatedGeHalf.lean), and
[R=(2z)^20 moment certification](proof/Erdos647_ParameterR20Moment.lean), and
[explicit polynomial error](proof/Erdos647_ParameterErrorPolynomial.lean), and
[dyadic parameter bracket](proof/Erdos647_DyadicParameterBracket.lean), and
[fifth-power error absorption](proof/Erdos647_ErrorAbsorptionPower.lean), and
[dyadic logarithmic-scale absorption](proof/Erdos647_DyadicErrorLogScale.lean), and
[real-log error absorption](proof/Erdos647_DyadicErrorRealLog.lean), and
[two-parameter sieve assembly](proof/Erdos647_TwoParameterSieveAssembly.lean),
[exposed concrete witness](proof/Erdos647_BoundingSieveExposed.lean),
[multSum audit](proof/Erdos647_MultSumFieldAudit.lean),
[remainder audit](proof/Erdos647_RemFieldAudit.lean),
[nu audit](proof/Erdos647_NuFieldAudit.lean), and
[remainder-bound field assembly](proof/Erdos647_RemBoundFieldAssembly.lean),
[siftedSum audit](proof/Erdos647_SiftedSumFieldAudit.lean),
[active-prime parity obstruction](proof/Erdos647_OddParameterRejectedByTwo.lean),
[exclude-two sieve repair](proof/Erdos647_BoundingSieveExcludeTwo.lean), and
[candidate Finset bridge](proof/Erdos647_CandidateFinsetBridge.lean), and
[repaired-modulus candidate coprimality](proof/Erdos647_RepairedModulusCandidateCoprime.lean), and
[small-parameter band](proof/Erdos647_SmallParameterBand.lean), and
[candidate bridge with additive z loss](proof/Erdos647_CandidateBridgeAddZ.lean),
[small-prime density values](proof/Erdos647_NuSmallPrimeValues.lean), and
[finite-prime sum correction](proof/Erdos647_PrimeSumExcludeSmall.lean),
[repaired modulus primeFactors](proof/Erdos647_RepairedProdPrimeFactors.lean), and
[repaired logarithmic denominator bound](proof/Erdos647_RepairedLogLLower.lean), and
[shift-output seven-form bundle](proof/Erdos647_ShiftOutputsToSevenForms.lean), and
[`BoundingSieve` to `SelbergSieve` adapter](proof/Erdos647_BoundingToSelberg.lean),
[candidate two-parameter assembly](proof/Erdos647_CandidateTwoParameterAssembly.lean), and
[direct candidate-density assembly](proof/Erdos647_DirectCandidateDensityAssembly.lean), and
[shift outputs to repaired coprimality](proof/Erdos647_ShiftOutputsRepairedCoprime.lean), and
[exact `n=2520N` candidate reindexing](proof/Erdos647_CandidateReindex2520.lean).
The supporting generic kernel-verified lemmas are the square-support result
`lambdaSquared(w)(d)=0` for `d>R²`, the Selberg log-moment identity, and the
`L_R` tail bound; see [attack-plan.md](attack-plan.md).

---

## Family 9 — post-density existence and variant frontier

These ten modules contain 45 top-level theorems and four top-level helper
lemmas. They sharpen the exact open cores exposed after the density theorem;
they do not settle any of the three research-open Formal Conjectures
statements.

| source | declarations | verified result and status |
|---|---:|---|
| [`proof/Erdos647_Shift910Frontier.lean`](proof/Erdos647_Shift910Frontier.lean) | 6 theorems | shift 10 has no square branch; its prime and `5·prime` branches have exact mod-5/mod-25 restrictions; the two Hughes families force opposite parity of `N`; the assembled frontier has `2×3×2` branches. The four new generic lemmas separately returned `kernel_pass`, and the composition source-compiled against the campaign modules. |
| [`proof/Erdos647_Shift10FrontierWitness.lean`](proof/Erdos647_Shift10FrontierWitness.lean) | 1 theorem | for `N=6,970,590`, all seven sieve forms are prime, every budget through shift 10 holds, and shift 11 fails. Episode `1dbde32d-4fb7-4377-931d-df32607e5a6a` is **kernel_verified**. |
| [`proof/Erdos647_Shift12FrontierWitness.lean`](proof/Erdos647_Shift12FrontierWitness.lean) | 1 theorem | for `N=244,692,464,302`, all seven forms are prime, every budget through shift 12 holds, and shift 13 fails. Complete episode `3eb4731d-d0c9-4b7d-9e06-d44934b19c30` and the independently tracked seven-prime sub-conjunction `8f021bf2-9e4b-4f46-b6b5-09e59e8c0d78` are **kernel_verified**. |
| [`proof/Erdos647_Shift13Refined.lean`](proof/Erdos647_Shift13Refined.lean) | 3 theorems | `σ₀(2520N−13)≤15` forces at most three distinct prime factors and excludes `2,3,5,7`; divisibility by 13 is equivalent to `13∣N`. On `N=13M`, either `M≡6 (mod 13)` or the cofactor has at most seven divisors and two distinct prime factors. Episodes `9499a13b-25db-45f6-a492-8b357900aade` and `1e79ece8-14f0-43d2-b24a-f5cb43152f38` are **kernel_verified**. |
| [`proof/Erdos647_ShiftFactorFramework.lean`](proof/Erdos647_ShiftFactorFramework.lean) | 7 theorems | generic coprime-factor and prime-power budget peeling, cofactor `primeFactors.card` control, and exact next-`p`-adic lift/modular-class equivalences. The prime-power peel and modular-lift cores are **kernel_verified** in episodes `3e3ee8d9-a23b-4997-bb26-345cfe672337` and `5ec047ae-3659-449e-8546-26ea9c941be0`. |
| [`proof/Erdos647_Shift14Refined.lean`](proof/Erdos647_Shift14Refined.lean) | 5 theorems | shift 14 yields `σ₀(1260N−7)≤8`; away from `N≡3 (mod 7)`, `180N−1` has at most four divisors and two distinct prime factors. The next 7-adic layer is either `N≡3 (mod 49)` or one of six prime-cofactor lifts. Episode `0ccca717-0a99-42b3-82cb-7011619cfb73` is **kernel_verified**. |
| [`proof/Erdos647_Shift15Refined.lean`](proof/Erdos647_Shift15Refined.lean) | 7 theorems | peeling the universal factor 3 gives an eight-divisor cofactor budget; two 5-adic layers give prime cofactors outside the sole residual class `N≡32 (mod 125)`. Episodes `4a1060e5-3f9e-4a72-8ccf-ed7ae231d3be` and `718d1350-8ff2-4069-8527-5474a1dddd16` are **kernel_verified**. |
| [`proof/Erdos647_Shift16Refined.lean`](proof/Erdos647_Shift16Refined.lean) | 6 theorems | the family-B/odd branch has a cofactor with at most four divisors and two prime factors; the family-A/even branch splits through explicit 2-adic layers, leaving `M≡3 (mod 8)` as the residual class. The full source chain compiles, and the strongest even-parameter core returned `kernel_pass` in job `9d45701f-7e1e-45bc-8cd2-6c5b4be6906f`; **no tracked episode is claimed**. |
| [`proof/Erdos647_LimitShiftInterface.lean`](proof/Erdos647_LimitShiftInterface.lean) | 4 theorems | convergence to `atTop` is equivalent to eventual arbitrarily large shift excess. Prime powers prove an explicit unbounded subsequence and non-`BddAbove`, not convergence. The exact adapter episode `3baedfa9-85ed-48b0-b477-18faa0d9e47f` is **kernel_verified**. |
| [`proof/Erdos647_InfiniteWindowFrontier.lean`](proof/Erdos647_InfiniteWindowFrontier.lean) | 5 theorems + 4 lemmas | window sizes at most two are unconditional; above `n>10`, depth-two survivors are exactly `n=2q+2` with `q` and `2q+1` prime; infinitude at depth two is therefore equivalent to infinitude of Sophie Germain primes. Episodes `e7b81c9f-8b1e-41c5-a760-d9aba712bb16` and `7cf0660b-3dac-48f3-8294-7b22d8e9f593` are **kernel_verified**; the converse and final equivalence source-compiled in the pinned environment, and the exact iff is stated directly over the Formal Conjectures window expression. |

## Family 10 — power-prefix, block-production, and certificate architecture

| source | declarations | independently tracked roots |
|---|---:|---:|
| `Erdos647_RoughPowerBound.lean` | 1 | 1 |
| `Erdos647_GenericLocalPowerBound.lean` | 4 | 4 |
| `Erdos647_GenericPowerPrefix.lean` | 3 | 3 |
| `Erdos647_ShiftGcdClass.lean` | 2 | 2 |
| `Erdos647_GcdClassCubeBound.lean` | 4 | 4 |
| `Erdos647_ArbitraryBlockPowerPrefix.lean` | 4 | 2 |
| `Erdos647_FactorizationCertificate.lean` | 9 | 3 |
| `Erdos647_PairwiseCoprimeBlockNovelty.lean` | 2 | 2 |
| `Erdos647_FourthPowerDivisorBound.lean` | 2 | 2 |
| **Total** | **31** | **23** |

This family compresses the all-shift candidate condition in three ways.
First, generic and class-sensitive divisor-power inequalities show that only
a finite prefix can violate a shift budget. The exact local-ratio theorem
turns finitely many verified prime-power inequalities into a global bound and
subsumes the `35·τ(m)^3` class coefficient without rational arithmetic.
Second, unique block coordinates turn the full shift family into an exactly
equivalent family of local block/rung checks. Third, the executable
factorization checker supplies a small kernel-sound certificate format for
those checks.

The pairwise-coprime theorem isolates a possible negative mechanism:
sufficiently many suitable cells produce distinct new primes, and a common
host for them must be exponentially large. Neither pairwise-coprime block
production nor the common-host premise has yet been derived uniformly from
candidacy.

The fourth-power theorem reduces the universal explicit prefix to fourth-root
scale, but the prefix still grows with `n`. Thus this family closes formal
assembly and compression problems, not the original existence problem. The
three Formal Conjectures research declarations remain open.

The central development here is no longer “one more shift.” The framework
isolates a reusable transition: factorization → coprime budget division →
prime-factor control → one exceptional next-adic congruence. Shifts 14–16 are
deliberately included as independent stress tests showing that 7-adic,
5-adic, and family-sensitive 2-adic arguments all fit that transition. What
remains genuinely shift-specific is the affine factorization, the available
family/parity hypotheses, and finite exceptional-digit enumeration. A full
existence proof still needs a global induction or growing-depth principle
showing that these transitions cannot continue indefinitely. The limit route
must upgrade sparse unboundedness to an eventual uniform statement. The first
open infinite-window depth is already the classical Sophie Germain infinitude
problem.

## Family 11 — large-factor novelty, CRT re-entry, and second-layer catalogs

This continuation turns the power-prefix architecture into two reusable
accumulation layers.  At the first layer, divisor budgets force primes beyond
a chosen smoothness width; exact shift-difference identities prevent reuse;
finite-catalog and primorial theorems make the resulting novelty explicit.
Product dichotomies then identify the precise subset input needed for a CRT
re-entry shift and its divisor-count exclusion certificate.

At the second layer, removing a square-scale prime leaves a proper coprime
cofactor with a halved divisor budget.  Gap rigidity and large-prime novelty
control interactions between those cofactors, while the smooth/nonsmooth
dichotomy leaves at most one additional exceptional coordinate.  Deleting the
two exceptional catalogs yields the conditional `W−2` second-layer catalog.
These are genuine new reductions and accumulation interfaces, but every
terminal assembly still has an explicit unproved global premise.  **Original
Formal Conjectures closure remains `0/3`.**

| source | declarations | tracked roots | verified result and status |
|---|---:|---:|---|
| [`proof/Erdos647_FifthPowerDivisorBound.lean`](proof/Erdos647_FifthPowerDivisorBound.lean) | 2 theorems | 2 | `τ(n)^5≤147700800n` and the exact fifth-root candidate prefix; both roots are **kernel_verified**. |
| [`proof/Erdos647_HybridPowerPrefix.lean`](proof/Erdos647_HybridPowerPrefix.lean) | 6 theorems | 1 | sharp cube, fourth-, and fifth-power bounds feed a hybrid candidate prefix; the compact assembly root is **kernel_verified**, and the unconditional source composition replays in the pinned project. |
| [`proof/Erdos647_SmoothLargePrimeFactor.lean`](proof/Erdos647_SmoothLargePrimeFactor.lean) | 4 theorems + 1 lemma | 2 | a positive smooth number is power-bounded by its divisor budget; exceeding that bound produces a prime factor larger than `W`. Both strongest roots are **kernel_verified**. |
| [`proof/Erdos647_ShiftDifferenceNovelty.lean`](proof/Erdos647_ShiftDifferenceNovelty.lean) | 7 theorems | 3 | exact shifted-value gcd transport, large-factor non-reuse, finite injectivity, and exponential shared-host accumulation; all three strongest roots are **kernel_verified**. |
| [`proof/Erdos647_BlockLargePrimeNovelty.lean`](proof/Erdos647_BlockLargePrimeNovelty.lean) | 4 theorems | 4 | consecutive candidate budgets plus smoothness escape produce distinct large prime factors, with exact candidate/scalar bridges and a shared-host product bound; all four roots are **kernel_verified**. |
| [`proof/Erdos647_FiniteCatalogEscape.lean`](proof/Erdos647_FiniteCatalogEscape.lean) | 6 theorems | 3 | every exact candidate beyond a finite catalog product has a bounded positive shift carrying a prime outside that catalog; all three strongest roots are **kernel_verified**. |
| [`proof/Erdos647_PrimorialCandidateEscape.lean`](proof/Erdos647_PrimorialCandidateEscape.lean) | 1 theorem | 1 | the primorial specialization exposes a prime larger than `W` together with the matching candidate shift budget; **kernel_verified**. |
| [`proof/Erdos647_PrimeProductDichotomy.lean`](proof/Erdos647_PrimeProductDichotomy.lean) | 4 theorems | 1 | either two distinct selected factors have product below `n`, or at most one coordinate has square below `n`; the strongest arbitrary-family root is **kernel_verified**. |
| [`proof/Erdos647_TSubsetProductDichotomy.lean`](proof/Erdos647_TSubsetProductDichotomy.lean) | 2 theorems | 1 | `t` individually power-small entries yield a `t`-subset product below `n`, otherwise fewer than `t` such entries exist; the constructive root is **kernel_verified**. |
| [`proof/Erdos647_CRTReentryExclusion.lean`](proof/Erdos647_CRTReentryExclusion.lean) | 6 theorems | 3 | distinct prime divisors force `2^|I|` divisors, the CRT remainder re-enters the shift condition, and a strict sandwich excludes candidacy; three roots are **kernel_verified**, with numerical corollaries source-replayed. |
| [`proof/Erdos647_LargePrimeCofactor.lean`](proof/Erdos647_LargePrimeCofactor.lean) | 3 theorems | 2 | square- and power-scale prime removal gives exact factorization, coprimality, and divisor-count splitting, then transports the halved budget to a candidate shift; both strongest roots are **kernel_verified**. |
| [`proof/Erdos647_CofactorGapRigidity.lean`](proof/Erdos647_CofactorGapRigidity.lean) | 3 theorems | 2 | cofactor gcds divide the shift gap, while a repeated positive cofactor with odd complementary primes forces `2q` to divide that gap; both strongest roots are **kernel_verified**. |
| [`proof/Erdos647_CofactorLargePrimeNovelty.lean`](proof/Erdos647_CofactorLargePrimeNovelty.lean) | 2 theorems | 1 | primes larger than the block width cannot repeat across second-layer cofactors, yielding an injective cofactor-prime family; **kernel_verified**. |
| [`proof/Erdos647_SmoothCofactorBound.lean`](proof/Erdos647_SmoothCofactorBound.lean) | 3 theorems | 1 | a positive `W`-smooth cofactor obeys `q≤W^(τ(q)−1)` and, under the doubled budget, `q≤W^(k/2)`; the combined root is **kernel_verified**. |
| [`proof/Erdos647_NonsmoothCofactorException.lean`](proof/Erdos647_NonsmoothCofactorException.lean) | 3 theorems | 1 | distinct block coordinates have distinct large cofactor primes; under the no-cross-pair hypothesis, at most one square-small cofactor is nonsmooth; **kernel_verified**. |
| [`proof/Erdos647_TwoExceptionalIndices.lean`](proof/Erdos647_TwoExceptionalIndices.lean) | 1 theorem | 1 | deleting two exceptional subsets of cardinality at most one leaves at least `W−2` block coordinates; **kernel_verified**. |
| [`proof/Erdos647_SecondLayerCatalogAssembly.lean`](proof/Erdos647_SecondLayerCatalogAssembly.lean) | 1 theorem | 1 | conditionally assembles at least `W−2` coordinates with prime/cofactor factorization, coprimality, square-smallness, smoothness, and explicit cofactor size; **kernel_verified**. |
| [`proof/Erdos647_Rung5Rung7Relation.lean`](proof/Erdos647_Rung5Rung7Relation.lean) | 1 theorem | 1 | proves the exact Bézout relation `5(504N−1)−7(360N−1)=2`; **kernel_verified**. |
| [`proof/Erdos647_Rung5Rung7Coprime.lean`](proof/Erdos647_Rung5Rung7Coprime.lean) | 1 theorem | 1 | combines that relation with parity to prove `Coprime (504N−1) (360N−1)`, the first concrete cross-rung factor non-reuse result; **kernel_verified**. |
| [`proof/Erdos647_RungCofactorsPairwiseCoprime.lean`](proof/Erdos647_RungCofactorsPairwiseCoprime.lean) | 6 theorems | 3 | six explicit positive Bézout identities prove pairwise coprimality of the reduced cofactors at rungs `5,7,9,10`; selected prime factors are pairwise distinct, every positive parameter supplies four such primes, the rung-5/rung-10 5-adic depths cannot both be positive, and the total base-block depth bound improves from `4B+20` to `3B+14`. All three tracked roots are **kernel_verified** and replayed. |
| [`proof/Erdos647_BaseGauntletAdicBoundary.lean`](proof/Erdos647_BaseGauntletAdicBoundary.lean) | +1 theorem | 0 new | `erdos647_base_gauntlet_adic_boundary_sharpened` returns the `3B+14` total directly from the four candidate shift budgets. The integrated corollary is source-checked in the pinned project; its two mathematical ingredients are the tracked roots above, so no additional tracked episode is claimed. |
| [`proof/Erdos647_BaseGauntletSharpDepth.lean`](proof/Erdos647_BaseGauntletSharpDepth.lean) | 1 theorem | 1 | excludes all four pure-power residual branches modulo `4,3,8,4`; returns residual divisor-count bounds `3,4,3,3`, depth bounds `1,2,2,1`, and total depth at most `5`. Episode `d1a3a3ae-24ba-4ece-ae85-5df82815be36` is **kernel_verified** and replayed. |
| [`proof/Erdos647_BaseGauntletResidualPrimes.lean`](proof/Erdos647_BaseGauntletResidualPrimes.lean) | 1 theorem | 1 | the `q5`, `q9`, and `q10` residuals cannot be squares modulo `8,8,4`; their `σ₀≤3` bounds therefore force all three to be prime. Episode `4faf6a2e-8528-4abd-a17d-9b30fc0ab98a` is **kernel_verified** and replayed. |
| [`proof/Erdos647_SigmaFourClassification.lean`](proof/Erdos647_SigmaFourClassification.lean) | 3 theorems | 3 | classifies every `σ₀≤4` integer as prime, prime square, prime cube, or distinct semiprime; removes the square branch for `q7`; and proves that a composite `q7` forces 7-adic depth zero. All three roots are **kernel_verified** and replayed. |
| [`proof/Erdos647_BaseGauntletDepthResidues.lean`](proof/Erdos647_BaseGauntletDepthResidues.lean) | 1 theorem | 1 | identifies the depth-one branches exactly as `a5=1↔N%5=4` and `a10=1↔N%5=3`; episode `dce030c5-2b7c-4e69-99fc-f4596b52f736` is **kernel_verified** and replayed. |
| [`proof/Erdos647_BaseGauntletHigherDepthResidues.lean`](proof/Erdos647_BaseGauntletHigherDepthResidues.lean) | 1 theorem | 1 | identifies all bounded 7-adic and 3-adic depth values exactly from `N mod 7,49,3,9`; episode `f9641fd5-9ce1-47ff-84d4-edc0a2083f42` is **kernel_verified** and replayed. |
| [`proof/Erdos647_Q7ResidueShapeRefinement.lean`](proof/Erdos647_Q7ResidueShapeRefinement.lean) | 2 theorems | 2 | positive 7-adic depth forces `q7` prime, while cube and distinct-semiprime branches acquire exact mod-3 factor residues; episodes `df6ab19d-4ade-4719-a408-02fa6b70c1db` and `98b5e0d7-2952-4507-b2b4-75530f770ea6` are **kernel_verified** and replayed. |
| **Continuation total** | **76 theorems + 1 lemma** | **44** | The 44 new exports are all **kernel_verified**; this table adds the exact 26-module continuation beyond the previous catalog checkpoint. |

---

*Counts are explicit: 467 actual theorem declarations plus five top-level
helper lemmas in 178 Lean files, and 331 related proof-search episodes in the
export archive (324 kernel-verified,
seven retained non-success histories). These are different metrics—one episode
can assemble several helper declarations, while some final repository
compositions are not standalone episodes. The global density theorem is
complete; original Formal Conjectures closure remains 0/3 and the existence
problem remains open.*
