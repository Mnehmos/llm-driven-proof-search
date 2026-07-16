# Machine evidence — Erdős #647 campaign

> Living document; last updated 2026-07-15. Tracked episode records below use
> the MCP proof-search pipeline (dev-attested fidelity basis →
> `kernel_verified`, the honest ceiling for a dev attestation). The final
> repository-level composition is recorded separately and is not represented
> as a standalone tracked episode. Import manifest for the tracked entries:
> `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]`.
> Pinned environment hash:
> `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.

## Repository-level composed replay (not a standalone MCP episode record)

On 2026-07-15, a clean source replay in the pinned environment compiled the
entire transitive dependency graph for
[`proof/Erdos647_ConcreteAsymptoticDensity.lean`](proof/Erdos647_ConcreteAsymptoticDensity.lean):
42 campaign modules plus `proof/campaign/family2-classifications.lean`, exit
code 0. All generated `.olean` files were removed before and after the replay;
the portable evidence is the Lean source.

The terminal theorem is:

```lean
theorem boundedCandidates_density_global (X : ℕ) :
    ((boundedCandidates X).card : ℝ) ≤
      globalDensityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7
```

Here `boundedCandidates X` is the bounded Erdős-647 candidate `Finset`, and
`globalDensityConstant` is an explicit effective real constant defined in the
same file. The proof includes both the large range and the finite initial
range. A source scan found no `sorry`, `admit`, or added axiom in the new
assembly files.

The repaired squarefree remainder proof also passed an independent exact
MCP kernel check: verification job
`0e256779-f272-4ca8-9658-5bdeeb2272bf`, result artifact
`a35c39592ae9ea69d560a96c43d859dfd91cd92a01763e454502b7b8b474036b`.

This evidence establishes the density theorem, not a resolution of whether a
larger Erdős-647 candidate exists.

## Existence-continuation checkpoint

Four post-density interfaces are now independently tracked and/or composed
from tracked source:

| field | value |
|---|---|
| statement | the global maximum condition implies `σ₀(n-k)≤k+2` for every `0<k<n` |
| problem_version_id | `11379956-bdc3-4ed9-bef3-3e373c8e85c2` |
| episode_id | `3061458d-df2c-4e48-b05d-76b48209a2f6` |
| root_statement_hash | `df1b2ec8493146e374e83d3c293fd3a25f7c6d4f4c4d48f1049a9050c3a6faa9` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_ShiftDepthInterface.lean](proof/Erdos647_ShiftDepthInterface.lean) |

The exact converse—global maximum iff all positive shift budgets—was then
tracked separately:

| field | value |
|---|---|
| statement | the global maximum condition is equivalent to all `0<k<n` shift budgets |
| problem_version_id | `e997a6ae-30ba-4af3-b49a-39a4c405b2d4` |
| episode_id | `8bc57f29-adcc-467d-b986-3e060b2d2e3c` |
| root_statement_hash | `7e1e0ea545ac3f75298bbece75068750bc4036dd40ed53d16886103725cb4556` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_ShiftDepthInterface.lean](proof/Erdos647_ShiftDepthInterface.lean) |

The finite interval needed by the existence problem is no longer merely
absorbed into a density constant:

| field | value |
|---|---|
| statement | every `25 ≤ n ≤ 84` has a certified failed shift |
| problem_version_id | `2c7952fa-4342-40ed-8a1d-43b093f585aa` |
| episode_id | `88a8417d-715f-4d93-aad6-6317e8f1be80` |
| root_statement_hash | `0b8b7fe73cb4aecbdb9e650fe50ee9e982ecab4d23273c92297fa331c6f8724d` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_FiniteBandClosure.lean](proof/Erdos647_FiniteBandClosure.lean) |

Finally, the exact adapter for the short-window variant is tracked:

| field | value |
|---|---|
| statement | the short-window maximum is equivalent to its finite shift-budget family |
| problem_version_id | `0c4b9003-af8d-4da4-8fb0-0129d1f85a67` |
| episode_id | `74fbfc4b-da2f-467c-9d44-d02b6eeb28f4` |
| root_statement_hash | `bdf2ab2b8d18289e8a6131c18f9fd0da555d7571ecf7f24b8243005adcca5409` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_WindowShiftInterface.lean](proof/Erdos647_WindowShiftInterface.lean) |

Source composition additionally proves that every candidate is above `84`,
is divisible by `2520`, and lies in one of the two verified four-prime
families; see
[proof/Erdos647_CandidateStructuralReduction.lean](proof/Erdos647_CandidateStructuralReduction.lean).
The refined shift-9 source removes the square branch and adds exact residue
restrictions. The new
[`proof/Erdos647_Shift910Frontier.lean`](proof/Erdos647_Shift910Frontier.lean)
also removes the shift-10 square branch, gives exact residue restrictions for
both surviving shift-10 branches, separates the two prime-chain families by
the parity of `N`, and assembles the resulting twelve-branch frontier. Its four
new generic lemmas separately returned `kernel_pass` in jobs
`7b41ecb5-e33d-41a5-a65d-3b82228c58cf`,
`21486d9c-5362-42c3-9874-de7ff8c5f14e`,
`f139e7c5-1c06-408a-8f42-478e4028333c`, and
`7cd52d14-886a-4923-a76d-8e6062aab8e1`; the assembled module source-compiled
against the campaign dependencies.

### Generic shift-factor / next-adic induction framework

The continuation is now organized around
[`proof/Erdos647_ShiftFactorFramework.lean`](proof/Erdos647_ShiftFactorFramework.lean),
not an indefinitely growing list of unrelated shift lemmas. It proves seven
generic theorems: coprime-factor budget peeling, prime-power specialization,
candidate-facing wrappers, cofactor prime-factor-cardinality control, and the
equivalence between one further `p`-adic layer and one exceptional congruence
class for a linear cofactor.

| result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| prime-power cofactor peel | `4aaaaeea-dd00-46fe-9a78-1fcebad0d236` | `3e3ee8d9-a23b-4997-bb26-345cfe672337` | **kernel_verified**, `root_proved`; precheck job `94f97429-5c14-428b-befd-cb119da1b79b` `kernel_pass` |
| next-adic lift iff modular exceptional class | `8f86185e-db7a-45af-8ffa-74d933439eb6` | `5ec047ae-3659-449e-8546-26ea9c941be0` | **kernel_verified**, `root_proved`; precheck job `d2260d3c-2e67-4a3e-ac55-13782f89237f` `kernel_pass` |

Shifts 14–16 were then used as stress tests for that API:

| source/result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| [shift-14 two-layer 7-adic frontier](proof/Erdos647_Shift14Refined.lean) | `0524467f-fcdf-45ea-a439-7c0709a50d95` | `0ccca717-0a99-42b3-82cb-7011619cfb73` | **kernel_verified**, `root_proved` |
| [shift-15 two-layer 5-adic frontier](proof/Erdos647_Shift15Refined.lean) | `9bee03bb-dbb7-43e3-91d7-eebc2b32c0d5` | `4a1060e5-3f9e-4a72-8ccf-ed7ae231d3be` | **kernel_verified**, `root_proved` |
| shift-15 generic peel core | `e12fd70e-31e9-48c6-8be8-4cd02ad2d949` | `718d1350-8ff2-4069-8527-5474a1dddd16` | **kernel_verified**, `root_proved` |
| [shift-16 family-sensitive 2-adic frontier](proof/Erdos647_Shift16Refined.lean) | — | — | source chain replay passed; strong even-parameter core job `9d45701f-7e1e-45bc-8cd2-6c5b4be6906f` **kernel_pass**; no tracked episode |

The full source chain—framework, shift 14, shift 15, and shift 16—compiled
cleanly in dependency order. The three examples show that the abstraction
handles 7-adic, 5-adic, and family-sensitive 2-adic refinements. The remaining
shift-specific work is the exact affine factorization, parity/family input,
and finite exceptional-digit enumeration. No theorem yet proves that the
generic transition terminates for every candidate.

Shift 13 now has its own exact refinement:

| result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| `σ₀(x)<2^(r+1)` bounds `x.primeFactors.card` by `r` | `0da6c01d-4e97-4b86-96f8-52e95b3b70db` | `9499a13b-25db-45f6-a492-8b357900aade` | **kernel_verified**, `root_proved` |
| exact first 13-adic split for a candidate's shift-13 value | `284723a7-d5b3-4417-b8d2-84dca18bf894` | `1e79ece8-14f0-43d2-b24a-f5cb43152f38` | **kernel_verified**, `root_proved` |

The source-checked middle theorem in
[`proof/Erdos647_Shift13Refined.lean`](proof/Erdos647_Shift13Refined.lean)
shows that `2520N−13` has at most three distinct prime factors, has no prime
factor among `2,3,5,7`, and is divisible by 13 exactly when `N` is. The tracked
13-adic theorem then proves that on `N=13M`, either the unique exceptional
first lift `M≡6 (mod 13)` occurs or the remaining cofactor has at most seven
divisors and at most two distinct prime factors.

Two exact consistency witnesses show why this fixed-depth frontier is not yet
a contradiction:

| result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| [`N=6,970,590`: seven prime forms, all budgets through shift 10, failure at shift 11](proof/Erdos647_Shift10FrontierWitness.lean) | `b9a96621-fc15-42af-bf3d-8b330a1cc0f0` | `1dbde32d-4fb7-4377-931d-df32607e5a6a` | **kernel_verified**, `root_proved` |
| [`N=244,692,464,302`: seven prime forms, all budgets through shift 12, failure at shift 13](proof/Erdos647_Shift12FrontierWitness.lean) | `3bf407ed-5a59-49d8-9791-9cf6f73b81d8` | `3eb4731d-d0c9-4b7d-9e06-d44934b19c30` | **kernel_verified**, `root_proved` |
| independently tracked seven-prime sub-conjunction for the depth-12 witness | `942cd91e-ae66-46da-97f5-2cf2a39b89da` | `8f021bf2-9e4b-4f46-b6b5-09e59e8c0d78` | **kernel_verified**, `root_proved` |

The witness proofs use explicit prime factorizations and multiplicativity of
`sigma`; they are kernel certificates, not trust in an external factorization
program. These are strict reductions and obstruction certificates for the
still-open existence problem, not evidence that it has been solved.

### Limit and infinite-window hard cores

The limit module isolates the exact missing uniform statement:

| result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| convergence to `atTop` iff every excess threshold is eventually exceeded by some shift | `7f51a2e4-b598-4a05-88ff-a0068f7e8a30` | `3baedfa9-85ed-48b0-b477-18faa0d9e47f` | **kernel_verified**, `root_proved` |

[`proof/Erdos647_LimitShiftInterface.lean`](proof/Erdos647_LimitShiftInterface.lean)
also proves an explicit prime-power subsequence is unbounded and that the
whole range is not `BddAbove`. The prime-power lower bound separately returned
`kernel_pass` in job `23015b9f-023c-44e7-a025-a6fdd9e1b417`. Sparse
unboundedness is deliberately not reported as convergence.

For the infinite-window variant, the first nontrivial fixed depth already
meets a classical open problem:

| result | problem_version_id | episode_id | outcome |
|---|---|---|---|
| window sizes at most two are unconditional | `f1717863-2574-48c0-a9d1-ae3a7b223fb9` | `e7b81c9f-8b1e-41c5-a760-d9aba712bb16` | **kernel_verified**, `root_proved` |
| infinitely many safe-prime parameters give infinitely many depth-two survivors | `62b31233-1d14-44f2-84f0-f1af49d33e0a` | `7cf0660b-3dac-48f3-8294-7b22d8e9f593` | **kernel_verified**, `root_proved` |

The source-compiled converse in
[`proof/Erdos647_InfiniteWindowFrontier.lean`](proof/Erdos647_InfiniteWindowFrontier.lean)
proves that, for `n>10`, surviving shifts 1 and 2 is equivalent to
`n=2q+2` with both `q` and `2q+1` prime. Consequently, infinitude at window
size three is exactly equivalent to infinitude of Sophie Germain primes. This
identifies the hard core of that case; it does not settle it. The exact same
iff is now also stated directly over the upstream window expression as
`infinite_window_three_iff_infinite_sophie_germain` in the Formal
Conjectures module. Its abstract finite-exception/image seam returned
`kernel_pass` in proof-search job
`d14bee02-f06e-4e06-a528-597a73f0bc38`.

The source-level compatibility replay additionally compiled
[`proof/Erdos647_FormalConjecturesCompatibility.lean`](proof/Erdos647_FormalConjecturesCompatibility.lean)
from a clean staged copy of the complete density dependency graph. It proves
`CandidateBound` iff the exact Formal Conjectures maximum expression by
`Iff.rfl`, proves equality of the two bounded candidate Finsets by extensional
simplification, and restates `boundedCandidates_density_global` for that exact
set. The counterpart API in `FormalConjectures/ErdosProblems/647.lean` was
compiled independently under Formal Conjectures' pinned Lean/Mathlib version;
the complete warning-as-failure build passed all 8,869 jobs with only the
three intentionally open research statements remaining as source `sorry`s.
The repositories pin different versions, so this is an honest dual-toolchain
compatibility check rather than a forced mixed-version import.

## Complete proof-search export archive

The repository now includes exports for all 227 related episodes identified by
source provenance, the evidence ledger, the reconstructed modular campaign
index, and a read-only database closure audit. Of these, 220 report
`KERNEL_VERIFIED` and `kernel_verified = true`; three are unfinished, three
report `GAVE_UP`, and one reports `budget_exhausted`. Every entry reports
`fidelity_status = attested` and the pinned environment hash above.

- [export manifest](dossiers/exports/manifest.tsv)
- [public summaries](dossiers/exports/public_summary/)
- [full Markdown proof dossiers](dossiers/exports/full/)
- [structured training exports](dossiers/exports/training/)

These episode exports complement rather than replace the repository-level
clean replay of the final theorem. The composed density theorem is not
fabricated as an extra tracked episode.

## Headline records (proof snapshots in [proof/](proof/))

### Theorem 2 (prime-chain reduction) — stage k = 1,2

| field | value |
|---|---|
| statement | `∀ n : ℕ, 24 < n → ArithmeticFunction.sigma 0 (n-1) ≤ 3 → ArithmeticFunction.sigma 0 (n-2) ≤ 4 → ∃ q, Nat.Prime q ∧ n = 2*q+2 ∧ Nat.Prime (n-1)` |
| problem_version_id | `1987e20c-6d03-4882-8c20-d0495744d9e9` |
| episode_id | `c4a688c1-053c-4e08-8da3-e3ab7c4c594e` |
| root_statement_hash | `4b5752c641c3fb016f1ecc6dae940feff8d02251d55880a491590964f7307c95` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_Thm2_Stage12.lean](proof/Erdos647_Thm2_Stage12.lean) |

### Theorem 2 — stage k = 4

| field | value |
|---|---|
| statement | `∀ q : ℕ, 13 ≤ q → q.Prime → (2*q+1).Prime → ArithmeticFunction.sigma 0 (2*q-2) ≤ 6 → ∃ p, p.Prime ∧ q = 2*p+1` |
| problem_version_id | `52ff69c0-e7f5-443c-9cc1-14da17c92dd4` |
| episode_id | `57bf2fb3-7a57-4644-b99a-f97ff2aa600c` |
| root_statement_hash | `f940625c1484f450d165e8f450a8f8c7eef5a39fc451e5f0f0a70f24f6c97afc` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| snapshot | [proof/Erdos647_Thm2_Stage4.lean](proof/Erdos647_Thm2_Stage4.lean) |

### Theorem 2 — stage k = 8 (final family split)

| field | value |
|---|---|
| statement | `∀ p : ℕ, 7 ≤ p → p.Prime → (2*p+1).Prime → ArithmeticFunction.sigma 0 (4*p-4) ≤ 10 → ∃ s, s.Prime ∧ (p = 2*s+1 ∨ p = 4*s+1)` |
| problem_version_id | `513c65fa-b031-479b-aa97-7d39091e7587` |
| episode_id | `95fae0a4-f448-4236-9039-604e5cb902e7` |
| root_statement_hash | `068b74ebba069c507eb598bade6aced904cb882e6b46745dedaeb1f97052382a` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| snapshot | [proof/Erdos647_Thm2_Stage8.lean](proof/Erdos647_Thm2_Stage8.lean) |

### Layer A — exact Mertens identity via Chebyshev θ

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ)) = Chebyshev.theta x / (x * Real.log x) + ∫ t in Set.Ioc (2:ℝ) x, (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t` |
| problem_version_id | `d584666d-e50d-488d-b459-5d1265a3aadd` |
| episode_id | `7a7e8098-a5bf-4dd9-97df-145e34ee914b` |
| root_statement_hash | `9802976a83cd2b4a604d3a77e6f1c4cf2800c41b9ec7797550df9f1fa28a7c98` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_MertensIdentity.lean](proof/Erdos647_MertensIdentity.lean) |

### Layer A part 2a — main-term antiderivative (FTC)

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2) = (Real.log (Real.log x) - (Real.log x)⁻¹) - (Real.log (Real.log 2) - (Real.log 2)⁻¹)` |
| problem_version_id | `781d4876-55c9-4c3c-9420-602b508771be` |
| episode_id | `36f8eaa9-7116-44a3-b633-f8f1a03210f4` |
| root_statement_hash | `513062caa29c528d7f2df3f6e92de50073c08703b87b05fe15abc49064431b65` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_MertensMainTerm.lean](proof/Erdos647_MertensMainTerm.lean) |

### Layer A part 2b (piece) — Mertens weight integral (FTC)

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2) = (2 * Real.log 2)⁻¹ - (x * Real.log x)⁻¹` |
| problem_version_id | `1fc1ab2d-de49-4660-8d7c-8aefeb853a73` |
| episode_id | `700f297f-d8bc-448f-b118-2921e1b98491` |
| root_statement_hash | `a9a3ca286fad52e416ba8ee74768a661e33d22b0528d82f9022c4f636b7795df` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_MertensWeightIntegral.lean](proof/Erdos647_MertensWeightIntegral.lean) |

### Layer A part 2b — power-law comparison antiderivative (FTC)

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, ((t^2)⁻¹) = (2:ℝ)⁻¹ - x⁻¹` |
| problem_version_id | `89b0e678-f69b-427d-9e71-9523856a7cab` |
| episode_id | `1f97aff1-1173-4246-b6dd-06d15ff25ee4` |
| root_statement_hash | `cd03a308ddacbad0f6723dfd5c88377d555d9737d0ce99b92a5b4d325db0fe9b` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_PowerIntegral.lean](proof/Erdos647_PowerIntegral.lean) |

### Layer A part 2b — log(t+2) error integral bound (analytic inequality)

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) ≤ 1 + (Real.log 2)⁻¹` |
| problem_version_id | `8bf294a3-c882-4588-9894-e2fbc8ee0edf` |
| episode_id | `6fa25185-251b-4203-a843-63fc2b0c43e6` |
| root_statement_hash | `935fe42967e7ff964228916ae4a685a231db58b3131fe2f491aff2da5b1c0a61` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_MertensErrorLog.lean](proof/Erdos647_MertensErrorLog.lean) |
| note | first genuine analytic inequality (pointwise comparison + `integral_mono_on`), not an antiderivative identity |

## Campaign ledger (problem_version_id index, 2026-07-12/13 sessions)

### Level-truncated Selberg optimal weight (2026-07-15)

| field | value |
|---|---|
| statement | `∀ s R, 1≤R → ∃ w, w 1=1 ∧ (∀d, R<d → w d=0) ∧ mainSum(lambdaSquared w)=1/∑_{l∣prodPrimes,l≤R}selbergTerms(l)` |
| problem_version_id | `4fad80bd-e331-441f-bf57-4c6aed41c4aa` |
| episode_id | `333d528d-3032-47b6-ba2e-fa5ae42da41f` |
| root_statement_hash | `4f1a4ce8ede04985ca97e7256937909614d1ab74ca0d5eebe28203c4dadac666` |
| outcome | **kernel_verified**, `root_proved` in 2 tracked proof-search attempts |
| environment_hash | `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d` |
| snapshot | [proof/Erdos647_SelbergOptimalWeightTruncated.lean](proof/Erdos647_SelbergOptimalWeightTruncated.lean) |

### Truncation-repair quantitative chain (2026-07-15)

| theorem | problem version | episode | statement hash | outcome |
|---|---|---|---|---|
| supported optimal weight + pointwise bound | `481f490b-672c-4b2a-9f08-f630a371c606` | `445e255c-cc28-443c-bcf5-a883543784da` | `594f3cedfb630efcbde24cffbbd05b68bd9af857eddcd47430ffd7fd8fba0d78` | **kernel_verified** |
| `lambdaSquared≤16^ω` | `fe23498c-ad0b-4c9a-97e1-93e38a1c32b2` | `cf8a89b5-0e9e-4b70-babf-ebffe3b4d954` | `71060def3dcb7eb54646d651bfd2fbebb2ae372bc4f1fae0454ab34bcbaed26a` | **kernel_verified** |
| `errSum≤(R²+1)^8` | `684cb8cf-bf0c-44e2-abec-7d0b7a0f5f28` | `312120f0-82e4-49d8-a0a5-022822683064` | `3c1e46fbc7804d2f063b72a31cebded17bd0e910f97c26551b7b6ecb13f62287` | **kernel_verified** |
| prime log-moment Abel identity | `34305a84-6663-460a-a0e8-006337c85838` | `fbf2047c-f3aa-4a54-9529-8ab7ecdd81e5` | `a35ce4674c9889b018360f522feeba117076c0036d4083c345d0667d116eec50` | **kernel_verified** |
| prime log-moment upper bound | `b6aa3391-d6b7-4f3b-bc08-9a73261ecf4d` | `e7e66b7f-45ad-4031-8dbc-c3c4af9d9717` | `ff77799760cbd395d0f550d8b0b208dda643178a58b585dceac4ef7aeaee837a` | **kernel_verified** |
| `L_R≥L/2` under the moment condition | `e8710139-6736-43ff-a7d3-efa7a852e365` | `d2c798f6-9476-4029-b72d-71ac9c898c14` | `2ccac8eafcf60ed27e66edff148e720217932117d7abc6095724b8707378a47e` | **kernel_verified** |
| `R=(2z)^20` satisfies the moment condition | `d6c321da-fb33-46c9-b1eb-114a339d01b8` | `c7a9a71b-13be-4c5a-ab86-953c8d7e76c1` | `7ed86d0c64adc313bc2f30c519577cf093fb1ec96ee833250cbd76a7475b7612` | **kernel_verified** |
| explicit `(R²+1)^8≤2^328·z^320` | `c64e7c8d-088b-4dc2-814f-a98bebd7dd7c` | `668f3e3f-190e-4b7d-9e23-c111482e2534` | `1f78e550b89c6a39a159f2c6900d34e701ec2f34dbdd88fcb9eea4fcd4920bb7` | **kernel_verified** |
| dyadic `z=2^k` bracket | `9f1f4f3c-7665-4fc6-8d71-0a6120ae145e` | `cd7d60ab-82d3-4288-9b58-da5f3553a257` | `cfe2b3be87e35a6e6a6c88137f2282074d5b894fead1755dbfd4eaba758986c9` | **kernel_verified** |
| exact fifth-power error absorption | `3544e7da-c8a9-4feb-844f-91be241dee92` | `88f161ad-0233-4381-aded-09f76a861a90` | `c02c2ab4543b320aef6f95f8b09474b90c684f139b2bad3fe5bd1f7fbc4f07e0` | **kernel_verified** |
| dyadic error at `X/k^7` scale | `e74ace30-3fd0-4192-aea1-1f0f348f6e9b` | `52f39da0-0c91-4381-ba6b-6763044014e1` | `7a3904890bde66411c6d2808eb1d5a8b1f7f81c0d5d6f9cc3f61061586d62a1e` | **kernel_verified** |
| real-log `X/(log z)^7` error bridge | `23d21971-6676-40d0-99cb-556e22be189b` | `a4646056-f6af-462c-be5f-1fee2bd03727` | `1d46a1c91a58507998f972e21cb91ba9e851a1a5a91546556d6da7a211140420` | **kernel_verified** |
| generic two-parameter sieve assembly | `372fc2d3-227e-4104-ac93-6657f6fd8538` | `47248be9-ad01-4c85-a333-1bade2673bfc` | `2670a2ea7507bf270826b978d761107e40e07564ff85cf843e340f47893d532c` | **kernel_verified** |
| exposed two-parameter concrete sieve | `6a01ac1e-442e-4f1b-a2d8-dc4935d8cfd1` | `76254e7f-c4ca-45e2-a029-26697df01c16` | `304244913c9d6af8b1a2f4e5f87b98c8c53b98723ce9155e892e1b1872835ef8` | **kernel_verified** |
| concrete `multSum` field audit | `640009dd-0b98-48b7-930a-c83c6e19c8ae` | `3c2ce9c0-6e0b-4bd8-9b52-8e6464a32d64` | `148469e0b0aca0bb147eb1330a3aba34913fe9c77b37739e82a47b855614c317` | **kernel_verified** |
| concrete `rem` field audit | `874897f7-1348-4cd2-ab74-bbc93ebb2920` | `e95b56da-6d95-43eb-85c5-ea2ae9c128be` | `c9b20538c0f9232f614f82198dc1b59db12236ac66eb0f1c74b89bdb66e2640b` | **kernel_verified** |
| squarefree concrete `nu` audit | `21676a9b-32f0-497b-a903-cacd52211606` | `a8a19a21-345a-4e96-a656-1206b8947f16` | `a0d0f1342429ff9d92538e5fbd2aa2edb3b6127fa5cbb4dd90febc33dc226e8b` | **kernel_verified** |
| concrete remainder-bound field assembly | `776de7d6-9710-427e-a3fe-29ad9be73f50` | `161e04d9-7439-4866-b5d7-483d1cb4b0c7` | `dad741f946608c63be3cd8a7d4ea6137ab771ecba09c866f38b5819df469b62b` | **kernel_verified** |
| exact concrete `siftedSum` field audit | `dd9707c4-da49-47f6-8c3f-223bd9fef756` | `1452648d-cac9-41ec-bd0c-b1def718b639` | `f689cbc5c7b187fc2cb95959c7d4df139121d5b1a07a9f97076a46d88ed5550d` | **kernel_verified** |
| odd-parameter rejection by active prime `2` | `8057d050-084d-49ef-8be3-91be624a6e36` | `346e79fe-6366-49e3-b67d-0335655ca461` | `318baf888e5c5753c02203ffe166b64f7da332a27e075d11bafe055527c7cca4` | **kernel_verified** |
| concrete sieve finite-prime repair excluding `2` | `96815907-c5f3-4be5-9e6b-15b1812c118d` | `5a05324a-c61b-4ae6-be26-5cc09c2e0d08` | `0dd01bfe773a2a937b524312f3b7c61334442a224ec14f0c6eb0cabfd315a90c` | **kernel_verified** |
| candidate Finset to `siftedSum` bridge | `3821e6ae-7ce0-40eb-913e-1a39e33e62b7` | `4ba7cc7e-7d4c-4b67-a1ee-867e9fa5c47e` | `6ef9f3e6e341975a7d4c186f0ffb78323d4ec10d6f9aac587e930b6c5e93fa8d` | **kernel_verified** |
| repaired-modulus candidate coprimality | `d1d08312-eea8-443a-9ff2-78f6c63d0014` | `4c2d4160-9914-4d83-b649-6bc22d1f04d6` | `3d8f14ca5dc6466efd34a526dba274fac3350e2647b16166b40599632f232726` | **kernel_verified** |
| explicit small-parameter band | `cc5eabec-9ba7-4b38-9f8a-482998d707af` | `13abb6bb-6091-4647-b46f-8ed0417beb04` | `fd551191af356f6d475dc719c877be08696d4ecfc78b1d135a8166288456fd5f` | **kernel_verified** |
| candidate bridge with explicit additive `z` loss | `20e17129-58dd-46aa-9a9f-d35e0d97c96b` | `48f49525-b5f1-4bac-8155-8dcfe91764ca` | `091284a06deb6c14f157b9dbe555e00409b518e8bf9c274edfcb2a89f8ecb8e6` | **kernel_verified** |
| concrete `nu` values at deleted primes | `7851c193-5d39-4302-a93f-a474a2ffa6c8` | `e11b21e8-95f3-4358-92d2-96b3263c864c` | `057a47bc28d86c645c29c77546fc05686d12c7126314e000dd8a8ccee52832f2` | **kernel_verified** |
| finite-prime sum correction | `35439d12-2f15-43bd-81ce-2eabea637710` | `34fa55fc-ad48-4028-9a47-adc93bd12f1f` | `7a62fdd6409e716383ae7beb65058b57665b8dbca26d8f1878a126db3088b1fc` | **kernel_verified** |
| repaired modulus primeFactors audit | `dd157db4-78e2-4285-8069-b6ce4ee14526` | `f307bb4a-7536-4cd5-aa06-4a570ed341f0` | `efe8ee4f7a731426d19c8df450b119aa2f170e57ba8c8d91489f3d854361750d` | **kernel_verified** |
| repaired logarithmic denominator lower bound | `ce61fdf7-5644-428c-a1ac-f3c7b3b9a5e1` | `6be4d210-d956-481a-893c-9999bdcac1a1` | `090c8da35d45ab27dc6f7ee42c12b2e2048edb54cf8a916be4b420106502378f` | **kernel_verified** |
| shift outputs to seven-form bundle | `e84e00c6-17b8-43e4-a832-b40909cb576a` | `6dd68116-dbbc-45e8-871a-9b3ab8edab75` | `2fbfb68c85117c41163b2c1acd682a353ea5cf1bac0e879976136c68b69f44c8` | **kernel_verified** |
| `BoundingSieve` to `SelbergSieve` adapter | `a1095c68-7d6f-4e6a-91ad-894d73d35863` | `e993eb52-c42d-43ba-88d9-f7a147ec2b6f` | `fcaef0ed5c3c0fe5416bcb3fe4291a300d525c6d116727ed1825badc22c6c6f5` | **kernel_verified** |
| candidate-count two-parameter assembly | `04896a5d-4423-44dc-ac03-424f8fba0689` | `e45bd140-c9b8-469a-980b-2414cb1dd3c3` | `185531de8d717c7c4dde91ffb618ab216796fec1b0e322ebb0b4342514cf6b34` | **kernel_verified** |
| direct generic candidate-density assembly | `9ad9f4e4-11d4-4f40-89f9-39c3c990b7fa` | `58cd0973-3eb4-46d0-8bd1-22e514bbf6ae` | `c15e88b4e9d19c53b514d0df428e04566b8c1fe43cd2faa685fb35f4b2999f30` | **kernel_verified** |
| shift outputs to repaired-modulus coprimality | `5570a9ac-16d7-42ad-9c06-7a2a16e5d30d` | `4cae8930-9352-4158-8873-6caeff3939ce` | `243afd8aa13511b4a00d551e016769fe46ae52da8e73e0a1a0de0978596ec8fa` | **kernel_verified** |
| exact `n=2520N` candidate reindexing | `74892f8f-6612-4031-a686-23ba5be359dd` | `a7c81412-3be2-44f5-99d4-abbbaec604a3` | `106d8dda7d5bd58ed14213ed8ac6ae176ccb35b0a1d10812950acd46d36b2a2a` | **kernel_verified** |

All thirty-five snapshots also passed separate asynchronous verification jobs in
environment `9e26d28e…`.

### Additional tracked closing seams (2026-07-15)

| theorem/source | problem | episode | outcome |
|---|---|---|---|
| large candidate divisibility assembly, [`proof/Erdos647_CandidateDivisible2520.lean`](proof/Erdos647_CandidateDivisible2520.lean) | `45f39da2-e4f2-4050-8401-65c82df535a3` | `2646ba8b-6646-4a28-8d81-a34ff56b693f` | **kernel_verified**; separate asynchronous `kernel_pass` |
| shift-one square-branch elimination, [`proof/Erdos647_ShiftOnePrime.lean`](proof/Erdos647_ShiftOnePrime.lean) | `ec29c1bd-1b37-4e1e-ae50-e43554a09746` | `74ae7201-fabb-468e-bd1d-83c2da3bb8ef` | **kernel_verified**; job `e100e36a-e764-4304-9c3d-1d92037e12fd` `kernel_pass` |


Base sieve & refinement certificates: `200bce1c` (48 survivors mod 46189),
`a001e7c1` (mod 23, 528), `4d2b7ec1` (mod 29, 768), `83fb9810` (mod 31, 864),
`b4196b16` (mod 37, 1152), `2f28d8d4` (mod 41, 1344), `c0f6a321` (mod 43,
1440), `b9083710` (45-class frontier certificate).

Shift classifications (13): `00cfc756` (shift 1), `87ea1d9a` (2), `323c4801`
(3), `14a21b69` (4), `e4397627` (5), `245e963a` (6), `0f8dcd94` (8),
`8ed738c7` (9), `6c5dcfd9` (10), `b9c90e1d` (12), `1710efdc` (18), `5a643568`
(20 — with the genuine `r=125` exception), `5df5a27e` (24). Reusable
characterization lemma: `fb7d4bf8`.

Bridging closures: 9 at ℓ≤19 (`de35e7ec`, `8a65bb51`, `dfb82405`, `ddc951c3`,
`c0565e84`, `efc75f5f`, `b542e676`, `a62e9824`, `7e6d5dde`) and 13 at ℓ≤29
(`90c306f4`, `3aa31e38`, `7f68e7f0`, `e6345707`, `c3337705`, `ec6ecc6a`,
`9bd67f4d`, `5ba4356c`, `84df59dc`, `b1b996c8`, `b0d5b386`, `9c93a1d6`, plus
shift-5's `7e6d5dde` tier).

Residue closures (45 → 41, matching Hughes): `e8e7b8cd` (N≡39325,
direct-full-value), `15bdd8f4` (41470, single-overlap + ZMod 8), `49ae1aa9`
(40612), `fa7e0a1f` (26884, 4-prime modulus, 11-leaf tree).

Sub-AP closures (48, frozen per the all-avoid obstruction): discovery closure
`40988498`; wave A–E `3f98ba86`, `d037ea2a`, `a109a5af`, `4b799f58`,
`02d5a4a3`; waves F–L including `82b78dec`, `1a283efe`, `32706bae`,
`61612470`, `0822d882`, `9a615fba` and 36 more (full list reproducible from
the environment's problem ledger by statement pattern
`N % <46189·p> = r → False`).

## Reproduction notes

- Tracked `.lean` snapshots in [proof/](proof/) preserve the exact statement
  and proof term accepted by the kernel (statement hashes above). A small
  number of final composition modules instead import those snapshots and are
  identified explicitly as source-replayed rather than assigned fabricated
  episode records.
- The tracked pipeline's episode ledgers (hash-chained, append-only) live in
  the proof-search environment's database; the IDs above are the lookup
  keys. This folder deliberately records *pointers + snapshots*, not the
  database itself.
- The final density dependency graph and the new post-density modules were
  source-replayed in the pinned environment. Formal Conjectures compatibility
  was additionally checked in that repository's separately pinned toolchain.
  These replays complement, but do not upgrade, the dev-attested fidelity of
  the tracked proof-search episodes.
