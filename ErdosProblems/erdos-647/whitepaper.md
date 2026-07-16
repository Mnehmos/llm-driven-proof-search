# Erdős #647 — mapping the wall and formalizing the density frontier

> **Status: GLOBAL DENSITY THEOREM KERNEL-VERIFIED; problem OPEN.** Last
> updated 2026-07-15. Erdős #647 is unresolved: no larger candidate is known
> and none is excluded in full. What is now complete is the formal density
> theorem `|C(X)| ≪ X/(log X)^7`, including an explicit effective constant.

## 1. The problem

[Erdős #647](https://www.erdosproblems.com/647) (Erdős–Selfridge, ~1979).
Let `τ(m)` count the divisors of `m`. Is there any `n > 24` with

```
max_{m < n} (m + τ(m)) ≤ n + 2 ?
```

True at `n = 24`, and `n + 2` is best possible. Erdős doubted any larger
solution exists. In plain words: the machine `m ↦ m + τ(m)` sprays values up
the number line; a solution `n` is a place where **every** smaller `m` lands
at or below `n + 2` — which forces every neighbor `n−1, n−2, n−3, …` to be
divisor-poor (prime or nearly prime) *simultaneously*. Candidates have been
excluded by computation up to **6.16 × 10¹⁷** (Hughes's frontier certificate;
Idén independently to 10¹² and beyond with gap-growth analysis).

## 2. Prior art this work builds on (and where it lives)

- **Scott Hughes** — [erdos647-proof-chain](https://github.com/scottdhughes/erdos647-proof-chain):
  Stage-1 modular reduction *in Lean* (every candidate `n > 84` has
  `2520 ∣ n` and `N = n/2520` in 41 explicit residue classes mod
  `46189 = 11·13·17·19`); a finite-range certificate to 6.16×10¹⁷; a paper
  (`paper/main.tex`) whose **Theorem 2** (prime-chain reduction) and
  **Theorem 3** (Brun-sieve density bound `|C(x)| ≪ x/(log x)⁷`) are
  **not** in his Lean development; and the **all-avoid obstruction**
  (`docs/stage1_boundary.md`) proving bounded congruence-tree searches
  cannot close the 41 open classes.
- **Kenta Kitamura** — necessary conditions (e.g. `(n−3)/3` prime) and
  co-development of the Brun-sieve direction (May–June 2026).
- **Patrik Idén** — segmented-sieve computation to 10¹², `D(n)` depth
  records, gap-growth heuristics.
- **Thomas Bloom** — erdosproblems.com, the catalog that coordinates all of
  this.

Everything below was produced in a verifier-gated LLM proof-search
environment: an AI agent proposes Lean proofs, and **only the Lean 4 kernel
(pinned Mathlib) decides what counts**. Individual milestones were checked
through tracked, hash-chained proof-search episodes. The terminal composition
was additionally replayed from clean Lean source across its full transitive
dependency graph; it is recorded as repository-level kernel evidence rather
than misrepresented as a single tracked episode. See
[evidence.md](evidence.md) for machine records and [credit.md](credit.md) for
full attribution and honest limits.

## 3. Campaign log

### 3.1 Independent rederivation of the modular reduction (2026-07-12/13)

Rather than importing Hughes's Lean code, we rederived the entire Stage-1
reduction from scratch in our own environment — a genuine independent
replication under a second verifier setup, and a tighter one:

- **13-coefficient base sieve, 48 survivors** (Hughes's 12-form sieve leaves
  96): kernel-verified counting certificate over `Finset.range 46189`
  (problem `200bce1c`), refined by extra primes 23, 29, 31, 37, 41, 43
  (problems `a001e7c1`, `4d2b7ec1`, `83fb9810`, `b4196b16`, `2f28d8d4`,
  `c0f6a321`) composing by CRT to a 955-million-class combined frontier —
  each tier a separate kernel-verified certificate.
- **13 shift-classification theorems**: for each shift `k ∣ 2520` in
  `{1,2,3,4,5,6,8,9,10,12,18,20,24}`, a theorem of the form "any candidate
  forces `(n−k)/k` to be prime / prime² / small-multiple-of-prime" — e.g.
  shift 3 is Kitamura's condition `(n−3)/3` prime. One genuine mathematical
  exception surfaced and was proven exactly: shift 20 admits `r = 125 = 5³`
  at `n = 2520` only.
- **Bridging-closure theorems (the step that makes the sieve *proven*, not
  just computed)**: for every shift row, a theorem deriving the sieve
  predicate itself from the classification theorem — so the modular
  reduction rests on proofs about divisor counts, not on trusting a
  `native_decide` scan. Proven at ℓ ≤ 19 and again at ℓ ≤ 29 (backing the
  refinement tiers). ~50 kernel-verified theorems in this family.
- **Frontier certificate**: our 45-class mod-46189 frontier, kernel-verified
  (problem `b9083710`), then reduced to **41 = Hughes's exact count** by
  closing four residues with his two harder techniques, re-derived and
  re-proven fresh here: `N ≡ 39325` (direct-full-value, modulus 2584),
  `41470` (single-overlap, modulus 3553, first `ZMod 8` argument of the
  campaign), `40612` (modulus 4199 — including a cleaner replacement for
  Hughes's own pure-power exclusion), and `26884` (modulus 14535, 4 prime
  factors, 11-leaf case tree, ~400 lines, kernel-passed cold).

### 3.2 Novel sub-AP closures — and why we stopped (2026-07-13)

An original computational search over `gcd(2520·r − k, 2520·46189·p)` found
**48 new sub-AP congruence closures** — refined residue classes (mod
`46189·p`, `p ∈ {23,29,31,37,41,43}`) excluded *unconditionally, for all N*.
All 48 kernel-verified, most on the first attempt, from a fully mechanical
template. These are the same species as the 6549 sub-AP closures inside
Hughes's finite-range certificate — independently discovered against our own
tighter frontier.

Then we stopped, deliberately. Hughes's **all-avoid obstruction** shows any
finite tree of congruence closures leaves a surviving branch (each
(shift, prime) pair excludes ≤ 1 residue class mod p; CRT recombines the
survivors). Sub-AP work extends verified range but **cannot** resolve the
problem. Per that structural fact — and an explicit direction from the
human operator — the 48 closures are frozen as artifacts, and the campaign
moved to the wall itself.

### 3.3 Theorem 2, formalized for the first time (2026-07-13)

Hughes's **Theorem 2 (prime-chain reduction)** — stated in his paper only as
a sketch, absent from his Lean tree — says every candidate `n > 24` lies in
one of two exact prime constellations:

- **Family A:** `n = 8s + 8` with `s, 2s+1, 4s+3, 8s+7` all prime,
- **Family B:** `n = 16s + 8` with `s, 4s+1, 8s+3, 16s+7` all prime.

We rederived the full proof from the sketch (validated numerically against
Hughes's published depth records `D = 4..7`) and formalized it as three
composable kernel-verified stages, each driven by a shift divisor-budget and
a 2-adic decomposition, with each stage's exceptional cases killed by
primality facts proven in the *previous* stage:

| stage | statement (abbrev.) | problem id | proof |
|---|---|---|---|
| k=1,2 | `σ₀(n−1)≤3 ∧ σ₀(n−2)≤4 → n=2q+2`, `q` & `n−1` prime | `1987e20c` | [Stage12](proof/Erdos647_Thm2_Stage12.lean) |
| k=4 | `+ σ₀(2q−2)≤6 → q=2p+1`, `p` prime | `52ff69c0` | [Stage4](proof/Erdos647_Thm2_Stage4.lean) |
| k=8 | `+ σ₀(4p−4)≤10 → p=2s+1 ∨ p=4s+1`, `s` prime | `513c65fa` | [Stage8](proof/Erdos647_Thm2_Stage8.lean) |

Chaining the three substitutions yields exactly families A and B. To our
knowledge this is the **first machine-checked proof of Theorem 2**.

### 3.4 A proven negative: Theorem 2 cannot close the 41 classes either

Translating the chain to sieve coordinates (`n = 2520N`): family A ⟺ `N`
even with base prime `s = 315N/... `-forms — every chain element is still a
**fixed linear form in N**. So the all-avoid obstruction applies verbatim:
congruence closures built from Theorem-2 chain elements have the same
"≤ 1 class per prime" structure, and CRT again guarantees a surviving
branch. We record this as a result, not a disappointment — it extends
Hughes's negative theorem to a track he had not explicitly ruled out, and it
says precisely why the next successful step had to be analytic rather than
another bounded modular search.

### 3.5 The density campaign: obstruction, repair, and concrete assembly (2026-07-13/15)

The Hughes–Kitamura density target is that candidates below `X` number at
most `≪ X/(log X)⁷`. The exponent seven comes from the simultaneous
seven-linear-form system obtained after writing a sufficiently large
candidate as `n = 2520N`:

```
210N−1, 315N−1, 420N−1, 630N−1,
840N−1, 1260N−1, 2520N−1.
```

Mathlib already contained the abstract `BoundingSieve` and `SelbergSieve`
framework, but not the concrete application or the level-truncated optimal
weight required here. The completed formalization proceeds in six layers.

1. **Candidate transport.** Define
   `boundedCandidates X` as the `n ∈ [1,X]` with `n > 24` satisfying the
   original divisor-count bound. Every member above 84 is proved divisible
   by 2520, so `n = 2520N` is exact and injective. The verified shift
   classifications imply precisely the coprimality condition required by the
   seven-form sieve, including the awkward `2·prime` branch.

2. **Concrete promoted sieve.** A nameable seven-form `BoundingSieve` is
   built with support equal to the image of the product of the seven forms,
   unit weights, total mass `X/2520`, and the exact root-union density `ν`.
   Removing the bad active prime 2 repairs the parity obstruction without
   changing the underlying support. The same structure is then promoted to a
   `SelbergSieve` at arbitrary positive level `R`.

3. **Level-truncated optimal weights.** The optimal weight has hard support
   `d ≤ R`; therefore `lambdaSquared(w)(d) = 0` for `d > R²`. Its pointwise
   coefficients satisfy

   ```
   |lambdaSquared(w)(d)| ≤ 16^ω(d).
   ```

   The concrete seven-form counting remainder satisfies

   ```
   |rem(d)| ≤ 7^ω(d)
   ```

   on the squarefree divisor lattice. Consequently the unrestricted divisor
   explosion is replaced by the polynomial bound

   ```
   errSum ≤ (R² + 1)^8.
   ```

   This repairs the only identified analytic obstruction: Mathlib's abstract
   `level` field does not itself truncate `lambdaSquared`, so using an
   untruncated optimal weight would have left an exponential-in-`π(z)` error.

4. **Polynomial level certification.** The verified prime logarithmic-moment
   estimate shows that `R = (2z)^20` preserves at least half of the full
   Selberg denominator. It also gives the explicit error estimate
   `(R²+1)^8 ≤ 2^328 z^320`.

5. **Seventh-power denominator.** The first analytic route formalized an
   exact Abel identity and an effective Chebyshev/Mertens lower bound for
   `∑_{p≤z}1/p`. That theorem is correct, but its available leading
   coefficient is `log 2`; multiplying by seven does **not** yield the full
   seventh power required here. The final proof therefore uses a stronger
   elementary comparison:

   ```
   ∑_{n≤z} 1/n ≤ ∏_{p≤z} (1 − 1/p)⁻¹.
   ```

   Every `n ≤ z` divides `z!`, and the reciprocal divisor sum of `z!`
   factors into finite geometric series bounded by the corresponding Euler
   factors. Since the concrete tuple has exactly seven roots at the relevant
   primes, Bernoulli's inequality lifts this to the seventh power. Deleting
   the exceptional primes `{2,3,5,7,11}` costs exactly `77/16`, giving

   ```
   (16/77)^7 · (log z)^7 ≤ L.
   ```

6. **Dyadic parameters and finite closure.** Choose `z = 2^k` from a
   verified dyadic bracket for `X`, then `R = (2z)^20`. Above the explicit
   threshold `16^400`, the main term, the polynomial error, the additive
   survivor loss `z`, and the fixed initial contribution are absorbed into
   `X/(log X)^7`. Below the threshold, the trivial card bound is absorbed by
   enlarging the constant.

The intermediate concrete inequality, before the final dyadic substitution,
is

```
|C(X)| ≤ 60
  + 2(77/16)^7 · (X/2520)/(log z)^7
  + (((2z)^20)^2 + 1)^8 + z.
```

### 3.6 Terminal theorem and replay evidence (2026-07-15)

The final source theorem is
[`boundedCandidates_density_global`](proof/Erdos647_ConcreteAsymptoticDensity.lean):

```lean
theorem boundedCandidates_density_global (X : ℕ) :
    ((boundedCandidates X).card : ℝ) ≤
      globalDensityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7
```

The constant is explicit:

```lean
densityConstant =
  (2 * (77/16)^7 + 3 * 2^328 * (log 2)^7) * 800^7

globalDensityConstant =
  max densityConstant (log (16^400))^7.
```

A genuinely clean replay removed all generated `.olean` files and rebuilt
the theorem's complete dependency graph: 42 campaign modules plus
`family2-classifications.lean`, exit code 0 in the pinned environment. A
source audit found no `sorry`, `admit`, or added axiom in the assembly. The
repaired squarefree remainder was also submitted to the independent exact
proof-search verifier and returned `kernel_pass`; identifiers and hashes are
recorded in [evidence.md](evidence.md).

For provenance beyond the source replay, all 331 related campaign
episodes are published under [dossiers/exports/](dossiers/exports/README.md)
in redacted public-summary JSON, full Markdown dossier, and structured
training JSON formats. Of these, 324 report `KERNEL_VERIFIED` in the pinned
environment; seven non-success histories are retained for audit completeness.

This proves a density-zero result with the claimed seventh logarithmic power.
It does **not** prove that no larger candidate exists: an infinite set can
have density zero, and the theorem supplies neither a witness nor a complete
exclusion.

### 3.7 From individual shifts to a reusable induction framework (2026-07-15)

The post-density campaign initially advanced shift by shift. Exact witnesses
then showed why this could not be presented as a quick closure: one parameter
survives every budget through shift 10 and fails at 11, while another survives
through shift 12 and first fails at 13. Those are kernel-checked consistency
certificates, not heuristic search observations.

The resulting change in architecture is more important than any next shift.
[`Erdos647_ShiftFactorFramework.lean`](proof/Erdos647_ShiftFactorFramework.lean)
extracts the common transition used by the refinements:

1. a candidate supplies `σ₀(n-k)≤k+2`;
2. an exact factorization and coprimality peel a known factor and divide the
   remaining divisor budget;
3. for a prime power `p^e`, the budget is divided by exactly `e+1`;
4. the divided budget bounds the cofactor's number of distinct prime factors;
5. failure of coprimality at the next stage is exactly one more `p`-adic
   layer, hence one exceptional congruence class for a linear cofactor.

The prime-power peel and modular-lift cores are tracked `kernel_verified`.
This is a genuine meta-framework: future concrete instances should provide
only the affine factorization, family/parity information, and a finite list of
exceptional `p`-adic digits.

Shifts 14–16 were formalized specifically to stress-test that abstraction.
Shift 14 produces a two-layer 7-adic frontier; outside `N≡3 (mod 7)`, the
cofactor `180N−1` has at most four divisors and two distinct prime factors,
while the next layer is one class modulo 49 or six explicit prime-cofactor
lifts. Shift 15 gives a two-layer 5-adic frontier with prime cofactors outside
the sole residual class `N≡32 (mod 125)`. Both capstones are tracked
`kernel_verified`. Shift 16 couples the same mechanism to the two
prime-chain families: the family-B odd branch has a cofactor with at most four
divisors and two prime factors; the family-A even branch passes through
explicit 2-adic layers and leaves `M≡3 (mod 8)` as the residual class. Its
full source chain compiles, and its strongest even-parameter core independently
returned `kernel_pass`; no tracked shift-16 episode is claimed.

These examples are not a commitment to march through every shift. Their role
is to demonstrate that 7-adic, 5-adic, and family-sensitive 2-adic arguments
share one verified transition. The open mathematical task is now to find a
global induction or growing-depth invariant proving that this transition
cannot continue indefinitely for a candidate. No such termination theorem is
claimed here.

### 3.8 Power-prefix compression and block production (2026-07-16)

The next abstraction compresses the number of shifts requiring explicit
arithmetic. For every positive `r`, if each prime divisor of `m` is at least
`2^r`, then

```text
τ(m)^r ≤ m.
```

More generally, [`Erdos647_GenericLocalPowerBound.lean`](proof/Erdos647_GenericLocalPowerBound.lean)
turns a finite table of verified local prime-power inequalities into a global
bound. It supports natural constants and an exact integral
denominator/numerator form. The latter recovers coefficients such as `8/5`
and `8/7` without formal rational arithmetic. A bound
`A·τ(m)^r≤C·m` implies that a failed budget `B+k<τ(n-k)` can occur only inside

```text
A(B+k)^r < C(n-k).
```

Thus a finite prefix certifies all shifts for any fixed `n`, and the `B=2`
corollary directly certifies the exact supremum predicate appearing in Formal
Conjectures.

For `n=2520N`, small-prime divisibility is known exactly:
`gcd(2520N-k,2520)=gcd(k,2520)`. Peeling `2,3,5,7` gives

```text
35·τ(2520N-k)^3 ≤ C(k)(2520N-k),
```

where

```text
C(k) =
  (if 2∣k then 8 else 1)
  (if 3∣k then 3 else 1)
  (if 5∣k then 8 else 5)
  (if 7∣k then 8 else 7).
```

The normalized local constants are `(8,3,8/5,8/7)`. This is stronger than
using the worst class uniformly.

Every positive shift also has unique block coordinates
`k=block·q+s`, `0<s≤block`. The formal block theorem proves an exact iff
between all global budgets and the local class-sensitive prefix cells
`block·(N-q)-s`. Different coordinates produce different shifted values,
although distinctness of values does not imply distinctness of prime factors.

An executable factorization checker closes the finite-certification seam.
For each required shift it checks a supplied list of distinct prime powers,
their exact product, and the resulting divisor count. A batch theorem proves
coverage of the entire prefix, and an end-to-end theorem converts a successful
batch into the exact candidate supremum condition. The kernel verifies the
factorization data; it need not run an unbounded factoring algorithm.

Two further theorems isolate the hoped-for accumulation mechanism. A
pairwise-coprime block of values greater than one produces one distinct prime
per cell, disjoint from any avoided older catalog. If all those primes divide
one positive host `H`, then

```text
2^block.card ≤ H.
```

The unresolved step is deriving sufficiently large pairwise-coprime blocks
and a shared host uniformly from candidacy.

Finally, the explicit global estimate

```text
τ(n)^4 ≤ 19680n
```

reduces the universal prefix to the fourth-root region

```text
(k+2)^4 < 19680(n-k).
```

This is a substantial compression for fixed-candidate certification, but the
prefix still grows with `n`. No theorem here supplies a universal
contradiction or a larger candidate. All three Formal Conjectures research
declarations remain open.

### 3.9 Large-factor accumulation, CRT re-entry, and the second layer (2026-07-16)

The next continuation replaces the pairwise-coprime-block hope by a weaker
fact that is available for every pair of shifts. For `k₁≤k₂<n`,

```text
gcd(n-k₁,n-k₂) = gcd(n-k₁,k₂-k₁).
```

Therefore every common divisor divides the shift gap. In a width-`W` block,
chosen prime factors larger than `W` cannot repeat, even when the shifted
values themselves are not pairwise coprime. This is the exact non-reuse
mechanism in `Erdos647_ShiftDifferenceNovelty.lean`.

The divisor budget supplies those factors through a smooth-number
alternative. If every prime divisor of a positive `m` is at most `W`, then

```text
m ≤ W^(τ(m)-1).
```

Hence a shifted value larger than its allowed smooth threshold has a prime
factor above `W`. The block assembly selects one such prime per coordinate
and proves injectivity. Separately, the fifth-power estimate
`τ(m)^5≤147700800m` and the hybrid cubic/fourth/fifth prefix reduce the
explicit checks needed for any fixed candidate. A finite prime catalog also
cannot stabilize the process: once `n` exceeds its product by enough, a
bounded shift has a prime divisor outside the catalog. The primorial
specialization gives a factor above every fixed cutoff.

Distinct large primes become useful when a subset product is below `n`.
The pair and general `t`-subset dichotomies formalize exactly this alternative.
For a selected index set `I`, put

```text
Q = ∏ i∈I, Pᵢ,     h = n mod Q.
```

When `Q<n`, the remainder is a genuine positive re-entry shift beyond the
original block, every `Pᵢ` divides `n-h`, and candidacy forces

```text
2^|I| ≤ τ(n-h) ≤ h+2.
```

Thus `h+2<2^|I|` is a complete kernel-checkable exclusion certificate. This
is a real feedback loop from many earlier shifts into one later shift, not
merely a cardinality heuristic.

The complementary no-small-product branch now has a second layer. Except for
at most one first-layer square exception, a selected prime `Pᵢ` can be peeled
from `n-(1+i)=Pᵢqᵢ`, giving `qᵢ<Pᵢ`, coprimality, and
`2τ(qᵢ)≤i+3`. Under the no-cross-product hypothesis, at most one square-small
cofactor can contain a prime above `W`: two such primes would be distinct by
the shift-gap argument, and their product would re-enter below `n`. Deleting
the two exceptional indices leaves at least `W-2` coordinates with

```text
qᵢ² < n,
every prime divisor of qᵢ at most W,
qᵢ ≤ W^((1+i)/2).
```

This conclusion is assembled in
`Erdos647_SecondLayerCatalogAssembly.lean`. The auxiliary gap-rigidity
theorems show that common cofactor divisors divide the coordinate gap; equal
cofactors with odd prime complements force twice the cofactor to divide that
gap.

A first concrete cross-rung incompatibility is also now verified. The rung-5
and rung-7 values satisfy

```text
5(504N-1) - 7(360N-1) = 2.
```

Every common divisor therefore divides `2`; both values are odd, so they are
coprime. The relation and coprimality conclusions are separately tracked in
`Erdos647_Rung5Rung7Relation.lean` and
`Erdos647_Rung5Rung7Coprime.lean`. The full calculation extends farther:
`Erdos647_RungCofactorsPairwiseCoprime.lean` gives six explicit positive
Bézout identities proving that the reduced cofactors at shifts `5,7,9,10`,
namely `504N-1`, `360N-1`, `280N-1`, and `252N-1`, are pairwise coprime.
Every positive parameter therefore supplies four pairwise distinct primes,
one dividing each shifted value. This blocks factor reuse across the entire
four-rung subsystem. Moreover, if `5^a₅` divides `504N-1` and `5^a₁₀`
divides `252N-1`, then `a₅=0` or `a₁₀=0`: the 5-adic escape branches at
rungs 5 and 10 cannot occur simultaneously. Combining this with the existing
individual bounds sharpens the base-gauntlet total from `4B+20` to `3B+14`;
at the main problem's `B=2`, the maximum falls from `28` to `20`.
`Erdos647_BaseGauntletAdicBoundary.lean` now exposes this sharpened total
directly from the four candidate shift budgets. The integrated corollary is
source-checked in the pinned Lean project; the incompatibility and arithmetic
bound it assembles are independently tracked kernel-verified roots. It is a structural increment,
not a global
contradiction.

The remaining slack in that `20` bound came from allowing a residual
cofactor to equal one. The tracked theorem
`Erdos647_BaseGauntletSharpDepth.lean` removes all four pure-power branches:
the required powers of `5`, `7`, `3`, and `5` have incompatible residues
modulo `4`, `3`, `8`, and `4`. Every residual cofactor is therefore
nontrivial and has at least two divisors. At `B=2`, their divisor counts are
at most `3,4,3,3`, their adic depths are at most `1,2,2,1`, and the two
5-adic depths cannot both be positive. The total depth is consequently at
most `5`, not `20`. This is a substantial finite-state compression, but the
surviving near-prime and semiprime branches still require a global
accumulation contradiction.

That residual state is now classified exactly. The three cofactors with
divisor budget at most three (`q5`, `q9`, and `q10`) are prime: the only
composite alternative is a square, and the affine decompositions exclude it
modulo `8`, `8`, and `4`. A general verified four-divisor classification
shows that `q7` is prime, a prime cube, or a product of two distinct primes
after its square branch is excluded modulo `3`. Finally, the original coupled
shift-7 budget shows that either `q7` is prime with 7-adic depth at most two,
or `q7` is composite and that depth is exactly zero. Thus the four-rung base
gauntlet has become an explicit shallow prime/semiprime state space rather
than an opaque low-divisor condition. Four new tracked episodes verify and
replay these statements independently.

The two 5-adic depth variables are now determined exactly by the parameter:
`a5=1` if and only if `N≡4 (mod 5)`, while `a10=1` if and only if
`N≡3 (mod 5)`. This fifth tracked result removes two existential choices from
the state space and makes the mutually exclusive 5-adic branches explicit.

The two remaining bounded depths are now residue data as well: `a7` is
determined by `N` modulo `7` and `49`, while `a9` is determined modulo
`3` and `9`. On the positive 7-adic branch the coupled shift-7 budget
forces `q7` prime. In the composite branches, the affine equation modulo
three forces a prime cube base to be `2 mod 3`, and a distinct-semiprime
pair to have residues `1,2` in some order. These are three separately
tracked, replayed kernel-verified refinements of the finite survivor state.

The remaining barrier is now precise. One must either force a re-entry subset
whose remainder violates `2^|I|≤h+2`, or prove that the large family of
smooth, size-controlled second-layer cofactors cannot coexist for a candidate.
Neither conclusion is currently proved. The original existence theorem, the
limit theorem, and the infinite-window theorem remain the same three open
Formal Conjectures declarations.

## 4. Scoreboard (honest)

- Problem status: **OPEN**. No new witness and no complete exclusion.
- Density status: **COMPLETE AND KERNEL-VERIFIED** with an explicit global
  constant and exponent seven.
- Portable proof source currently contains **467 actual theorem
  declarations and five top-level helper lemmas across 178 Lean files** under
  `proof/`. Including 47 definitions (45 public and two private helpers) gives
  519 declarations. These counts include helper and assembly declarations;
  they are not presented as 516 independent mathematical discoveries or 516
  standalone tracked episodes.
- Novel vs. replication: the sub-AP closures, the tighter 48-survivor base
  sieve, the bridging-closure layer, the Theorem-2 formalization, the
  extended negative result, the Mertens infrastructure, the explicit
  truncation repair, the elementary denominator proof, and the complete Lean
  density assembly are new artifacts. The frontier structure (41 classes,
  closure techniques, Theorem 2's statement, and the density target) comes
  from Hughes/Kitamura/Idén's mathematical program.

## 5. What "verified" means here

Every "proved" in this document means accepted by the **Lean 4 kernel**
against pinned Mathlib. Most milestones were submitted through the tracked
pipeline (`problem_create → episode_create → attempt_claim → episode_step`)
and carry statement hashes and episode IDs. The final composition is instead
identified explicitly as a clean repository-level replay of its entire
source dependency graph. The fidelity basis is a dev attestation (statements
were authored inside this project, not imported from a neutral catalog), so
tracked outcomes are reported as `kernel_verified`—never "certified." The
AI's prose and the human's expectations are not evidence; the checked source
is.

## 6. Open invitations

This folder is a living workspace, not a museum. The density program is no
longer an open invitation; it has landed. The original existence campaign is
active again. Its first new formal interface is
[`Erdos647_ShiftDepthInterface.lean`](proof/Erdos647_ShiftDepthInterface.lean):
the global maximum condition is equivalent to every budget
`σ₀(n-k)≤k+2`, and therefore a single failed budget excludes an individual
candidate. The interval `25≤n≤84` is now closed exactly; every remaining
hypothetical candidate is above `84`, divisible by `2520`, and lies in one of
the two verified four-prime families. The short-window formulation is also
equivalent to fixed-depth survival, isolating that variant to an infinitude
statement. This makes the next proof target precise: produce a failure at a
depth that may grow with `n`, or force it from the prime-chain classifications.
Useful next directions are:

Two subsequent checks sharpen that boundary. First, the shift-10 square
branch is impossible and the remaining prime/`5·prime` branches have exact
residue restrictions, but this still does not contradict shift 9 or the seven
prime forms. The exact parameter `N=6,970,590` gives
`n=17,565,886,800`, satisfies every budget through shift 10, and has all seven
forms prime; it first fails at shift 11. This fact is kernel-verified, so
“combine shifts 9 and 10” is now a formally closed dead end rather than a
plausible slogan.

The same test was then pushed through the full existing fixed-depth package.
For `N=244,692,464,302`, `n=616,625,010,041,040`, every budget from shift 1
through shift 12 holds and all seven forms are prime. The first failure is
shift 13, with `τ(n-13)=16>15`. Its explicit prime-factorization proof is also
tracked `kernel_verified`. Consequently, even adding the current shift-11/12
information cannot produce a uniform contradiction; the next honest target
must be structural or use depth growing with `n`.

Shift 13 now has a formal arithmetic frontier. Any hypothetical candidate has
`τ(2520N-13)≤15`, so that number has at most three distinct prime factors;
it is not divisible by `2`, `3`, `5`, or `7`, and it is divisible by
`13` exactly when `13∣N`. If `N=13M`, then outside the exceptional
residue `M≡6 (mod 13)`, removing the forced factor `13` leaves
`2520M-1` with at most seven divisors and at most two distinct prime factors.
This is a genuine narrowing of the first unclassified shift, but it is not yet
a contradiction.

The main continuation therefore packages the shared mechanism rather than
declaring shifts 14, 15, and 16 to be three unrelated new directions. The
generic factor/adic framework turns any exact factorization into a divided
cofactor budget, a prime-factor bound, and a unique exceptional next-adic
class. The shift-14/15 capstones are tracked `kernel_verified`; shift 16 has a
clean source-chain replay plus an independent `kernel_pass` for its strongest
even-parameter core. Together they validate the framework across 7-adic,
5-adic, and family-sensitive 2-adic branches. The desired breakthrough is a
global induction principle controlling repeated transitions, not an endless
catalog of shifts.

Second, the two open variants expose classical hard cores. The conjectured
limit is equivalent to requiring, for every `B`, an eventual shift with
`B+k<τ(n-k)`; prime powers make the sequence unbounded only along the sparse
subsequence `n=2^B+1`. For the infinite-window conjecture, window sizes at
most two are unconditional, while the first open size `k=3` is equivalent to
infinitude of Sophie Germain primes. These are genuine reductions, not
replacements for either variant `sorry`; the original existence `sorry` also
remains open. The exact `k=3` iff is stated directly in the Formal Conjectures
module, whose complete warning-as-failure build passes with those three
research statements still explicit.

Predicate compatibility with the upstream-style open formalization is also
mechanically recorded in
[`Erdos647_FormalConjecturesCompatibility.lean`](proof/Erdos647_FormalConjecturesCompatibility.lean).
The density theorem counts exactly the same candidate property, but it is not
the same proposition as the existential question and cannot replace its
`sorry`.

1. **Independent replay and proof review** — check the committed source in a
   fresh pinned environment, audit the candidate-to-sieve bridge, and seek
   simpler constants or a smaller threshold without weakening the theorem.
2. **Upstream the reusable sieve lemmas** — the level-truncated optimal
   weight, coefficient/support bounds, finite Euler-product comparison, and
   generic two-parameter assembly are Mathlib-shaped contributions.
3. **Find the global induction behind shift refinement** — use the generic
   factor/adic transition to prove that repeated exceptional lifts cannot
   continue for every candidate, ideally yielding a growing bound `k≤D(n)`
   at which some budget fails. Density zero is not emptiness, and bounded
   congruence trees cannot close the remaining classes.
4. **A better wall theorem** — the all-avoid obstruction rules out bounded
   congruence trees; what is the *strongest* class of arguments it rules
   out? Formalizing the obstruction itself in Lean would sharpen this.
5. **Anything we got wrong** — every claim above carries enough metadata to
   be checked. If a hash doesn't reproduce or a bound doesn't hold, that is
   exactly the kind of contribution this setup exists to catch.

*Contact / discussion: via the repository issues, or the erdosproblems.com
comment thread for #647.*
