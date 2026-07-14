# Erdős #647 — mapping the wall, formalizing the frontier

> **Status: LIVING DOCUMENT — problem OPEN.** Last updated 2026-07-13.
> Erdős #647 is unresolved. Nothing in this folder claims otherwise. As long
> as the problem stays open, this document grows: each dated section below is
> a checkpoint, not a conclusion.

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
(pinned Mathlib) decides what counts**. Every theorem cited here reached
`kernel_verified` through a tracked, hash-chained episode pipeline. See
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
says precisely *why* the remaining work must be analytic, not modular.

### 3.5 The frontier: density bounds, and the state of Lean's sieve theory (2026-07-13 →)

The live mathematical frontier (Hughes–Kitamura, May–June 2026) is the
**Brun sieve density bound**: candidates below `x` number at most
`≪ x/(log x)⁷`, because membership demands 7 simultaneous primes in an
admissible tuple. This exists only in manuscripts. Formalizing it would be,
as far as we can tell, the first kernel-checked sieve density bound of its
kind. Scoping findings (all verified against our pinned Mathlib):

- **Mathlib already has the Selberg sieve core**:
  `Mathlib.NumberTheory.SelbergSieve` — `BoundingSieve`, the Λ² sieve, and
  `siftedSum ≤ totalMass · mainSum + errSum`. (A fuzzy search misses it; we
  initially and wrongly declared it absent. Corrected on direct lookup —
  the mistake and correction are both part of the record.)
- **Missing piece #1 — quantitative Mertens**: Mathlib knows `∑ 1/p`
  diverges but has no rate. The sieve needs one.
- **Missing piece #2 — the Selberg optimization step**: Mathlib diagonalizes
  the Λ² main term but stops before the classical optimal-weights bound.
- **Missing piece #3** — the application layer: admissibility of the two
  7-tuples, density function ν, error-sum control.

**First brick, laid and kernel-verified** (problem `d584666d`,
[proof](proof/Erdos647_MertensIdentity.lean)): an *exact* identity

```
∑_{p ≤ x} 1/p  =  θ(x)/(x·log x)  +  ∫_{(2,x]} (log t + 1)/(t²·log²t) · θ(t) dt   (x ≥ 2)
```

via Mathlib's Abel summation applied to Chebyshev's θ. Since Mathlib carries
*effective* two-sided bounds on θ, quantitative Mertens now reduces to
bounding one explicit real integral — the next milestone in
[attack-plan.md](attack-plan.md).

## 4. Scoreboard (honest)

- Problem status: **OPEN**. No new witness; no disproof. Nothing here
  changes the answer — it changes what is *machine-checked* about the
  answer.
- Kernel-verified theorems in this campaign: **~110** (sieve certificates,
  13 classifications, 26+ bridging closures, 4 residue closures, 48 sub-AP
  closures, Theorem 2 × 3 stages, Mertens identity).
- Novel vs. replication: the sub-AP closures, the tighter 48-survivor base
  sieve, the bridging-closure layer, the Theorem-2 formalization, the
  extended negative result, and the Mertens identity are new artifacts; the
  frontier structure (41 classes, closure techniques, Theorem 2's
  *statement*, the density-bound program) is Hughes/Kitamura/Idén's
  mathematics.

## 5. What "verified" means here

Every "proved" in this document means: submitted through a tracked pipeline
(`problem_create → episode_create → attempt_claim → episode_step`), accepted
by the **Lean 4 kernel** against pinned Mathlib, recorded with statement
hashes and episode IDs ([evidence.md](evidence.md)). The fidelity basis is a
dev attestation (statements were authored inside this project, not imported
from a neutral catalog), so outcomes are reported as `kernel_verified` —
never "certified." The AI's claims are not trusted; the human's aren't
either. The checker's word is the only one that counts.

## 6. Open invitations

This folder is a living workspace, not a museum. Standing directions anyone
is welcome to pick up, argue with, or race us to:

1. **Quantitative Mertens in Lean** (Layer A, in progress here) — bound the
   integral above using `Chebyshev.theta_ge` / `theta_le_log4_mul_x`.
2. **The Selberg optimization step** (Layer B) — the classical
   optimal-weight bound on `mainSum`, on top of Mathlib's diagonalization.
3. **The 7-tuple application** (Layer C) — admissibility + error control
   for families A/B, targeting a machine-checked `x/(log x)⁷`.
4. **A better wall theorem** — the all-avoid obstruction rules out bounded
   congruence trees; what is the *strongest* class of arguments it rules
   out? Formalizing the obstruction itself in Lean would sharpen this.
5. **Anything we got wrong** — every claim above carries enough metadata to
   be checked. If a hash doesn't reproduce or a bound doesn't hold, that is
   exactly the kind of contribution this setup exists to catch.

*Contact / discussion: via the repository issues, or the erdosproblems.com
comment thread for #647.*
