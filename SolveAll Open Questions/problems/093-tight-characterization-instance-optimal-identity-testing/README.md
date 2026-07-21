# Tight Characterization of Instance-Optimal Identity Testing

**Status:** Unsolved  
**Source:** Posed by Clement Canonne (2024)

## Categories

- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #93 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $q$ be a known discrete probability distribution over a countable domain $\Omega$ , given to the tester via a succinct description, and let $\varepsilon\in(0,1]$ . The tester is given i.i.d. samples from an unknown distribution $p$ over $\Omega$ and must, with success probability at least $2/3$ (over its internal randomness and the samples), distinguish between

$
H_0: p=q \quad\text{and}\quad H_1: \mathrm{TV}(p,q) > \varepsilon,
$

where total variation distance is $\mathrm{TV}(p,q):=\tfrac12\sum_{x\in\Omega}|p(x)-q(x)|$ . Define the instance-optimal sample complexity $n^*(q,\varepsilon)$ as the minimum integer $n$ for which there exists such a (possibly randomized) tester that uses at most $n$ samples from $p$ .

### Unsolved Problem

Characterize $n^*(q,\varepsilon)$ up to universal constant factors for all discrete $q$ and all $\varepsilon\in(0,1]$ , in terms of a simple, explicit instance-dependent functional of the reference distribution and accuracy: identify a functional $\Phi(q,\varepsilon)$ and absolute constants $c,C>0$ such that

$
c\,\Phi(q,\varepsilon) \le n^*(q,\varepsilon) \le C\,\Phi(q,\varepsilon)
$

for all $q,\varepsilon$ . Equivalently, what is the correct instance-dependent quantity that governs the optimal sample complexity of identity testing to a fixed reference distribution $q$ at distance parameter $\varepsilon$ ?

## Significance & Implications

Worst-case identity-testing bounds optimize over the hardest reference distributions, but can substantially overestimate the samples needed for a given, fixed $q$ . A tight instance-optimal characterization would (i) precisely separate which parts of $q$ drive the statistical difficulty at accuracy $\varepsilon$ , (ii) pin down the best achievable adaptivity (designing a single tester whose sample usage matches $n^*(q,\varepsilon)$ up to constants for every instance), and (iii) provide a sharp benchmark for lower bounds and algorithm design across qualitatively different regimes (e.g., near-uniform versus heavy-tailed or highly non-uniform references).

## Known Partial Results

- Valiant and Valiant (2014) introduced the instance-optimal identity-testing formulation and gave upper and lower bounds on $n^*(q,\varepsilon)$ expressed via an $\ell_{2/3}$ -type quantity applied to a suitable truncation of the reference distribution $q$ .

- In this line of work, the $\ell_{2/3}$ quasi-norm is typically written as $\|v\|_{2/3}:=(\sum_i |v_i|^{2/3})^{3/2}$ for a nonnegative vector $v$ .

- The resulting upper and lower bounds do not, in general, match within constant factors: for some choices of $q$ the multiplicative gap between the best known upper and lower bounds can be arbitrarily large.

- Consequently, the identification of the correct functional $\Phi(q,\varepsilon)$ that tightly characterizes $n^*(q,\varepsilon)$ up to universal constant factors remains open.

## References

[1]

 [Open Problem: Tight Characterization of Instance-Optimal Identity Testing](https://proceedings.mlr.press/v247/canonne24a.html) 

ClÃ©ment Canonne (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/canonne24a.html) [2]

 [Open Problem: Tight Characterization of Instance-Optimal Identity Testing (PDF)](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf) 

ClÃ©ment Canonne (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf)

## Notes / Progress

_Work log goes here._
