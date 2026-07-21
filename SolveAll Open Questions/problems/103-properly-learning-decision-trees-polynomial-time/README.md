# Properly learning decision trees in polynomial time?

**Status:** Unsolved  
**Source:** Posed by Guy Blanc et al. (2022)

## Categories

- Learning Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #103 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $n,s\in\mathbb{N}$ and let $f:\{0,1\}^n\to\{0,1\}$ be an unknown Boolean function promised to be representable by a rooted Boolean decision tree with at most $s$ leaves (i.e., each internal node queries one input bit, and each leaf is labeled in $\{0,1\}$ ). Let $\mathcal{U}$ denote the uniform distribution over $\{0,1\}^n$ . A randomized *proper learner* is given $(n,s,\epsilon,\delta)$ and oracle access to *membership queries* for $f$ (on any adaptively chosen $x\in\{0,1\}^n$ , the oracle returns $f(x)$ ); since $\mathcal{U}$ is known, the learner may also generate independent samples $x\sim\mathcal{U}$ . The learner must output an explicit decision tree hypothesis $h:\{0,1\}^n\to\{0,1\}$ such that, with probability at least $1-\delta$ over its internal randomness, the uniform error is at most $\epsilon$ :

$
\Pr_{x\sim\mathcal{U}}[h(x)\neq f(x)]\le \epsilon.
$

### Unsolved Problem

Does there exist such a proper learning algorithm whose running time (and total number of membership queries) is bounded by $\mathrm{poly}(n,s,1/\epsilon,\log(1/\delta))$ ? Equivalently, can properly learning size- $s$ decision trees under $\mathcal{U}$ with membership queries be done in true polynomial time, improving over the best known quasipolynomial and almost-polynomial bounds?

## Significance & Implications

This is a canonical proper-learning benchmark: the output must be a decision tree (not an arbitrary hypothesis), so the goal is to recover an explicit structured model consistent with the decision-tree representation. Resolving whether polynomial-time proper learning is possible under the uniform distribution with membership queries would pin down the algorithmic complexity of a basic concept class and determine whether the current gap between almost-polynomial/quasipolynomial algorithms and a genuine $\mathrm{poly}(n,s,1/\epsilon)$ algorithm reflects an inherent barrier or is merely an artifact of existing techniques.

## Known Partial Results

- Blanc, Lange, Qiao, and Tan (BLQT21) gave an almost-polynomial-time membership-query algorithm for properly learning decision trees under the uniform distribution.

- Prior to BLQT21, the fastest known approach for this setting was quasipolynomial time, obtainable as a consequence of the classic distribution-free decision-tree learning algorithm of Ehrenfeucht and Haussler (EH89).

- The COLT 2022 open-problem note (Blanc, Lange, Qiao, Tan, 2022) isolates the remaining gap (almost-polynomial/quasipolynomial versus polynomial time) and discusses intermediate milestones as potential stepping stones.

## References

[1]

 [Open Problem: Properly learning decision trees in polynomial time?](https://proceedings.mlr.press/v178/open-problem-blanc22a.html) 

Guy Blanc, Jane Lange, Mingda Qiao, Li-Yang Tan (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-blanc22a.html) [2]

 [Open Problem: Properly learning decision trees in polynomial time? (PDF)](https://proceedings.mlr.press/v178/open-problem-blanc22a/open-problem-blanc22a.pdf) 

Guy Blanc, Jane Lange, Mingda Qiao, Li-Yang Tan (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-blanc22a/open-problem-blanc22a.pdf)

## Notes / Progress

_Work log goes here._
