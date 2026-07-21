# Characterize adaptive distribution classes where two-point rates are attainable

**Status:** Unsolved  
**Source:** Sourced from the work of Spencer Compton, Gregory Valiant

## Categories

- Mathematical Statistics
- Information Theory
- Combinatorics & Graph Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #71 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal F$ be a nonempty class of probability distributions on $\mathbb R$ such that every $P\in\mathcal F$ has finite mean $\mu(P):=\int x\,dP(x)$ , and $\mathcal F$ is translation-invariant in the sense that for every $P\in\mathcal F$ and every $t\in\mathbb R$ , the translated law $P_t$ of $X+t$ (for $X\sim P$ ) also belongs to $\mathcal F$ . For $P,Q$ on $\mathbb R$ , define squared Hellinger distance by

$
H^2(P,Q):=1-\int \sqrt{\frac{dP}{d\lambda}\frac{dQ}{d\lambda}}\,d\lambda,
$

where $\lambda$ is any common dominating measure (the value is independent of $\lambda$ ). For $m\in\mathbb N$ , let $P^{\otimes m}$ denote the $m$ -fold product law, and define the local $m$ -sample Hellinger modulus for mean estimation at $P$ by

$
\omega_H(P,m):=\sup\Big\{|\mu(Q)-\mu(P)|:Q\in\mathcal F,\ H^2\!\big(P^{\otimes m},Q^{\otimes m}\big)\le \tfrac14\Big\}.
$

(Any fixed constant in $(0,1)$ in place of $\tfrac14$ is equivalent up to absolute-constant rescaling of sample size.)

Given i.i.d. data $X_1,\dots,X_n\sim P$ with unknown $P\in\mathcal F$ , an estimator is any measurable map $\hat\mu_n=\hat\mu_n(X_1,\dots,X_n)\in\mathbb R$ .

### Unsolved Problem

Determine exactly those translation-invariant classes $\mathcal F$ for which there exists a single sequence of estimators $\{\hat\mu_n\}_{n\ge2}$ and constants $C,k,c>0$ such that

$
\sup_{P\in\mathcal F}\frac{\mathbb E_P\!\left[\,|\hat\mu_n-\mu(P)|\,\right]}{\omega_H\!\big(P,\max\{1,\lfloor cn\rfloor\}\big)}
\le C(\log n)^k
\quad\text{for all }n\ge2.
$

Equivalently, determine necessary and sufficient conditions on $\mathcal F$ under which adaptive mean estimation over $\mathcal F$ can match, uniformly over $P$ , the two-point-testing lower-bound scale given by the local Hellinger modulus, up to polylogarithmic factors.

## Significance & Implications

[Compton & Valiant (2025)](#references) gives both positive and negative attainability results for different classes, indicating a nontrivial phase boundary. A full characterization would unify these examples and reveal the structural property that governs whether Le Cam two-point lower bounds are algorithmically achievable in adaptive mean estimation.

## Known Partial Results

This paper gives a near-attainability result for mixtures of symmetric log-concave distributions with a common mean, and a non-attainability result even for symmetric unimodal distributions. These establish that attainability is class-dependent but do not provide a complete necessary-and-sufficient characterization; the problem appears open.

## References

[1]

 [Attainability of Two-Point Testing Rates for Finite-Sample Location Estimation](https://arxiv.org/abs/2502.05730v3) 

Spencer Compton, Gregory Valiant (2025)

Annals of Statistics (to appear)

📍 Section 6 (Discussion), Question 1, p. 30: "Characterize adaptive distribution classes where two-point rates are attainable."

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2502.05730v3) [DOI ↗](https://doi.org/10.48550/arXiv.2502.05730) [arXiv ↗](https://arxiv.org/abs/2502.05730v3)

## Notes / Progress

_Work log goes here._
