# Finite-sample valid fast QMC confidence intervals without integrand bounds

**Status:** Unsolved  
**Source:** Sourced from the work of Zexin Pan

## Categories

- Mathematical Statistics
- Probability Theory
- Analysis & PDEs

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #83 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $s\ge 1$ and fix a confidence level $1-\alpha\in(0,1)$ . For each integer $m=2^M$ , let $P^{(1)},\dots,P^{(r)}$ be $r$ independent linearly scrambled digital nets in $[0,1]^s$ , each of size $m$ , and define

$
\widehat\mu_{m,j}=\frac1m\sum_{x\in P^{(j)}} f(x),\qquad j=1,\dots,r,
$

as randomized quasi-Monte Carlo estimators of

$
\mu=\int_{[0,1]^s} f(x)\,dx.
$

Assume $f$ belongs to a smooth class for which linearly scrambled digital nets can beat the Monte Carlo rate $m^{-1/2}$ (for example, the infinitely differentiable classes analyzed in the source paper).

### Unsolved Problem

Construct a confidence-interval procedure

$
I_{m,r}=I_{m,r}(\widehat\mu_{m,1},\dots,\widehat\mu_{m,r})
$

that simultaneously satisfies all three goals below:

- 

finite-sample validity: $\mathbb P_f(\mu\in I_{m,r})\ge 1-\alpha$ for every $m,r$ and every admissible $f$ ;

- 

QMC efficiency: the interval width shrinks at a genuine QMC rate, in particular faster than $m^{-1/2}$ under the source paper's smoothness assumptions;

- 

no known envelope assumption: the procedure does not require an a priori known bound on $f$ (or on the derivatives used to certify such a bound).

The source paper explicitly notes that this combination of honest finite-sample coverage and faster-than-Monte-Carlo behavior remains unresolved.

## Significance & Implications

QMC can substantially outperform ordinary Monte Carlo on smooth integrands, but practitioners still lack interval procedures that are both honest at finite sample and able to preserve that speedup without requiring hard-to-obtain global bounds on the integrand. Resolving this would close a central uncertainty-quantification gap in high-dimensional numerical integration.

## Known Partial Results

- [Loh (2003)] establishes asymptotic normality for Owen-scrambled nets under classical restrictions, supporting t-intervals in that setting.

- [Nakayama & Tuffin (2024)] derive sufficient conditions for CLTs and confidence intervals for randomized QMC when the number of independent replicates grows with sample size.

- [Jain et al. (2025)] provide empirical-Bernstein and betting intervals with finite-sample guarantees and faster-than-MC convergence when explicit integrand bounds are known.

- [Pan (2025/2026)] proves asymptotically valid quantile-based intervals for linearly scrambled nets on smooth classes, but explicitly leaves the finite-sample/no-known-bounds combination open.

## References

[1]

 [Quasi-Monte Carlo confidence intervals using quantiles of randomized nets](https://arxiv.org/abs/2504.19138v2) 

Zexin Pan (2025)

Annals of Statistics (to appear)

📍 Final discussion paragraph before Acknowledgments, p. 30 in arXiv v2.

Source paper where the interval-design problem is posed.

 [Link ↗](https://arxiv.org/abs/2504.19138v2) [DOI ↗](https://doi.org/10.48550/arXiv.2504.19138) [arXiv ↗](https://arxiv.org/abs/2504.19138v2) [2]

 [Empirical Bernstein and betting confidence intervals for randomized quasi-Monte Carlo](https://arxiv.org/abs/2504.18677v2) 

A. Jain, F. J. Hickernell, A. B. Owen, A. G. Sorokin (2025)

arXiv preprint

📍 Cited in the source paper's final discussion paragraph on p. 30 as the bounded-integrand interval that already gives finite-sample guarantees and faster-than-MC convergence.

Provides finite-sample empirical-Bernstein and betting intervals when explicit integrand bounds are available.

 [Link ↗](https://arxiv.org/abs/2504.18677v2) [DOI ↗](https://doi.org/10.48550/arXiv.2504.18677) [arXiv ↗](https://arxiv.org/abs/2504.18677v2) [3]

 [On the asymptotic distribution of scrambled net quadrature](https://scholar.google.com/scholar?q=On%20the%20asymptotic%20distribution%20of%20scrambled%20net%20quadrature) 

W.-L. Loh (2003)

Annals of Statistics

Classical asymptotic-normality result underlying t-intervals for scrambled nets.

[4]

 [Sufficient conditions for central limit theorems and confidence intervals for randomized quasi-monte carlo methods](https://scholar.google.com/scholar?q=Sufficient%20conditions%20for%20central%20limit%20theorems%20and%20confidence%20intervals%20for%20randomized%20quasi-monte%20carlo%20methods) 

M. K. Nakayama, B. Tuffin (2024)

ACM Transactions on Modeling and Computer Simulation

Gives CLT and confidence-interval conditions for randomized QMC with growing replicate counts.

## Notes / Progress

_Work log goes here._
