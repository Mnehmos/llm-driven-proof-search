# Remove polylogarithmic slack in attainable two-point rates

**Status:** Unsolved  
**Source:** Sourced from the work of Spencer Compton, Gregory Valiant

## Categories

- Mathematical Statistics
- Information Theory
- Combinatorics & Graph Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #72 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal{F}$ be the class of all probability distributions $P$ on $\mathbb{R}$ such that $P$ has a density of the form

$
p(x)=\int_{\Theta} g_\theta(x-\mu)\,d\Pi(\theta),
$

where $\mu\in\mathbb{R}$ , $\Pi$ is a probability measure on an index set $\Theta$ , and for every $\theta\in\Theta$ , $g_\theta$ is a probability density on $\mathbb{R}$ that is symmetric and log-concave about $0$ (equivalently, $g_\theta(t)=g_\theta(-t)$ for all $t$ , and $\log g_\theta$ is concave on its support). Then each component has mean $0$ , so $\mu(P):=\mathbb{E}_P[X]=\mu$ is well-defined. In the adaptive estimation model, one observes $X_1,\dots,X_n \stackrel{\mathrm{i.i.d.}}{\sim} P$ with unknown $P\in\mathcal{F}$ , and an estimator is any measurable map $\hat\mu_n:\mathbb{R}^n\to\mathbb{R}$ .

For distributions $P,Q$ on $\mathbb{R}$ , define squared Hellinger distance by $H^2(P,Q):=\frac12\int(\sqrt{dP/d\nu}-\sqrt{dQ/d\nu})^2\,d\nu$ , where $\nu$ dominates both $P$ and $Q$ . For $m\in\mathbb{N}$ , define the local Hellinger modulus at $P$ by

$
\omega_H(P,m):=\sup\left\{|\mu(Q)-\mu(P)|:Q\in\mathcal{F},\ H\!\left(P^{\otimes m},Q^{\otimes m}\right)\le \frac13\right\}.
$

(The constant $1/3$ can be replaced by any fixed number in $(0,1)$ at the cost of universal constant changes.)

### Unsolved Problem

Does there exist an estimator sequence $(\hat\mu_n)_{n\ge1}$ and universal constants $C,c>0$ such that for every $n\ge1$ and every $P\in\mathcal{F}$ ,

$
\mathbb{E}_P\!\left[|\hat\mu_n-\mu(P)|\right]\le C\,\omega_H\!\left(P,\lfloor c n\rfloor\right),
$

with no extra multiplicative polylogarithmic factor (for example, no factor of the form $(\log n)^k$ )?

## Significance & Implications

The paper’s benchmark is near-attainment up to polylogarithmic factors, leaving open whether exact constant-factor attainability is possible. Resolving this would clarify whether the remaining gap is information-theoretic or an artifact of current methods. This entry treats the question as open based on the cited source.

## Known Partial Results

The paper gives a near-linear-time, parameter-free estimator with guarantees matching the two-point modulus up to polylogarithmic factors over a broad log-concave-mixture location class; it does not claim exact constant-factor matching. Open-status annotation here is dated 2026-02-17 and may be outdated without a dedicated follow-up literature check.

## References

[1]

 [Attainability of Two-Point Testing Rates for Finite-Sample Location Estimation](https://arxiv.org/abs/2502.05730) 

Spencer Compton, Gregory Valiant (2025)

Annals of Statistics (to appear)

📍 arXiv:2502.05730v3, Section 6 (Discussion), open-questions paragraph on removing polylogarithmic slack in adaptive attainability (see the explicit open-question statement in that section).

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2502.05730) [DOI ↗](https://doi.org/10.48550/arXiv.2502.05730) [arXiv ↗](https://arxiv.org/abs/2502.05730)

## Notes / Progress

_Work log goes here._
