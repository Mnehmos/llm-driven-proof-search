# Sharp boundary for attainability in finite-sample location models

**Status:** Unsolved  
**Source:** Sourced from the work of Spencer Compton, Gregory Valiant

## Categories

- Mathematical Statistics
- Information Theory
- Combinatorics & Graph Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #73 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $P_0$ be a Borel probability distribution on $\mathbb{R}$ with finite first moment and centered so that $\int x\,dP_0(x)=0$ . For each shift parameter $\theta\in\mathbb{R}$ , define the location family member $P_\theta$ by $P_\theta(A)=P_0(A-\theta)$ for all Borel sets $A\subseteq\mathbb{R}$ . Given $n$ i.i.d. observations $X_1,\dots,X_n\sim P_{\theta^\star}$ with unknown $\theta^\star$ , an estimator is any measurable map $\hat\theta_n:\mathbb{R}^n\to\mathbb{R}$ .

Define worst-case absolute-error risk

$
R_n(\hat\theta_n;P_0)=\sup_{\theta\in\mathbb{R}}\mathbb{E}_{P_\theta^{\otimes n}}\!\left[\,|\hat\theta_n-\theta|\,\right],
$

and minimax risk $R_n^\star(P_0)=\inf_{\hat\theta_n}R_n(\hat\theta_n;P_0)$ .

For probability measures $P,Q$ on $\mathbb{R}$ , define squared Hellinger distance

$
H^2(P,Q)=1-\int \sqrt{\frac{dP}{d\mu}\frac{dQ}{d\mu}}\,d\mu,
$

where $\mu$ is any dominating measure (this value is independent of $\mu$ ). Define the location-model Hellinger modulus for real effective sample size $t\ge 1$ by

$
\omega_{P_0}(t)=\sup\left\{|\delta|:\ H^2(P_0,P_\delta)\le \frac{1}{t}\right\}.
$

(For integer $t=m$ , this matches the usual sample-size- $m$ two-point-testing benchmark up to universal constants via Le Cam lower bounds.)

Say the two-point rate is near-attainable for this fixed base distribution $P_0$ if there exist constants $C>0$ , $a,b\ge 0$ , and estimators $\{\hat\theta_n\}_{n\ge 2}$ such that for all $n\ge 2$ ,

$
R_n(\hat\theta_n;P_0)\le C(\log n)^a\,\omega_{P_0}\!\left(\frac{n}{(\log n)^b}\right).
$

Equivalently: for this $P_0$ , estimation error matches the Hellinger-modulus lower bound up to polylogarithmic factors and a $\tilde O(n)$ effective sample-size loss.

### Unsolved Problem

Determine a necessary-and-sufficient condition on $P_0$ for this near-attainability property to hold.

## Significance & Implications

Compton & Valiant (arXiv:2502.05730, v3 dated 2026-01-04) give positive and negative finite-sample attainability results in related shape-constrained settings, but do not provide a full iff characterization over base laws $P_0$ for this location-model criterion. A sharp criterion would complete the one-dimensional finite-sample picture and identify exactly which distributional geometries permit near-attainment of the two-point benchmark. This problem remains open under currently cited sources.

## Known Partial Results

For the known- $P_0$ location setting, the paper proves near-attainability guarantees for unimodal base distributions under its stated theorem assumptions (up to polylog factors). Separately, its symmetric-distribution lower bound is existential/non-uniform over the class (for each sample size, there exist symmetric examples with large gaps from the two-point benchmark), so it should not be read as saying every symmetric $P_0$ fails near-attainability. A complete necessary-and-sufficient characterization for fixed $P_0$ is not provided there and remains open.

## References

[1]

 [Attainability of Two-Point Testing Rates for Finite-Sample Location Estimation](https://arxiv.org/abs/2502.05730) 

Spencer Compton, Gregory Valiant (2025)

Annals of Statistics (to appear)

📍 Section 6 (Discussion), avenue "Adaptive location estimation for more general distributions", p. 56 (arXiv v3, 2026-01-04)

Primary source paper discussing this open direction.

 [Link ↗](https://arxiv.org/abs/2502.05730) [DOI ↗](https://doi.org/10.48550/arXiv.2502.05730) [arXiv ↗](https://arxiv.org/abs/2502.05730)

## Notes / Progress

_Work log goes here._
