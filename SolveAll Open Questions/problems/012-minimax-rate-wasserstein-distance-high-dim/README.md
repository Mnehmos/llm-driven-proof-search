# Minimax Rate for Wasserstein Distance Estimation in High Dimensions

**Status:** Unsolved  
**Importance:** Notable

## Categories

- Mathematical Statistics
- Probability Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #12 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix $d \in \mathbb{N}$ , $p \ge 1$ , and sample sizes $n,m \in \mathbb{N}$ . Let $\mathcal{P}_d$ be the set of all Borel probability measures on $[0,1]^d \subset \mathbb{R}^d$ . For $P,Q \in \mathcal{P}_d$ , define the $p$ -Wasserstein distance

$
W_p(P,Q):=\left(\inf_{\pi \in \Pi(P,Q)} \int_{[0,1]^d \times [0,1]^d} \|x-y\|_2^p \, d\pi(x,y)\right)^{1/p},
$

where $\Pi(P,Q)$ is the set of all couplings of $P$ and $Q$ .

Assume we observe independent samples $X_1,\dots,X_n \stackrel{\mathrm{i.i.d.}}{\sim} P$ and $Y_1,\dots,Y_m \stackrel{\mathrm{i.i.d.}}{\sim} Q$ , with the $X$ -sample independent of the $Y$ -sample. An estimator of $W_p(P,Q)$ is any measurable map $\widehat W=\widehat W(X_1,\dots,X_n,Y_1,\dots,Y_m) \in \mathbb{R}$ . Its worst-case squared-error risk over $\mathcal{P}_d$ is

$
\mathcal{R}_{n,m,d,p}(\widehat W):=\sup_{P,Q \in \mathcal{P}_d} \mathbb{E}_{P^n \otimes Q^m}\!\left[\left(\widehat W-W_p(P,Q)\right)^2\right].
$

Define the minimax risk

$
\mathfrak{M}_{n,m,d,p}:=\inf_{\widehat W}\mathcal{R}_{n,m,d,p}(\widehat W).
$

### Unsolved Problem

Determine the sharp dependence of $\mathfrak{M}_{n,m,d,p}$ on $(n,m,d,p)$ (up to constants, and logarithmic factors where unavoidable) for the full class $\mathcal{P}_d$ . A key distinction is between: (1) rates for empirical-measure approximation ( $W_p(P_n,P)$ and $W_p(Q_m,Q)$ ), and (2) rates for direct estimation of the functional $W_p(P,Q)$ from samples. In high dimension (notably regimes like $d>2p$ ), does the empirical plug-in estimator

$
\widehat W_{\mathrm{emp}}:=W_p(P_n,Q_m), \qquad P_n:=\frac1n\sum_{i=1}^n \delta_{X_i}, \quad Q_m:=\frac1m\sum_{j=1}^n \delta_{Y_j},
$

achieve minimax-optimal squared risk over unrestricted $\mathcal{P}_d$ , or can one do strictly better (possibly under additional smoothness/separation assumptions)? Current literature does not resolve this for the fully nonparametric class.

## Significance & Implications

Optimal transport and Wasserstein distances are central in statistics and machine learning. For unrestricted high-dimensional distributions, empirical Wasserstein convergence shows strong dimensional effects (with regime changes around $d=2p$ ), but those results do not by themselves settle minimax optimality for direct estimation of $W_p(P,Q)$ under squared loss. Clarifying this gap is important both theoretically and for practical sample-complexity guidance.

## Known Partial Results

- Empirical-measure estimation (not direct functional estimation): [Weed & Bach (2019)](#references) gives sharp benchmark rates for $\mathbb{E}W_p(P_n,P)$ over broad classes on $[0,1]^d$ , with regime split at $d=2p$ : typically $n^{-1/2}$ for $d<2p$ , $n^{-1/2}(\log n)^{1/p}$ at $d=2p$ , and $n^{-1/d}$ for $d>2p$ (for unsquared loss; squared-loss exponents double).

- Plug-in implications for $W_p(P,Q)$ : triangle-inequality arguments transfer empirical-measure upper bounds to $|W_p(P_n,Q_m)-W_p(P,Q)|$ , but these are indirect and do not by themselves prove minimax optimality for direct functional estimation under squared risk.

- Direct Wasserstein-functional estimation: [Niles-Weed & Rigollet (2022)](#references) provides model-based lower/upper bounds (spiked transport model) showing nontrivial gaps and that structure can help, without resolving the unrestricted minimax rate over all $\mathcal P_d$ .

- Smooth-cost / separation regimes: [Manole & Niles-Weed (2024)](#references) establishes sharp empirical OT rates under smooth-cost regularity assumptions; these results clarify favorable structured regimes but do not close the general worst-case two-sample functional-estimation question.

- Current status: the full minimax characterization for estimating $W_p(P,Q)$ over unrestricted $\mathcal P_d$ remains open, especially in high-dimensional regimes such as $d>2p$ .

## References

[1]

 [Estimation of Wasserstein distances in the spiked transport model](https://arxiv.org/abs/1909.07513) 

Jonathan Niles-Weed, Philippe Rigollet (2022)

Bernoulli

📍 Section 3.3 (Lower bounds), paragraph after Theorem 3 (states that closing the rate gap for Wasserstein-distance estimation is a fundamental open question).

 [arXiv ↗](https://arxiv.org/abs/1909.07513) [2]

 [Sharp convergence rates for empirical optimal transport with smooth costs](https://arxiv.org/abs/2106.13181) 

Tudor Manole, Jonathan Niles-Weed (2024)

Annals of Applied Probability

 [arXiv ↗](https://arxiv.org/abs/2106.13181) [3]

 [Sharp asymptotic and finite-sample rates of convergence of empirical measures in Wasserstein distance](https://doi.org/10.3150/18-BEJ1065) 

Jonathan Weed, Francis Bach (2019)

Bernoulli

📍 Sections 1 and 3 (dimension-dependent rates for empirical-measure convergence in $W_p$, including low-dimensional boundary-log behavior).

 [DOI ↗](https://doi.org/10.3150/18-BEJ1065)

## Notes / Progress

_Work log goes here._
