# Nonasymptotic guarantees for bagged regularized M-estimators

**Status:** Unsolved  
**Source:** Sourced from the work of Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #53 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Formal setup (matching the paper): under Assumptions A--D, let $X\in\mathbb R^{n\times p}$ have i.i.d. $N(0,1/p)$ entries, $y=X\theta+z$ with i.i.d. signal coordinates from $F_\theta$ and i.i.d. noise coordinates from $F_z$ , and subsample index sets $I_m\subset[n]$ (with $|I_m|=k_m$ ) drawn independently as in Assumption B. For each $m\in[M]$ , train the residual-loss regularized estimator

$
\hat\theta_m\in\arg\min_{b\in\mathbb R^p}\Big\{\sum_{i\in I_m}\mathrm{loss}_m\big(y_i-x_i^\top b\big)+\sum_{j=1}^p\mathrm{reg}_m(b_j)\Big\},
$

where each $(\mathrm{loss}_m,\mathrm{reg}_m)$ satisfies Assumption C, and Assumption D gives the additional moment/regularity conditions used in the risk-limit theory. Define the bagged estimator $\hat\theta_M:=M^{-1}\sum_{m=1}^M\hat\theta_m$ and the squared excess prediction risk

$
R_M:=\frac1p\|\hat\theta_M-\theta\|_2^2
=\mathbb E\!\left[(x_0^\top\hat\theta_M-x_0^\top\theta)^2\mid X,y,\{I_m\}_{m=1}^M\right],
$

for $x_0\sim N(0,I_p/p)$ independent of training data. (When $\mathbb E[Z^2]<\infty$ , full squared prediction risk adds the irreducible term $\mathbb E[Z^2]$ .) Let $\mathrm{EST}$ be the source's data-dependent risk estimator, and let $R_M^{\infty}$ denote the deterministic proportional-limit risk for the corresponding proportional-asymptotic regime.

This setup follows [Koriyama et al. (2025)](#references) .

### Unsolved Problem

The paper explicitly asks whether hyperparameters tuned by minimizing $\mathrm{EST}$ (e.g., subsample ratio and regularization level) are close to oracle hyperparameters minimizing true excess risk $p^{-1}\|\hat\theta_M-\theta\|_2^2$ (or its deterministic limit $R_M^{\infty}$ ), and notes this would require suitable smoothness (e.g., Holder/Lipschitz) of excess risk or its limit as a function of hyperparameters. A stronger target, proposed here as an extension, is a uniform nonasymptotic guarantee over a tuning class $\mathcal T_n$ :

$
\mathbb P\!\left(\sup_{t\in\mathcal T_n}|\widehat R_n(t)-R_n(t)|>\varepsilon_n\right)\le\delta_n,
$

for an appropriate finite-sample risk proxy $\widehat R_n$ (e.g., $\mathrm{EST}$ -type criteria), with explicit rates in $(n,p,M,k,\lambda)$ . Broader formulations (anisotropic designs, deterministic signals, non-separable penalties, or beyond the Assumptions A--D regime) should be treated as extensions beyond this core problem statement.

## Significance & Implications

The paper gives precise proportional asymptotics and a consistent risk estimator, but practical tuning requires finite-sample control of the oracle gap. Proving nonasymptotic guarantees for estimator-based tuning would connect asymptotic risk formulas to defensible hyperparameter selection at realistic sample sizes.

## Known Partial Results

Under Assumptions A--D, the paper proves deterministic proportional-limit formulas for squared excess prediction risk (including heterogeneous ensembles) and establishes consistency of a data-dependent risk estimator (Corollary 6), but does not provide general uniform nonasymptotic oracle-tuning guarantees.

## References

[1]

 [Precise Asymptotics of Bagging Regularized M-estimators](https://arxiv.org/abs/2409.15252) 

Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec (2025)

Annals of Statistics (in press)

📍 Section 3.4, paragraph immediately after Corollary 6 and equation (14), beginning "A natural question arising from the above discussion is whether hyperparameters..." (p. 16 in arXiv v3).

Primary source paper; listed on Annals of Statistics Future Papers as in press (no final volume/issue pages or journal DOI publicly listed ).

 [Link ↗](https://arxiv.org/abs/2409.15252) [arXiv ↗](https://arxiv.org/abs/2409.15252v3)

## Notes / Progress

_Work log goes here._
