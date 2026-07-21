# Overparameterized optimal subsample size for infinite-ensemble subagging

**Status:** Unsolved  
**Source:** Sourced from the work of Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #52 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Assume the homogeneous subagging setup studied in Koriyama et al.: i.i.d. data $(x_i,y_i)_{i=1}^n$ in proportional asymptotics ( $n,p\to\infty$ with $p/n\to\gamma\in(0,\infty)$ ), with Gaussian design $x_i\sim N(0,I_p/p)$ , linear signal-plus-noise response $y_i=x_i^\top\theta+z_i$ , and finite second moments for signal/noise. Base learners are regularized M-estimators with convex differentiable loss and convex penalty, trained on uniform subsamples of size $k$ , and the full-ensemble estimator is the $M\to\infty$ limit (conditional subsample expectation).

Let $\mathcal R_{n,p}(\lambda,k)$ denote squared prediction risk of the full-ensemble estimator, and let $k^\star_{n,p}(\lambda)\in\arg\min_{1\le k\le n}\mathcal R_{n,p}(\lambda,k)$ .

### Unsolved Problem

In the vanishing-regularization regime $\lambda=\lambda_{n,p}\to0^+$ , establish whether

$
\limsup_{n,p\to\infty}\frac{k^\star_{n,p}(\lambda_{n,p})}{\min\{n,p\}}\le 1
$

holds under the full generality of the M-estimation framework. Existing results/evidence separate into: (i) proved or analytically derived behavior in specific tractable cases (notably ridgeless/squared-loss settings), (ii) empirical/numerical evidence in other cases (including lasso-type settings), and (iii) the unresolved unified conjecture across general losses/penalties.

For sequences with $p, the limsup formulation to test is correspondingly

$
\limsup_{n,p\to\infty,\,p

rather than a pointwise eventual inequality.

## Significance & Implications

This would formalize when implicit regularization from subagging alone is sufficient to control prediction error without explicit penalization. A proof would clarify phase transitions in optimal subsampling and provide principled guidance for choosing $k$ in modern high-dimensional regimes. See Koriyama et al. for the current asymptotic formulas and evidence.

## Known Partial Results

Koriyama et al. provide precise asymptotic risk characterizations for subagged regularized M-estimators. In specialized tractable regimes (notably ridgeless/squared-loss settings), the formulas support overparameterized-optimal- $k$ behavior; for broader settings (including lassoless/lasso-type cases), the paper presents supportive numerical evidence but not a single theorem covering all losses/penalties under vanishing regularization.

## References

[1]

 [Precise Asymptotics of Bagging Regularized M-estimators](https://arxiv.org/abs/2409.15252) 

Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec (2025)

Annals of Statistics (future paper; to appear)

📍 Section 5.2 ("Optimal subsample size"), first paragraph and Figure 5 discussion of $k^\star$ shifting toward the overparameterized regime for vanishing explicit regularization (arXiv v3 dated 2025-09-27; canonical citation uses base arXiv id).

Primary source; IMS Annals of Statistics future-papers listing and arXiv preprint (latest public revision v3).

 [Link ↗](https://arxiv.org/abs/2409.15252) [arXiv ↗](https://arxiv.org/abs/2409.15252)

## Notes / Progress

_Work log goes here._
