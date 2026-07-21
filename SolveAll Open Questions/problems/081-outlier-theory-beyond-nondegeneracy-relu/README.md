# Outlier theory beyond non-degeneracy/invertibility assumptions (ReLU and zero diagonal entries)

**Status:** Unsolved  
**Source:** Sourced from the work of Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #81 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

In the high-dimensional regime $d,n\to\infty$ with $n/d\to\alpha\in(0,\infty)$ , consider weighted sample-covariance/Hessian-type matrices of the form $H_n=\frac1n\sum_{\ell=1}^n D_{\ell\ell}y_\ell y_\ell^\top$ arising from Gaussian-mixture features and data-dependent diagonal gates $D_{\ell\ell}=w(s_\ell)$ . Existing outlier analyses in this line of work typically assume non-degeneracy/invertibility-type conditions on effective diagonal weights.

### Unsolved Problem

In the high-dimensional regime $d,n\to\infty$ with $n/d\to\alpha\in(0,\infty)$ , for weighted sample-covariance/Hessian-type matrices of the form $H_n=\frac1n\sum_{\ell=1}^n D_{\ell\ell}y_\ell y_\ell^\top$ arising from Gaussian-mixture features and data-dependent diagonal gates $D_{\ell\ell}=w(s_\ell)$ , develop an outlier theory when $\mathbb P(D_{\ell\ell}=0)>0$ : characterize limiting outlier locations and eigenvector alignments, and identify outlier phase transitions, without assuming diagonal weights are bounded away from zero.

## Significance & Implications

Extending the theory to ReLU-like degeneracy would broaden applicability of existing spectral results to commonly used gated models.

## Known Partial Results

The source develops bulk/outlier results under non-degeneracy assumptions and indicates that the zero-mass (ReLU-type) degenerate case must be treated separately; no complete treatment of that degenerate extension is provided there.

## References

[1]

 [Local geometry of high-dimensional mixture models: Effective spectral theory and dynamical transitions](https://arxiv.org/abs/2502.15655v3) 

Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath (2025)

Annals of Statistics (to appear)

📍 Section 1.5.1 (Multi-layer GMM classification); Remark 1.14.

Source paper where this problem appears. Metadata convention: `year` records the initial preprint year (2025), while this entry cites version `v3` dated January 22, 2026.

 [Link ↗](https://arxiv.org/abs/2502.15655v3) [arXiv ↗](https://arxiv.org/abs/2502.15655v3)

## Notes / Progress

_Work log goes here._
