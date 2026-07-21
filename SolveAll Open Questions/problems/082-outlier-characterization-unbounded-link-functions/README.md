# Outlier characterization for unbounded link functions (e.g., phase retrieval)

**Status:** Unsolved  
**Source:** Sourced from the work of Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #82 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(d,n)\to\infty$ with $n/d\to\alpha\in(0,\infty)$ . For each $d$ , let $Y_1,\dots,Y_n\in\mathbb{R}^d$ be i.i.d. samples from a $k$ -component Gaussian mixture

$
Y=\mu_{Z}+g,\qquad \mathbb{P}(Z=a)=\pi_a,\ \pi_a>0,\ \sum_{a=1}^k\pi_a=1,\ g\sim\mathcal{N}(0,I_d),
$

where $\mu_1,\dots,\mu_k\in\mathbb{R}^d$ are deterministic class means with $\|\mu_a\|=O(1)$ . Let $X=[x_1,\dots,x_p]\in\mathbb{R}^{d\times p}$ be deterministic with $\|x_j\|=O(1)$ , and define the projected feature $U_\ell=X^\top Y_\ell\in\mathbb{R}^p$ .

This setup follows [Arous et al. (2025)](#references) .

Consider random matrices of Hessian/information type

$
M_n=\frac1n\sum_{\ell=1}^n w(U_\ell)\,Y_\ell Y_\ell^\top,
$

where $w:\mathbb{R}^p\to\mathbb{R}$ is measurable and may be unbounded (for example, $w(u)$ growing polynomially; in phase retrieval-type models one gets $w(u)\asymp u^2$ in the single-index case $p=1$ ). Let $S=\mathrm{span}\{x_1,\dots,x_p,\mu_1,\dots,\mu_k\}$ and $r=\dim S\le p+k$ . Assume the empirical spectral distribution of $M_n$ converges almost surely to a deterministic law $\nu$ whose support is not bounded above.

### Unsolved Problem

In bounded-support settings, outliers are characterized by eigenvalues separating to the right of the finite bulk edge. Here no finite right edge exists. Motivated by the open-direction discussion in the source paper, formulate a replacement theory in this unbounded-support regime:

- 

Give necessary and sufficient conditions, in terms of $(\alpha,\pi_a,\mu_a,X,w)$ (equivalently the finite-dimensional Gram data of signal directions plus the link-induced moments), for existence of finitely many spike-generated eigenvalues of $M_n$ that are spectrally distinguishable from the background spectrum despite $\sup\mathrm{supp}(\nu)=\infty$ .

- 

Prove deterministic asymptotic formulas for those eigenvalues and for eigenvector alignment with $S$ , i.e. limits of quantities like $\|P_S v_j\|^2$ for corresponding unit eigenvectors $v_j$ .

- 

Identify an appropriate notion of "isolation" when the bulk has unbounded support (for example, separation from the unspiked comparison model at the relevant extreme-value scale) and establish a BBP-type phase transition criterion under that notion.

See *Local geometry of high-dimensional mixture models: Effective spectral theory and dynamical transitions* (arXiv:2502.15655v3) for context.

## Significance & Implications

Unbounded-link models (including phase-retrieval-type examples) arise naturally, while rigorous outlier characterizations in this line of work mainly rely on a finite right bulk edge. Extending those results to unbounded-support regimes would broaden the currently analyzable model class.

## Known Partial Results

The paper develops effective bulk analysis beyond uniformly bounded links, but its outlier arguments are tied to separation past a finite right bulk edge; a full unbounded-support outlier theory is left open (as of February 25, 2025, in arXiv:2502.15655v3).

## References

[1]

 [Local geometry of high-dimensional mixture models: Effective spectral theory and dynamical transitions](https://arxiv.org/abs/2502.15655v3) 

Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath (2025)

Annals of Statistics (to appear)

📍 arXiv v3, Section 1.5.2 (Parametric regression for the multi-index model), Remark 1.15

Source paper; Section 1.5.2 and Remark 1.15 motivate the unbounded-link outlier characterization as an open direction.

 [Link ↗](https://arxiv.org/abs/2502.15655v3) [DOI ↗](https://doi.org/10.48550/arXiv.2502.15655) [arXiv ↗](https://arxiv.org/abs/2502.15655v3)

## Notes / Progress

_Work log goes here._
