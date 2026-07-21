# Remove the Polylogarithmic Gap to Exact Minimax Optimality

**Status:** Unsolved  
**Source:** Sourced from the work of Kaizheng Wang

## Categories

- Mathematical Statistics
- Learning Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #35 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal X$ be an input space and $K:\mathcal X\times\mathcal X\to\mathbb R$ a symmetric positive-semidefinite kernel with RKHS $\mathcal H$ and feature map $\phi:\mathcal X\to\mathcal H$ (so $K(x,z)=\langle\phi(x),\phi(z)\rangle_{\mathcal H}$ ). Observe independent datasets:

$
\mathcal D_s=\{(X_i,Y_i)\}_{i=1}^n\ \text{i.i.d. from source law }P,\qquad
\mathcal D_t=\{X_{0i}\}_{i=1}^{n_0}\ \text{i.i.d. from target covariate law }Q_X,
$

where target labels in the target sample are unobserved.

This setup follows [Wang (2023)](#references) .

Assume a common regression function under covariate shift:

$
f^\star(x)=\mathbb E[Y\mid X=x]=\mathbb E[Y_0\mid X_0=x]=\langle\phi(x),\theta^\star\rangle_{\mathcal H}
$

for some $\theta^\star\in\mathcal H$ , with $P_X\neq Q_X$ allowed. Define

$
\mathcal F=\{f_\theta:\ f_\theta(x)=\langle\phi(x),\theta\rangle_{\mathcal H},\ \theta\in\mathcal H\},
$

$
\mathcal R_Q(f):=\mathbb E[(f(X_0)-Y_0)^2],\qquad
\mathcal R_Q(f)-\mathcal R_Q(f^\star)=\mathbb E_{X_0\sim Q_X}[(f(X_0)-f^\star(X_0))^2].
$

For $\lambda>0$ , kernel ridge regression on source labels is

$
\widehat f_\lambda\in\arg\min_{f\in\mathcal F}\Big\{\frac1n\sum_{i=1}^n(f(X_i)-Y_i)^2+\lambda\|f\|_{\mathcal F}^2\Big\}.
$

Assume there exist constants $R,\sigma,M>0$ such that $|f^\star(X)|\le R$ almost surely, noise $\eta:=Y-f^\star(X)$ is conditionally $\sigma$ -sub-Gaussian given $X$ , and either $\|\phi(X)\|_{\mathcal H}\le M$ almost surely or $\phi(X)$ is strongly sub-Gaussian in $\mathcal H$ with proxy $M$ . Define

$
\Sigma:=\mathbb E[\phi(X)\otimes\phi(X)],\qquad \Sigma_0:=\mathbb E[\phi(X_0)\otimes\phi(X_0)],\qquad \mu^2:=\max\{\sigma^2/R^2,\,M^2\},
$

and effective sample size

$
n_{\mathrm{eff}}:=\sup\{t\le n:\ t\Sigma_0\preceq n\Sigma+\mu^2 I\}.
$

The source proves (up to polylogarithmic factors) a high-probability upper bound of the form

$
\mathcal R_Q(\widehat f)-\mathcal R_Q(f^\star)
\lesssim
\inf_{\rho>0}\Big\{R^2\rho+\frac{\sigma^2}{n_{\mathrm{eff}}}\sum_{j\ge1}\frac{\mu_j}{\mu_j+\rho}\Big\}
+R^2\mu^2\big(n_{\mathrm{eff}}^{-1}+n_0^{-1}\big),
$

where $(\mu_j)$ are eigenvalues of $\Sigma_0$ .

### Unsolved Problem

Remove the remaining polylogarithmic gap. Determine whether one can (i) construct an estimator with a matching upper bound without extra polylog factors under the same assumptions, or (ii) prove a matching lower bound showing those log factors are unavoidable for this formulation.

## Significance & Implications

The paper's minimax discussion indicates matching rates up to polylogarithmic factors in the effective-sample-size regime. Resolving whether the remaining log gap is removable would sharpen the statistical optimality picture for pseudo-label-based adaptation and clarify whether the gap is methodological or intrinsic.

## Known Partial Results

In arXiv:2302.10160v4, Section 4, Theorem 4.1 ("Excess risk") proves non-asymptotic high-probability excess-risk bounds driven by the effective sample size $n_{\mathrm{eff}}$ . Corollary 4.1 gives explicit rates (finite-rank, exponential, polynomial spectral regimes) that are minimax-optimal up to polylogarithmic factors under the paper's assumptions. Section 4, Remark 3 ("Optimality and adaptivity") relates sharpness to Theorem 2 of Ma-Pathak-Wainwright (2023) in bounded-likelihood-ratio settings.

## References

[1]

 [Pseudo-Labeling for Kernel Ridge Regression under Covariate Shift](https://arxiv.org/abs/2302.10160v4) 

Kaizheng Wang (2023)

Annals of Statistics (accepted; forthcoming)

📍 Section 4: definition of effective sample size (Eq. (4.1) in the PDF), Theorem 4.1 ("Excess risk"), Corollary 4.1, and Remark 3 ("Optimality and adaptivity"); Section 7 for broader future directions.

Primary source for the minimax-up-to-polylog results. Year is recorded by arXiv first posting (2023), while v4 reflects a later revision.

 [Link ↗](https://arxiv.org/abs/2302.10160v4) [arXiv ↗](https://arxiv.org/abs/2302.10160v4) [2]

 [Optimally tackling covariate shift in RKHS-based nonparametric regression](https://doi.org/10.1214/23-AOS2268) 

Cong Ma, Reese Pathak, Martin J Wainwright (2023)

The Annals of Statistics

📍 Theorem 2 (minimax lower bound under bounded likelihood-ratio assumptions), as cited in Wang's Section 4 optimality remark.

Lower-bound benchmark cited by Wang for sharpness comparisons in bounded-likelihood-ratio regimes.

 [Link ↗](https://doi.org/10.1214/23-AOS2268) [DOI ↗](https://doi.org/10.1214/23-AOS2268)

## Notes / Progress

_Work log goes here._
