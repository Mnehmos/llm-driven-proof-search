# Uniform risk dominance of transformed Moore-Penrose estimators

**Status:** Unsolved  
**Source:** Sourced from the work of Taras Bodnar, Nestor Parolya

## Categories

- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #62 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

For each $n\in\mathbb{N}$ , let $p_n\in\mathbb{N}$ satisfy $p_n/n\to c$ for some constant $c\in(1,\infty)$ . Observe independent random vectors $X_{1,n},\dots,X_{n,n}\in\mathbb{R}^{p_n}$ of the form $X_{i,n}=\Sigma_n^{1/2}Z_{i,n}$ , where $\Sigma_n\in\mathbb{R}^{p_n\times p_n}$ is symmetric positive definite, $\mathbb{E}[Z_{i,n}]=0$ , $\mathbb{E}[Z_{i,n}Z_{i,n}^\top]=I_{p_n}$ , and moments are uniformly bounded (for example, $\sup_{n,i,j}\mathbb{E}|(Z_{i,n})_j|^{4+\delta}<\infty$ for some $\delta>0$ ). Define

$
S_n=\frac1n\sum_{i=1}^n X_{i,n}X_{i,n}^\top.
$

If $p_n>n$ , then $\operatorname{rank}(S_n)\le n deterministically, so $S_n$ is singular for every sample realization; let $S_n^\dagger$ denote its Moore-Penrose pseudoinverse.

This setup follows [Bodnar & Parolya (2024)](#references) .

Let $\mathcal{C}$ be a prescribed spectral class of covariance sequences $\Sigma=(\Sigma_n)_{n\ge1}$ , e.g. eigenvalues uniformly bounded away from $0$ and $\infty$ : there exist constants $0 such that $m\le\lambda_{\min}(\Sigma_n)\le\lambda_{\max}(\Sigma_n)\le M$ for all $n$ . For any estimator $\widehat\Theta_n$ of $\Sigma_n^{-1}$ , define Frobenius risk

$
R_n(\widehat\Theta_n;\Sigma_n)=\mathbb{E}_{\Sigma_n}\!\left[\|\widehat\Theta_n-\Sigma_n^{-1}\|_F^2\right].
$

Fix a benchmark class $\mathcal{B}$ of measurable estimators $\widehat\Theta_n^{(b)}$ , $b\in\mathcal{B}$ (e.g. ridge/linear-shrinkage families such as $(S_n+\lambda_n I_{p_n})^{-1}$ or $\alpha_n S_n^\dagger+\beta_n I_{p_n}$ , with deterministic or data-driven tuning). A transformed Moore-Penrose estimator is of the form

$
\widehat\Theta_n=T_n(S_n^\dagger),
$

with measurable data-driven $T_n$ .

Source-established result (Bodnar--Parolya, arXiv:2403.15792v2): asymptotic trace-moment formulas are derived and used to construct specific fully data-driven shrinkage estimators with asymptotic quadratic-loss optimality for those constructions.

### Unsolved Problem

Determine whether there exists $(T_n)$ such that

$
\limsup_{n\to\infty}\ \sup_{\Sigma\in\mathcal{C}}\ \sup_{b\in\mathcal{B}}
\Big\{R_n\!\big(T_n(S_n^\dagger);\Sigma_n\big)-R_n\!\big(\widehat\Theta_n^{(b)};\Sigma_n\big)\Big\}\le 0.
$

Equivalently: can a fully data-driven transformation of $S_n^\dagger$ uniformly match or beat every estimator in $\mathcal{B}$ over $\mathcal{C}$ when $p_n/n\to c>1$ ? This strengthened uniform-domination statement remains open.

## Significance & Implications

The often-quoted phrase that transformed Moore-Penrose estimators "seem" to perform similarly to or better than benchmarks is verifiably documented in the Linkoping University seminar abstract for this work (not asserted here as a proved theorem statement). Turning that empirical/heuristic claim into a uniform asymptotic dominance theorem would clarify when pseudo-inverse-based precision estimation is provably preferable in high dimensions.

## Known Partial Results

Bodnar--Parolya (arXiv:2403.15792v2) derive high-dimensional asymptotics for weighted trace moments (using partial exponential Bell polynomials) and construct data-driven shrinkage estimators with asymptotic quadratic-loss optimality for their specified targets. These results support strong practical performance, but they do not by themselves establish the synthesized full uniform risk-dominance claim over an arbitrary benchmark class $\mathcal{B}$ .

## References

[1]

 [Reviving pseudo-inverses: Asymptotic properties of large dimensional Moore-Penrose and Ridge-type inverses with applications](https://arxiv.org/abs/2403.15792v2) 

Taras Bodnar, Nestor Parolya (2024)

arXiv preprint

📍 arXiv:2403.15792v2 (version-specific source for the technical asymptotic and shrinkage results).

Primary technical source; citation is explicitly version-specific (v2).

 [Link ↗](https://arxiv.org/abs/2403.15792v2) [arXiv ↗](https://arxiv.org/abs/2403.15792v2) [2]

 [Seminarier i matematisk statistik (Resurrecting pseudo-inverses: Asymptotic properties of large dimensional Moore-Penrose and Ridge-type inverses with applications)](https://liu.se/artikel/seminarier-i-matematisk-statistik) 

Taras Bodnar (2023)

Linkoping University seminar webpage

📍 Seminar abstract text under the listed talk title (sentence containing 'it seems that its proper transformation (shrinkage) performs similarly to or even outperforms the existing benchmarks ...').

Verifiable location of the 'it seems ... outperforms the existing benchmarks' wording used for significance context.

 [Link ↗](https://liu.se/artikel/seminarier-i-matematisk-statistik)

## Notes / Progress

_Work log goes here._
