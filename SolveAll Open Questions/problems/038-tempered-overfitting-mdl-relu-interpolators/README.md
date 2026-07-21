# Rigorous tempered-overfitting guarantees for MDL ReLU interpolators under label noise

**Status:** Unsolved  
**Source:** Sourced from the work of Sourav Chatterjee, Timothy Sudijono

## Categories

- Learning Theory
- Mathematical Statistics
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #38 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix an input space $\mathcal X\subseteq \mathbb R^d$ and let $(X_i,Y_i)_{i=1}^n$ be i.i.d. samples from a distribution $P$ on $\mathcal X\times\{0,1\}$ . Assume there exists a binary target function $f^\star:\mathcal X\to\{0,1\}$ such that

$
Y = f^\star(X)\oplus \xi,
$

where $\oplus$ is XOR, and conditionally on $X=x$ , $\xi\sim \mathrm{Bernoulli}(\eta(x))$ with measurable $\eta:\mathcal X\to[0,\bar\eta]$ for some fixed $\bar\eta<\tfrac12$ . Then $\mathbb P(Y\neq f^\star(X)\mid X=x)=\eta(x)$ and

$
R^\star=\inf_{g:\mathcal X\to\{0,1\}} \mathbb P(g(X)\neq Y)=\mathbb E[\eta(X)].
$

Assume $f^\star$ has finite description complexity in a fixed prefix-free language $\mathcal L$ :

$
K_{\mathcal L}(f^\star):=\min\{|p|: p\in\mathcal L,\ p\text{ outputs }f^\star\}<\infty.
$

Let $\mathcal F_{\mathrm{ReLU}}$ be binary classifiers representable by finite feedforward ReLU networks (real-valued output thresholded at $1/2$ ), each with prefix-free code length $\mathrm{DL}(f)\in\mathbb N$ . Define $\hat f_n$ via penalized ERM with approximate minimization: for given $\lambda_n>0$ and tolerance $\alpha_n\ge 0$ , choose measurable $\hat f_n\in\mathcal F_{\mathrm{ReLU}}$ such that

$
\hat R_n(\hat f_n)+\lambda_n\frac{\mathrm{DL}(\hat f_n)}{n}
\le
\inf_{f\in\mathcal F_{\mathrm{ReLU}}}\left\{\hat R_n(f)+\lambda_n\frac{\mathrm{DL}(f)}{n}\right\}+\alpha_n,
\quad
\hat R_n(f)=\frac1n\sum_{i=1}^n\mathbf 1\{f(X_i)\neq Y_i\}.
$

This setup follows [Chatterjee & Sudijono (2024)](#references) .

### Unsolved Problem

Under explicit assumptions linking program complexity, ReLU approximation/realizability, coding choices, and the sequences $(\lambda_n,\alpha_n)$ , prove a nonasymptotic high-probability excess-risk bound

$
\mathbb P\!\left(R(\hat f_n)-R^\star\le \varepsilon(n,\delta,K_{\mathcal L}(f^\star),\bar\eta,\text{model/coding parameters})\right)\ge 1-\delta,
$

with explicit $\varepsilon(\cdot)$ and $\varepsilon\to0$ as $n\to\infty$ (for fixed $\delta$ and fixed complexity/noise parameters). Motivation: this would rigorously quantify whether and when MDL regularization tempers overfitting in noisy-label ReLU interpolation, extending the source paper's noiseless guarantees.

## Significance & Implications

The abstract of [Chatterjee & Sudijono (2024)](#references) proves strong generalization in noiseless low-complexity settings and only indicates noisy extensions heuristically. A rigorous theorem in the noisy regime would formalize whether MDL-style selection avoids catastrophic memorization and quantify when overfitting is tempered under label noise.

## Known Partial Results

Theorem 5.1 proves high-probability generalization guarantees in the noiseless low-complexity setting, and Section 7 discusses noisy-label extensions only as future work; a full proved noisy-label theorem is still open.

## References

[1]

 [Neural Networks Generalize on Low Complexity Data](https://arxiv.org/abs/2409.12446v5) 

Sourav Chatterjee, Timothy Sudijono (2024)

arXiv preprint

📍 Theorem 5.1 (main noiseless high-probability generalization guarantee) and Section 7 (Discussion), paragraph after Theorem 5.1 noting noisy-observation extensions as future work rather than a proved noisy-label theorem.

Primary source is the 2024 arXiv preprint; Annals of Statistics acceptance/to-appear status is separate (reported in 2025) and not itself a noisy-regime theorem.

 [Link ↗](https://arxiv.org/abs/2409.12446v5) [arXiv ↗](https://arxiv.org/abs/2409.12446v5)

## Notes / Progress

_Work log goes here._
