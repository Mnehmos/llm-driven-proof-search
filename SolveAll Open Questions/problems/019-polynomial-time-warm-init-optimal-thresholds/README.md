# Polynomial-time warm initialization at statistically optimal thresholds

**Status:** Unsolved  
**Importance:** Notable
**Source:** Sourced from the work of Wanteng Ma, Dong Xia

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #19 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $m\ge 2$ and dimensions $d_1,\dots,d_m\in\mathbb N$ . Let $T^\star\in\mathbb R^{d_1\times\cdots\times d_m}$ be an unknown low-multilinear-rank tensor with mode- $k$ rank $r_k$ , and define

$
d:=\sum_{k=1}^m d_k,\qquad d^\star:=\max_{k\in[m]}\prod_{j\ne k} d_j.
$

Observe i.i.d. samples

$
(\omega_i,Y_i),\qquad \omega_i\sim\mathrm{Unif}([d_1]\times\cdots\times[d_m]),\qquad Y_i=T^\star_{\omega_i}+\xi_i,
$

where $\xi_i$ are mean-zero noise with scale $\sigma$ (e.g., Gaussian/sub-Gaussian). For mode- $k$ matricization $\mathcal M_k(T^\star)$ , define

$
\lambda_{\min}:=\min_{k\in[m]}\sigma_{r_k}\!\big(\mathcal M_k(T^\star)\big).
$

A statistically optimal scaling regime considered in [Ma & Xia (2024)](#references) (up to absolute constants and polylogarithmic factors) is

$
n\gtrsim d,\qquad \frac{\lambda_{\min}}{\sigma}\gtrsim\sqrt{\frac{d^\star d}{n}}.
$

Ma et al. (2024) require a warm-initialization condition ( [Ma & Xia (2024)](#references) ). Specifically, for an initializer $\widetilde T$ built on an independent data split, there exists an absolute constant $C_1>0$ such that

$
\|\widetilde T-T^\star\|_{\ell_\infty}\le C_1\,\sigma\sqrt{\frac{d\log d}{n}}
$

with high probability (the paper states probability at least $1-d^{-3m}$ in the corresponding assumption).

### Unsolved Problem

Under the statistical scaling above, does there exist a randomized algorithm running in polynomial time in problem size that outputs, with high probability, an initializer satisfying this warm-start accuracy guarantee?

## Significance & Implications

This is a central bottleneck for achieving statistically optimal inference without oracle/computationally intractable initialization. A positive result would shrink a key statistical-to-computational gap; a negative result would formalize a computational barrier in tensor inference. See [Ma & Xia (2024)](#references) .

## Known Partial Results

The paper proves that if a sufficiently accurate initializer is available, debiasing plus one-step power iteration yields asymptotic normality and optimal variance. It also gives a computationally intractable constrained least-squares initializer achieving warm start under minimal sample size (with data splitting), and polynomial-time guarantees only under stronger computational conditions.

## References

[1]

 [Statistical Inference in Tensor Completion: Optimal Uncertainty Quantification and Statistical-to-Computational Gaps](https://imstat.org/journals-and-publications/annals-of-statistics/annals-of-statistics-future-papers/) 

Wanteng Ma, Dong Xia (2024)

Annals of Statistics (Future Papers / in press record)

📍 Section 7.1, discussion linking Condition (30) to initialization of (9) (arXiv v2 updated Nov 1, 2024).

Definitive in-press listing in Annals of Statistics Future Papers; preprint version is arXiv:2410.11225v2.

 [Link ↗](https://imstat.org/journals-and-publications/annals-of-statistics/annals-of-statistics-future-papers/) [arXiv ↗](https://arxiv.org/abs/2410.11225v2)

## Notes / Progress

_Work log goes here._
