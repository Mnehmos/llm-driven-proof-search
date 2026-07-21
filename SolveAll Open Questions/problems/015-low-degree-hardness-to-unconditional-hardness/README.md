# From low-degree hardness to unconditional polynomial-time hardness

**Status:** Unsolved  
**Importance:** Notable
**Source:** Sourced from the work of Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li

## Categories

- Probability Theory
- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #15 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

For each $n$ , let $[n]=\{1,\dots,n\}$ and $U_n=\{\{i,j\}:1\le i. Fix constants $k\ge 2$ , $\lambda>0$ , $\epsilon\in(0,1)$ , and subsampling rate $s\in(0,1)$ , with $k,\lambda=O(1)$ as $n\to\infty$ .

This setup follows [Chen et al. (2025)](#references) .

The formal correlated-SBM model and detection setup below follow the source paper. First sample latent labels $\sigma^\*\in[k]^n$ uniformly (equivalently, i.i.d. uniform on $[k]$ ). Conditional on $\sigma^\*$ , sample independent edges $(G_{ij})_{\{i,j\}\in U_n}$ with

$
\mathbb P(G_{ij}=1\mid \sigma^\*)=
\begin{cases}
\frac{(1+(k-1)\epsilon)\lambda}{n}, & \sigma^\*(i)=\sigma^\*(j),\\[1mm]
\frac{(1-\epsilon)\lambda}{n}, & \sigma^\*(i)\ne \sigma^\*(j).
\end{cases}
$

Then sample independent Bernoulli $(s)$ variables $(J_{ij})_{\{i,j\}\in U_n}$ and $(K_{ij})_{\{i,j\}\in U_n}$ , and an independent uniform permutation $\pi^\*\in S_n$ . The observed pair $(A,B)$ is

$
A_{ij}=G_{ij}J_{ij},\qquad
B_{ij}=G_{\pi^{\* -1}(i),\,\pi^{\* -1}(j)}K_{ij}\quad (\{i,j\}\in U_n).
$

Let $P_n$ be the law of $(A,B)$ (after marginalizing $\sigma^\*,\pi^\*,G,J,K$ ). Let $Q_n$ be the null law where $A$ and $B$ are independent Erd\H{o}s-R'enyi graphs $G(n,\lambda s/n)$ .

The detection problem is to construct tests $\varphi_n:\{0,1\}^{U_n}\times\{0,1\}^{U_n}\to\{0,1\}$ ; success with vanishing error means

$
P_n(\varphi_n=0)+Q_n(\varphi_n=1)\to 0.
$

A randomized polynomial-time test means runtime $n^{O(1)}$ (including internal randomness).

A partial matching estimator is a randomized polynomial-time map $\widehat\pi_n(A,B)\in S_n$ . One concrete notion of nontrivial partial recovery is: there exists $\eta>0$ such that

$
\liminf_{n\to\infty} P_n\!\left(\frac1n\big|\{i\in[n]:\widehat\pi_n(i)=\pi^\*(i)\}\big|\ge \eta\right)>0.
$

Let $\alpha\approx 0.338$ denote the Otter constant in this paper's notation, i.e., the inverse of the classical rooted-tree growth constant $\rho\approx 2.955765\ldots$ (so $\alpha=1/\rho$ ), equivalently $t_m=\Theta(\alpha^{-m}m^{-3/2})$ for unlabeled rooted trees.

The source establishes a sharp transition for low-degree methods but leaves unconditional polynomial-time hardness open.

### Unsolved Problem

Prove or refute unconditionally (that is, beyond the low-degree-polynomial framework) that whenever

$
s<\min\!\left\{\sqrt{\alpha},\frac{1}{\lambda\epsilon^2}\right\},
$

no randomized polynomial-time algorithm can distinguish $P_n$ from $Q_n$ with vanishing error; and similarly no randomized polynomial-time algorithm can achieve nontrivial partial recovery of the latent matching $\pi^\*$ .

## Significance & Implications

Chen et al. (arXiv:2409.00966v2) proves a sharp transition for low-degree polynomial tests/computations, not an unconditional polynomial-time lower bound for all algorithms. Establishing or refuting the corresponding unconditional polynomial-time hardness would close this complexity-theoretic gap.

## Known Partial Results

The paper establishes the threshold $s=\min\{\sqrt{\alpha},1/(\lambda\epsilon^2)\}$ for low-degree polynomial tests (and corresponding low-degree hardness evidence via reductions for related tasks). It does not prove unconditional polynomial-time impossibility for all randomized polynomial-time algorithms below that threshold.

## References

[1]

 [A Computational Transition for Detecting Correlated Stochastic Block Models by Low-Degree Polynomials](https://arxiv.org/abs/2409.00966v2) 

Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li (2024)

Annals of Statistics (to appear)

📍 Section 1: Definition 1.1 (model), Problem 1.2 (detection problem), Theorem 1.3 (low-degree threshold), and the adjacent item-(2) discussion on the lack of complexity-theoretic tools/open unconditional-hardness gap.

Primary source; first preprint posted in 2024, with cited revised version v2 dated 2025-07-22.

 [Link ↗](https://arxiv.org/abs/2409.00966v2) [arXiv ↗](https://arxiv.org/abs/2409.00966v2)

## Notes / Progress

_Work log goes here._
