# Lower-bound the spanning-tree polynomial to sharpen Gaussian chi^2 bounds

**Status:** Unsolved  
**Source:** Sourced from the work of Yanjun Han, Jonathan Niles-Weed

## Categories

- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #78 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $n \ge 2$ and $d \ge 1$ , a positive-definite covariance matrix $\Sigma \in \mathbb R^{d \times d}$ , and mean vectors $\mu_1,\dots,\mu_n \in \mathbb R^d$ . For each $i \in [n]:=\{1,\dots,n\}$ , let $P_i=\mathcal N(\mu_i,\Sigma)$ with density $p_i$ on $\mathbb R^d$ , and define the average measure $\bar P=\frac1n\sum_{i=1}^n P_i$ with density $\bar p=\frac1n\sum_{i=1}^n p_i$ .

Define two distributions on $(\mathbb R^d)^n$ . The permutation mixture $\mathbb P_n$ is

$
\mathbb P_n=\frac1{n!}\sum_{\pi\in S_n}\bigotimes_{k=1}^n P_{\pi(k)},
$

equivalently with density $p_{\mathrm{perm}}(x_1,\dots,x_n)=\frac1{n!}\sum_{\pi\in S_n}\prod_{k=1}^n p_{\pi(k)}(x_k)$ . Its i.i.d. counterpart is

$
\mathbb Q_n=\bar P^{\otimes n},
$

with density $q(x_1,\dots,x_n)=\prod_{k=1}^n \bar p(x_k)$ .

Let $\chi^2(\mathbb P_n\|\mathbb Q_n):=\int\!\left(\frac{d\mathbb P_n}{d\mathbb Q_n}-1\right)^2d\mathbb Q_n$ . Define $A\in\mathbb R^{n\times n}$ by

$
A_{ij}:=\frac1n\int_{\mathbb R^d}\frac{p_i(x)p_j(x)}{\bar p(x)}\,dx,\qquad i,j\in[n].
$

For this construction, $A$ is symmetric, positive semidefinite, and doubly stochastic. Let $\mathcal T_n$ be the set of spanning trees on vertex set $[n]$ , and define the weighted spanning-tree polynomial

$
\tau(A):=\sum_{T\in\mathcal T_n}\ \prod_{(u,v)\in E(T)} A_{uv}.
$

### Unsolved Problem

Prove a nontrivial Gaussian-structure-dependent lower bound on $\tau(A)$ (for matrices $A$ arising from the above Gaussian family) that could improve the currently available eigenvalue-only upper bound on $\chi^2(\mathbb P_n\|\mathbb Q_n)$ ,

$
\chi^2(\mathbb P_n\|\mathbb Q_n)+1\le \prod_{k=2}^n(1-\lambda_k(A))^{-1},
$

where $1=\lambda_1(A)\ge \lambda_2(A)\ge\cdots\ge\lambda_n(A)$ are the eigenvalues of $A$ . In particular, the goal is to exploit constraints specific to Gaussian-generated $A$ beyond trace/spectral-gap information.

## Significance & Implications

This is a proposed route in the paper for potentially sharpening approximate-independence guarantees in Gaussian permutation-mixture settings. If stronger $\chi^2$ control is obtained, it would typically imply tighter downstream total-variation/testing/decision bounds via standard inequalities; these downstream improvements are inferential unless separately proved. See [Han & Niles-Weed (2024)](#references) for details.

## Known Partial Results

The paper proves permanent-based upper bounds for $\chi^2(\mathbb P_n\|\mathbb Q_n)$ , including a bound of the form $\chi^2(\mathbb P_n\|\mathbb Q_n)+1\le \prod_{i=2}^n(1-\lambda_i)^{-1}$ (with $\lambda_i$ eigenvalues of $A$ ), and identifies this quantity with a spanning-tree polynomial expression; the authors describe exploiting extra structure of $A$ as an open direction that could improve Gaussian bounds. This direction appears open in the cited source.

## References

[1]

 [Approximate independence of permutation mixtures](https://arxiv.org/abs/2408.09341v3) 

Yanjun Han, Jonathan Niles-Weed (2024)

Annals of Statistics (to appear)

📍 Section 6.1 (Discussion: Tightness of upper bounds), paragraph immediately after Lemma 6.2 ("for specific $P$, further properties of the matrix $A$...") on p. 26 (arXiv v3; Section 5.1 in earlier numbering)

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2408.09341v3) [arXiv ↗](https://arxiv.org/abs/2408.09341v3)

## Notes / Progress

_Work log goes here._
