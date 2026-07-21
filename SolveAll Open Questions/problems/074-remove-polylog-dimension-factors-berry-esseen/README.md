# Remove polylogarithmic dimension factors in high-dimensional Berry-Esseen bounds for m-dependent sums

**Status:** Unsolved  
**Source:** Sourced from the work of Heejong Bong, Arun Kumar Kuchibhotla, Alessandro Rinaldo

## Categories

- Mathematical Statistics
- Probability Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #74 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $q>2$ , $m,n,d\in\mathbb N$ , and let $X_1,\dots,X_n$ be random vectors in $\mathbb R^d$ . Assume:

- 

 $X_i$ are mean-zero: $\mathbb E[X_i]=0$ for all $i$ .

- 

 $X_1,\dots,X_n$ are $m$ -dependent, meaning that for every $k\in\{1,\dots,n\}$ , the sigma-fields $\sigma(X_i:i\le k)$ and $\sigma(X_j:j\ge k+m+1)$ are independent.

- 

A uniform $q$ -moment bound holds: for some finite constant $M_q$ , $\max_{1\le i\le n}\max_{1\le j\le d}\mathbb E|X_{ij}|^q\le M_q^q$ .

- 

For

$
S_n:=\frac{1}{\sqrt n}\sum_{i=1}^n X_i,\qquad \Sigma_n:=\operatorname{Cov}(S_n),
$

 $\Sigma_n$ is nondegenerate in coordinates, e.g. $\min_{1\le j\le d}(\Sigma_n)_{jj}\ge \underline{\sigma}^2$ for some $\underline{\sigma}>0$ .

Let $Z\sim N(0,\Sigma_n)$ , and let $\mathcal H_d$ be the class of axis-aligned hyper-rectangles

$
\mathcal H_d:=\left\{\prod_{j=1}^d (a_j,b_j]:\ -\infty\le a_j\le b_j\le \infty\right\}.
$

Define the rectangle Kolmogorov distance

$
\Delta_{n,d}:=\sup_{A\in\mathcal H_d}\left|\mathbb P(S_n\in A)-\mathbb P(Z\in A)\right|.
$

### Unsolved Problem

Under the assumptions above, does there exist a constant $C$ depending only on fixed model parameters (for example only on $q$ , $M_q$ , and $\underline{\sigma}$ ), but independent of $d,n,m$ , such that for all $d,n,m$ and all such $m$ -dependent arrays,

$
\Delta_{n,d}\le C\,\frac{m^{(q-1)/(q-2)}}{\sqrt n},
$

that is, with no additional multiplicative $\operatorname{polylog}(d)$ factor?

## Significance & Implications

Bong, Kuchibhotla, and Rinaldo’s arXiv record is currently `2306.14299v3` (latest arXiv version; revised 2025-08-29), and the work is listed as accepted at Annals of Statistics (2025). Their bounds are sharp in $n$ and $m$ up to logarithmic factors in $d$ ; removing (or proving unavoidable) these dimension-log factors would clarify optimal high-dimensional Gaussian approximation rates under $m$ -dependence.

## Known Partial Results

This paper proves sharp high-dimensional bounds with only polylogarithmic dependence on $d$ and optimal $m$ / $n$ scaling $m^{(q-1)/(q-2)}/\sqrt n$ . In univariate settings, matching optimal rates are known (up to logs as stated in the abstract).

## References

[1]

 [Dual Induction CLT for High-dimensional m-dependent Data](https://arxiv.org/abs/2306.14299v3) 

Heejong Bong, Arun Kumar Kuchibhotla, Alessandro Rinaldo (2025)

Annals of Statistics (accepted, 2025)

📍 Section 3 (Discussion), item 2, p. 14 (arXiv v3 manuscript).

Source paper where this problem appears; latest arXiv version is v3 (revised 2025-08-29).

 [Link ↗](https://arxiv.org/abs/2306.14299v3) [arXiv ↗](https://arxiv.org/abs/2306.14299v3)

## Notes / Progress

_Work log goes here._
