# Sharp minimax rate for central-space estimation in the low-signal SIR regime

**Status:** Partially Resolved  
**Source:** Sourced from the work of Dongming Huang, Songtao Tian, Qian Lin

## Categories

- Mathematical Statistics
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #28 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $n,p,d\in\mathbb N$ with $1\le d\le p$ . We observe i.i.d. data $(X_i,Y_i)_{i=1}^n$ from

$
Y=f(PX)+\varepsilon,\qquad X\sim N(0,I_p),
$

where $P\in\mathbb R^{p\times p}$ is an unknown rank- $d$ orthogonal projector, $f(x)$ depends on $x$ only through $Px$ , and $\varepsilon\perp X$ . Let

$
M:=\operatorname{Cov}(\mathbb E[X\mid Y]),\qquad \lambda_d(M)\asymp \lambda.
$

Under the model class and regularity assumptions used in Huang-Tian-Lin (Theorems 5-6; including their low-gSNR setup and technical conditions required for the SIR upper bound), the minimax risk for estimating the central subspace $\mathcal S(P)$ under projection-Frobenius loss satisfies matching lower and upper bounds of order

$
\frac{dp}{n\lambda}
$

(in particular in the low-signal regime discussed there, including $\lambda\le d^{-8.1}$ ).

This setup follows [Huang et al. (2023)](#references) .

### Unsolved Problem

Thus, for that stated model class, the sharp minimax-rate question is already resolved in the paper. A broader claim beyond those assumptions is currently uncertain unless one re-proves comparable upper and lower bounds for the enlarged class.

## Significance & Implications

The paper's Theorems 5-6 already give a matched minimax characterization (up to universal constants) for the paper's own low-gSNR model class and assumptions, so the previously stated "open minimax-rate" framing is stale for that scope. Remaining interest is in robustness: whether the same $dp/(n\lambda)$ rate persists under weaker or different assumptions.

## Known Partial Results

For the model class and regularity assumptions explicitly treated in the paper, Theorems 5-6 provide matching minimax lower and upper bounds of order $dp/(n\lambda_d)$ (equivalently $dp/(n\lambda)$ up to constants when $\lambda_d\asymp\lambda$ ). What remains open is extension to broader classes not covered by those assumptions.

## References

[1]

 [On the Structural Dimension of Sliced Inverse Regression](https://arxiv.org/abs/2305.04340) 

Dongming Huang, Songtao Tian, Qian Lin (2023)

Annals of Statistics (to appear)

📍 Section 3 ("Small gSNR with a large structural dimension"), opening paragraph before Section 3.1 (citing Lin et al. (2021)'s conjecture), together with Theorems 5-6 and discussion claims in the same paper showing matching minimax upper/lower rates for the paper's stated model class.

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2305.04340) [arXiv ↗](https://arxiv.org/abs/2305.04340)

## Notes / Progress

_Work log goes here._
