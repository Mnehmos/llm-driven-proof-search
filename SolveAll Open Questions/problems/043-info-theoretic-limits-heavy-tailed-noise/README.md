# Information-theoretic limits under heavy-tailed (non-sub-Gaussian) noise

**Status:** Unsolved  
**Source:** Sourced from the work of Akshay Prasadan, Matey Neykov

## Categories

- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #43 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $d\ge 1$ and $N\ge 1$ , and fix contamination parameters $\kappa\in(0,1/2]$ and $\epsilon\in[0,1/2-\kappa]$ (equivalently, one may consider the boundary regime $\epsilon\le 1/2$ ). Let $p>2$ , $\nu>0$ , and let $K\subseteq\mathbb R^d$ be a known constraint set for the unknown mean vector $\mu$ (in the motivating framework, $K$ is star-shaped with respect to $0$ ). Define

$
\mathcal P_{p,\nu}=\left\{P\ \text{on }\mathbb R^d:\ \mathbb E_P[\xi]=0,\ \mathbb E_P\|\xi\|_2^p\le \nu^p\right\}.
$

For $(\mu,P)\in K\times\mathcal P_{p,\nu}$ , let $X_i^\star=\mu+\xi_i$ with $\xi_1,\dots,\xi_N\stackrel{i.i.d.}{\sim}P$ . Under Huber contamination, an adversary replaces at most $\lfloor\epsilon N\rfloor$ observations arbitrarily, yielding $X_1,\dots,X_N$ . For measurable estimators $\hat\mu:(\mathbb R^d)^N\to\mathbb R^d$ (or $K$ ), consider

$
\mathfrak R^\star(N,\epsilon,p,\nu;K)
=
\inf_{\hat\mu}
\sup_{\mu\in K}
\sup_{P\in\mathcal P_{p,\nu}}
\sup_{|\mathcal O|\le \lfloor\epsilon N\rfloor}
\mathbb E\!\left[\|\hat\mu(X_1,\dots,X_N)-\mu\|_2^2\right].
$

### Unsolved Problem

Determine sharp minimax upper/lower bounds (rates, and if possible constants) for this heavy-tailed setting, including dependence on $N,\epsilon,p,\nu$ and on geometry of $K$ (e.g., heavy-tail analogues of local complexity).

## Significance & Implications

Heavy-tailed robustness is explicitly posed as a future direction in the source paper. Clarifying minimax limits here would test how much of the star-shaped, geometry-driven theory persists beyond sub-Gaussian tails and which additional complexity terms are unavoidable.

## Known Partial Results

The paper establishes minimax characterizations for several sub-Gaussian regimes (including unbounded star-shaped sets) but does not provide a full heavy-tailed minimax characterization. Based on the source framing, this heavy-tailed formulation should be treated as a proposed extension and remains open.

## References

[1]

 [Information Theoretic Limits of Robust Sub-Gaussian Mean Estimation Under Star-Shaped Constraints](https://arxiv.org/abs/2412.03832v2) 

Akshay Prasadan, Matey Neykov (2025)

Annals of Statistics (accepted; final volume/issue/pages/DOI pending)

📍 Section 6 (Discussion and Future Work), first paragraph: "Another avenue for future research is to understand the case when the noise can be heavy tailed."

Primary source paper; Section 6 frames heavy-tailed noise as future work rather than a completed characterization.

 [Link ↗](https://arxiv.org/abs/2412.03832v2) [arXiv ↗](https://arxiv.org/abs/2412.03832v2)

## Notes / Progress

_Work log goes here._
