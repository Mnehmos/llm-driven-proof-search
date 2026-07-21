# Optimal guarantees in the low-sample tensor regime (below constant-Frobenius threshold)

**Status:** Unsolved  
**Source:** Sourced from the work of Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter

## Categories

- Mathematical Statistics
- Information Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #32 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $K\ge 3$ , dimensions $d_1,\dots,d_K\ge 2$ , and $D=\prod_{k=1}^K d_k$ . Observe i.i.d. tensors $X_1,\dots,X_n\in\mathbb R^{d_1\times\cdots\times d_K}$ from a tensor-normal model

$
\operatorname{vec}(X_i)\sim \mathcal N\big(0,\Sigma_K\otimes\cdots\otimes\Sigma_1\big),\qquad \Sigma_k\in\mathbb S_{++}^{d_k}.
$

The Kronecker factors are only identifiable up to reciprocal rescaling, so use shape-normalized factors

$
\bar\Sigma_k:=\Sigma_k/(\det\Sigma_k)^{1/d_k},\qquad \det(\bar\Sigma_k)=1.
$

Define affine-invariant error via the Fisher--Rao metric

$
d_{\mathrm{FR}}(A,B)=\|\log(A^{-1/2}BA^{-1/2})\|_F,
$

and mode-wise minimax risks

$
R_k^\star(n,\mathbf d):=\inf_{\hat S_k}\sup_{(\Sigma_1,\dots,\Sigma_K)}\mathbb E\big[d_{\mathrm{FR}}^2(\hat S_k,\bar\Sigma_k)\big],\qquad k=1,\dots,K,
$

plus a full-covariance risk defined analogously for $\Sigma=\Sigma_K\otimes\cdots\otimes\Sigma_1$ .

This setup follows [Oliveira et al. (2021)](#references) .

Call a sample size $n$ a constant-error regime if a universal constant $C_0$ exists such that the corresponding minimax risk is at most $C_0$ ; otherwise $n$ is below the constant-error threshold.

### Unsolved Problem

Obtain sharp nonasymptotic minimax characterizations in the low-sample regime below the constant-error threshold, including matching upper and lower bounds for tensor-normal covariance/factor estimation without imposing extra structural assumptions (bounded condition number, sparsity, incoherence, or similar restrictions).

## Significance & Implications

The paper explicitly separates tensor guarantees above a constant-Frobenius threshold from what is known below it. Closing this gap would pin down the true minimax phase transition for low-sample tensor-normal estimation and determine whether current upper/lower bounds are sharp in the sub-threshold regime.

## Known Partial Results

The source paper proves near-optimal tensor-normal guarantees in regimes where constant Frobenius recovery is information-theoretically attainable and states an explicit open question about weakening the tensor sample-threshold requirement (Section 6). The source framing treats this direction as open.

## References

[1]

 [Near Optimal Sample Complexity for Matrix and Tensor Normal Models via Geodesic Convexity](https://arxiv.org/abs/2110.07583v3) 

Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter (2021)

Annals of Statistics (accepted; to appear)

📍 arXiv v3 HTML anchors: Definition 1.1 (Eqs. (1.1)-(1.2)); Definition 1.9 (Eqs. (1.3)-(1.4)); Theorem 1.10 hypothesis Eq. (1.5); Section 6 "Conclusion and open problems" (lines 769-772), including: "whether the sample threshold requirement for Theorem 1.10 can be weakened" and the constant-Frobenius-error regime qualifier.

Primary source; originally posted on arXiv in 2021, with v3 revision dated 2025-10-23; final journal bibliographic metadata not yet specified on arXiv.

 [Link ↗](https://arxiv.org/abs/2110.07583v3) [arXiv ↗](https://arxiv.org/abs/2110.07583v3) [2]

 [Broader follow-up literature check for tensor-normal low-sample minimax closure (accessed 2026-02-17)](https://arxiv.org/search/?query=tensor+normal+minimax+sample+complexity+Kronecker+covariance&searchtype=all&abstracts=show&order=-announced_date_first&size=50) 

arXiv search index

📍 Search results inspected on 2026-02-17 for post-2021 follow-up works on tensor-normal/Kronecker covariance minimax sample complexity.

Post-2021 sweep used to check for explicit closure claims; no clear paper was identified that states a full matching minimax characterization for the sub-threshold tensor-normal regime.

 [Link ↗](https://arxiv.org/search/?query=tensor+normal+minimax+sample+complexity+Kronecker+covariance&searchtype=all&abstracts=show&order=-announced_date_first&size=50)

## Notes / Progress

_Work log goes here._
