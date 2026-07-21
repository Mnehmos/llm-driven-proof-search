# Full minimax characterization for tensor normal factor estimation beyond the largest factor

**Status:** Unsolved  
**Source:** Sourced from the work of Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter

## Categories

- Mathematical Statistics
- Information Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #31 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $K\ge 3$ and dimensions $d_1,\dots,d_K\in\mathbb{N}$ . For each sample, observe a random tensor $X\in\mathbb{R}^{d_1\times\cdots\times d_K}$ , and write $\operatorname{vec}(X)\in\mathbb{R}^{D}$ with $D=\prod_{j=1}^K d_j$ . Assume

$
\operatorname{vec}(X_i)\stackrel{\text{i.i.d.}}{\sim}\mathcal{N}(0,\Sigma),\qquad \Sigma=\Sigma_1\otimes\cdots\otimes\Sigma_K,\qquad \Sigma_k\in\mathbb{S}_{++}^{d_k},
$

for $i=1,\dots,n$ , where $\mathbb{S}_{++}^{d}$ is the cone of $d\times d$ real symmetric positive-definite matrices and $\otimes$ is the Kronecker product.

Because the factorization is not unique under rescalings $\Sigma_k\mapsto c_k\Sigma_k$ with $c_k>0$ and $\prod_{k=1}^K c_k=1$ , define identifiable factor parameters by shape normalization

$
\bar\Sigma_k:=\Sigma_k/(\det\Sigma_k)^{1/d_k}\in\mathbb{S}_{++}^{d_k},\qquad \det(\bar\Sigma_k)=1.
$

For estimation error, use the affine-invariant Fisher-Rao distance

$
d_{\mathrm{FR}}(A,B):=\|\log(A^{-1/2}BA^{-1/2})\|_F,
$

and optionally the Thompson/log-spectral form

$
d_{\mathrm{Th}}(A,B):=\|\log(A^{-1/2}BA^{-1/2})\|_{\mathrm{op}}.
$

These two metrics are comparable but not dimension-free equivalent: for $d\times d$ SPD matrices,

$
d_{\mathrm{Th}}(A,B)\le d_{\mathrm{FR}}(A,B)\le \sqrt d\,d_{\mathrm{Th}}(A,B).
$

Define minimax risks

$
R_k^\star(n,\mathbf d):=\inf_{\hat S_k}\sup_{(\Sigma_1,\dots,\Sigma_K)}\mathbb{E}\big[d_{\mathrm{FR}}^2(\hat S_k,\bar\Sigma_k)\big],
\qquad
R_{\mathrm{full}}^\star(n,\mathbf d):=\inf_{\hat\Sigma}\sup_{(\Sigma_1,\dots,\Sigma_K)}\mathbb{E}\big[d_{\mathrm{FR}}^2(\hat\Sigma,\Sigma)\big],
$

where infima are over all measurable estimators based on $X_1,\dots,X_n$ , and the supremum is over all unrestricted positive-definite factors (no bounded condition number, sparsity, or structural constraints unless explicitly imposed).

### Unsolved Problem

Determine the exact nonasymptotic minimax rates (up to universal constant factors) for $R_k^\star(n,\mathbf d)$ for every mode $k\in\{1,\dots,K\}$ and for $R_{\mathrm{full}}^\star(n,\mathbf d)$ , uniformly over all sample-size/dimension regimes $(n,d_1,\dots,d_K)$ , including regimes where $n$ is too small to guarantee constant Frobenius error. Equivalently, provide matching upper and lower bounds that fully characterize the statistical difficulty of estimating each Kronecker factor (not only the largest one) and the full covariance in the tensor normal model.

## Significance & Implications

The tensor case is substantially harder and central in multiway data analysis. A complete minimax theory would specify the true statistical limits for every mode and clarify whether current guarantees are sharp only in restricted regimes or uniformly across regimes. The primary source is the 2021 arXiv preprint (revised in 2025), which is listed as accepted in Annals of Statistics and to appear.

## Known Partial Results

The paper proves nearly optimal guarantees for tensor normal MLE and establishes constant-factor minimax optimality for the largest factor and overall covariance in regimes with enough samples for constant Frobenius error. It explicitly leaves full minimax characterization for all tensor factors as an open direction in Section 8. The source paper leaves this direction open.

## References

[1]

 [Near Optimal Sample Complexity for Matrix and Tensor Normal Models via Geodesic Convexity](https://arxiv.org/abs/2110.07583v3) 

Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter (2021)

arXiv preprint (2021); accepted in Annals of Statistics (to appear)

📍 arXiv:2110.07583v3, Section 8 "Conclusion and open problems," paragraph discussing tensor-normal minimax guarantees beyond the largest factor (the paragraph beginning with the tensor-normal limitation statement in that section).

Primary source containing the open-problem discussion; arXiv metadata (v3, 2025-10-23) states "accepted in Annals of Statistics."

 [Link ↗](https://arxiv.org/abs/2110.07583v3) [arXiv ↗](https://arxiv.org/abs/2110.07583v3)

## Notes / Progress

_Work log goes here._
