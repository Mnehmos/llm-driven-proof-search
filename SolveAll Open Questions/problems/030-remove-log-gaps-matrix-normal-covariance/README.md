# Remove logarithmic gaps in minimax sample complexity for matrix normal covariance estimation

**Status:** Unsolved  
**Source:** Sourced from the work of Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter

## Categories

- Mathematical Statistics
- Information Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #30 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d_1,d_2\ge 2$ and let $\mathbb{S}_{++}^{d}$ denote the set of $d\times d$ real symmetric positive-definite matrices. Assume i.i.d. matrix-normal observations $X_1,\dots,X_n\in\mathbb{R}^{d_1\times d_2}$ with mean zero and

$
\mathrm{vec}(X_t)\sim\mathcal{N}(0,\Sigma_2\otimes \Sigma_1),
$

for unknown $\Sigma_1\in\mathbb{S}_{++}^{d_1}$ and $\Sigma_2\in\mathbb{S}_{++}^{d_2}$ . This implies

$
\mathrm{Cov}\!\left((X_t)_{ab},(X_t)_{cd}\right)=(\Sigma_1)_{ac}(\Sigma_2)_{bd},
\qquad 1\le a,c\le d_1,\;1\le b,d\le d_2.
$

The parameterization is non-identifiable up to reciprocal scaling: $(\Sigma_1,\Sigma_2)$ and $(c\Sigma_1,c^{-1}\Sigma_2)$ , $c>0$ , induce the same distribution.

For $A,B\in\mathbb{S}_{++}^{d}$ , define the Fisher--Rao distance

$
d_{\mathrm{FR}}(A,B)=\left\|\log\!\left(A^{-1/2}BA^{-1/2}\right)\right\|_{F},
$

and the Thompson distance

$
d_{\mathrm{Th}}(A,B)=\left\|\log\!\left(A^{-1/2}BA^{-1/2}\right)\right\|_{\mathrm{op}}
=\max_i |\log \lambda_i(A^{-1}B)|.
$

For pairs, use scale-invariant losses

$
L_{\mathrm{FR}}\big((\widehat\Sigma_1,\widehat\Sigma_2),(\Sigma_1,\Sigma_2)\big)
=\inf_{c>0}\Big(d_{\mathrm{FR}}(\widehat\Sigma_1,c\Sigma_1)^2+d_{\mathrm{FR}}(\widehat\Sigma_2,c^{-1}\Sigma_2)^2\Big),
$

$
L_{\mathrm{Th}}\big((\widehat\Sigma_1,\widehat\Sigma_2),(\Sigma_1,\Sigma_2)\big)
=\inf_{c>0}\Big(d_{\mathrm{Th}}(\widehat\Sigma_1,c\Sigma_1)^2+d_{\mathrm{Th}}(\widehat\Sigma_2,c^{-1}\Sigma_2)^2\Big).
$

For $m\in\{\mathrm{FR},\mathrm{Th}\}$ , define minimax risk

$
\mathcal{R}_{n,m}(d_1,d_2)=\inf_{\widehat\Sigma_1,\widehat\Sigma_2}\ \sup_{\Sigma_1\in\mathbb{S}_{++}^{d_1},\,\Sigma_2\in\mathbb{S}_{++}^{d_2}}
\mathbb{E}_{\Sigma_1,\Sigma_2}\!\left[L_m\big((\widehat\Sigma_1,\widehat\Sigma_2),(\Sigma_1,\Sigma_2)\big)\right],
$

where the infimum is over all measurable estimators based on $X_1,\dots,X_n$ .

### Unsolved Problem

Determine the exact finite-sample order (up to universal constant factors, with no $\operatorname{polylog}(d_1,d_2)$ slack) of $\mathcal{R}_{n,\mathrm{FR}}(d_1,d_2)$ and $\mathcal{R}_{n,\mathrm{Th}}(d_1,d_2)$ , and equivalently determine the sharp minimax sample complexities

$
n_m^\star(\varepsilon;d_1,d_2)=\min\{n:\mathcal{R}_{n,m}(d_1,d_2)\le \varepsilon^2\},\quad m\in\{\mathrm{FR},\mathrm{Th}\},
$

by proving matching upper and lower bounds that differ only by absolute constants and contain no extra logarithmic factors in $d_1,d_2$ .

## Significance & Implications

The source paper reports that matrix-normal bounds are minimax-optimal only up to logarithmic factors; closing this would remove the remaining known finite-sample rate gap. Absent a dedicated post-2021 resolution sweep, this problem appears open.

## Known Partial Results

This paper proves nonasymptotic guarantees for the MLE with sample complexity/rates minimax-optimal up to logarithmic factors, without conditioning/sparsity assumptions or initialization requirements.

## References

[1]

 [Near Optimal Sample Complexity for Matrix and Tensor Normal Models via Geodesic Convexity](https://arxiv.org/abs/2110.07583v3) 

Rafael Mendes de Oliveira, William Cole Franks, Akshay Ramachandran, Michael Walter (2021)

Annals of Statistics (accepted; to appear, 2025+ context)

📍 Abstract, p. 1 (arXiv v3 full text): "For the matrix normal model, all our bounds are minimax optimal up to logarithmic factors." Related open-direction discussion is in Section 8 (Conclusion and open problems).

Primary source paper (preprint first posted in 2021; later revised and accepted to Annals of Statistics).

 [Link ↗](https://arxiv.org/abs/2110.07583v3) [arXiv ↗](https://arxiv.org/abs/2110.07583v3)

## Notes / Progress

_Work log goes here._
