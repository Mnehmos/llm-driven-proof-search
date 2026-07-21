# Exact information-theoretic detection threshold for correlated SBM vs Erdos-Renyi pair

**Status:** Partially Resolved  
**Source:** Sourced from the work of Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li

## Categories

- Probability Theory
- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #33 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix constants $k\ge 2$ , $\lambda>0$ , and $\epsilon\in[-1/(k-1),1]$ , and for each $n$ define

$
p_{\mathrm{in}}=\frac{\lambda(1+(k-1)\epsilon)}{n},\qquad
p_{\mathrm{out}}=\frac{\lambda(1-\epsilon)}{n}.
$

Assume $n$ is large enough that $p_{\mathrm{in}},p_{\mathrm{out}}\in[0,1]$ . Let $[k]=\{1,\dots,k\}$ .

Under $H_1$ (correlated SBM with latent matching), sample a parent graph $G^\star$ on latent vertices $[n]$ by first drawing labels $\sigma_1,\dots,\sigma_n\overset{i.i.d.}{\sim}\mathrm{Unif}([k])$ , then conditionally on $\sigma$ sampling edges independently with

$
\mathbb P\big((i,j)\in E(G^\star)\mid \sigma\big)=
\begin{cases}
p_{\mathrm{in}},&\sigma_i=\sigma_j,\\
p_{\mathrm{out}},&\sigma_i\ne \sigma_j.
\end{cases}
$

Generate $A^\star,B^\star$ by independent edge subsampling from $G^\star$ with parameter $s\in[0,1]$ (keep each parent edge independently in each child with probability $s$ , and never add non-parent edges). Then draw a latent uniform permutation $\pi\in S_n$ , independent of everything else, and observe

$
A:=A^\star,\qquad B:=\pi(B^\star),
$

where $\pi(B^\star)$ is the relabeled graph. Let $P_n=P_{n,\lambda,k,\epsilon,s}$ be the law of observed $(A,B)$ .

Under $H_0$ , let $Q_n$ be the law where $A,B$ are independent Erdos-Renyi graphs $G(n,\lambda s/n)$ (equivalently, independent even after an unknown relabeling of one graph).

### Unsolved Problem

For a test $\phi_n$ (measurable map from pairs of adjacency matrices to $\{0,1\}$ , with $\phi_n=1$ meaning $H_1$ ), define

$
R_n(\phi_n)=P_n(\phi_n=0)+Q_n(\phi_n=1).
$

Determine the exact information-theoretic threshold $s_{\mathrm{IT}}(\lambda,\epsilon,k)\in[0,1]$ such that

$
\inf_{\phi_n}R_n(\phi_n)\to 0\ \text{as }n\to\infty\quad\Longleftrightarrow\quad s>s_{\mathrm{IT}}(\lambda,\epsilon,k),
$

and for $s no sequence of tests has vanishing total error.

## Significance & Implications

With known alignment, the problem is effectively trivialized by edge-overlap statistics; the latent-permutation formulation is the nontrivial model studied in the source line of work. The exact information-theoretic threshold in this corrected model is still not pinned down, but post-2024 results (including arXiv:2503.06464v2) now give additional algorithmic/impossibility evidence in specific parameter regimes.

## Known Partial Results

Proven: (i) For low-degree polynomial tests, arXiv:2409.00966v2 establishes a sharp threshold at $s>\min\{\sqrt{\alpha},1/(\lambda\epsilon^2)\}$ (Theorem 1.3 / abstract). (ii) Recent work, arXiv:2503.06464v2, proves additional algorithmic achievability and impossibility statements in sparse-regime parameter slices (see its abstract for exact quantified regimes).

Heuristic evidence (not yet a full IT characterization): arXiv:2409.00966v2, Remark 1.4 (p. 4) argues plausibility of strong detection at least when $s>\min\{C^*(k)/(\lambda\epsilon^2),\sqrt{\alpha},\sqrt{1/\lambda}\}$ by combining prior SBM and correlated-ER intuitions.

Net status after correcting the model to include latent permutation: the exact information-theoretic threshold $s_{\mathrm{IT}}(\lambda,\epsilon,k)$ remains open.

## References

[1]

 [A Computational Transition for Detecting Correlated Stochastic Block Models by Low-Degree Polynomials](https://arxiv.org/abs/2409.00966v2) 

Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li (2025)

arXiv preprint

📍 Introduction: model definition of correlated SBM pair with latent vertex correspondence and testing setup against independent $G(n,\lambda s/n)$; Theorem 1.3 (low-degree threshold); Remark 1.4 (plausibility formula $s>\min\{C^*(k)/(\lambda\epsilon^2),\sqrt{\alpha},\sqrt{1/\lambda}\}$), p. 4 in v2 PDF.

Primary source for the correlated-SBM-vs-ER detection problem and the low-degree threshold; includes an explicit plausibility discussion for stronger detection bounds.

 [Link ↗](https://arxiv.org/abs/2409.00966v2) [DOI ↗](https://doi.org/10.48550/arXiv.2409.00966) [arXiv ↗](https://arxiv.org/abs/2409.00966v2) [2]

 [Correlated SBM Detection and Matching in the Sparse Regime](https://arxiv.org/abs/2503.06464v2) 

Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li (2025)

arXiv preprint

📍 Abstract (v2): computationally efficient strong detection above roughly $s>\lambda^{-1/2+\gamma}$ under stated signal conditions, and information-theoretic impossibility below roughly $s<\lambda^{-1/2-\gamma}$ in a complementary sparse-signal regime.

Recent follow-up giving additional sparse-regime detection/matching results relevant to the IT-threshold landscape.

 [Link ↗](https://arxiv.org/abs/2503.06464v2) [DOI ↗](https://doi.org/10.48550/arXiv.2503.06464) [arXiv ↗](https://arxiv.org/abs/2503.06464v2)

## Notes / Progress

_Work log goes here._
