# Computational Threshold for Tensor PCA

**Status:** Unsolved  
**Importance:** Major
**Source:** Posed by Richard & Montanari (2014)

## Categories

- Mathematical Statistics
- Learning Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #8 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix an integer $k \ge 3$ . For each dimension $n$ , let $T \in (\mathbb{R}^n)^{\otimes k}$ be an order- $k$ real tensor with entries $\{T_{i_1,\dots,i_k}\}_{i_1,\dots,i_k=1}^n$ . Consider the hypothesis-testing problem

$
H_0:\; T=W,
\qquad
H_1:\; T=\lambda_n\,x^{\otimes k}+W,
$

where:

- 

 $W$ is a Gaussian noise tensor with independent entries $W_{i_1,\dots,i_k}\sim \mathcal N(0,1)$ ;

- 

 $x\in\{\pm 1\}^n$ is an unknown spike vector (typically drawn uniformly from $\{\pm 1\}^n$ under $H_1$ , independently of $W$ );

- 

 $x^{\otimes k}$ is the rank-one tensor with entries $(x^{\otimes k})_{i_1,\dots,i_k}=x_{i_1}\cdots x_{i_k}$ ;

- 

 $\lambda_n>0$ is the signal strength (possibly depending on $n$ ).

A (possibly randomized) detector is a map $\phi_n:(\mathbb R^n)^{\otimes k}\to\{0,1\}$ , with output $1$ meaning “spike present.” Detection is said to succeed asymptotically if

$
\mathbb P_{H_0}(\phi_n(T)=1)+\mathbb P_{H_1}(\phi_n(T)=0)\to 0
\quad\text{as }n\to\infty.
$

Call $\phi_n$ polynomial-time if its running time is polynomial in $n$ .

In this normalization, standard benchmarks (fixed $k\ge 3$ ) are: information-theoretically, detection is possible for $\lambda_n\gg n^{-k/4}$ ; known polynomial-time unfolding/matricization-based spectral methods require roughly $\lambda_n\gg n^{-(k-1)/4}$ (sometimes with polylogarithmic factors depending on the precise algorithm/result). Here $a_n\gg b_n$ means $a_n/b_n\to\infty$ , and $a_n\ll b_n$ means $a_n/b_n\to 0$ .

Equivalent unit-sphere convention: if $u=x/\sqrt n\in\mathbb S^{n-1}$ , then

$
T=\tilde\lambda_n\,u^{\otimes k}+W,\qquad \tilde\lambda_n=\lambda_n n^{k/2}.
$

Under this conversion, the above two benchmark scales become $\tilde\lambda_n\gg n^{k/4}$ (information-theoretic) and $\tilde\lambda_n\gg n^{(k+1)/4}$ (known polynomial-time spectral).

### Unsolved Problem

Does there exist a polynomial-time sequence of detectors that succeeds for signal levels in the intermediate regime

$
n^{-k/4}\ll \lambda_n \ll n^{-(k-1)/4},
$

or, instead, is it true that no polynomial-time algorithm can reliably detect in this regime (an intrinsic computational-statistical gap)? As of October 2025, this remains open.

## Significance & Implications

Tensor PCA is a canonical model for computational-statistical gaps. Unlike matrix PCA ( $k=2$ ), tensors of order $k\ge 3$ are believed to exhibit a hard intermediate regime. This connects to sum-of-squares, average-case complexity, and limits of efficient inference in high dimensions. Low-degree likelihood-ratio analyses provide strong predictive (but not unconditional) evidence for the conjectured hardness; see [Kunisky et al. (2019)](#references) , especially Conjecture 2.4. See also the related [Sparse PCA problem](/problem/minimax-optimal-sparse-pca-computational-gap) .

## Known Partial Results

- Degree-4 SoS guarantees: [Hopkins et al. (2015)](#references) gives polynomial-time guarantees at essentially the unfolding/spectral scale via degree-4 sum-of-squares ideas (with formulation-dependent log factors); this citation should not be read as proving a general degree- $O(n^{\delta})$ SoS lower bound for tensor PCA.

- Low-degree evidence: [Kunisky et al. (2019)](#references) provides heuristic/predictive evidence (not an unconditional lower bound), including Conjecture 2.4 for Tensor PCA.

- No unconditional lower bound (e.g., from $\mathsf{P}\neq\mathsf{NP}$ ) is known for the average-case detection task in the intermediate regime.

- The gap disappears for $k=2$ (matrix PCA).

- Status checkpoint in cited literature: open.

## References

[1]

 [A statistical model for tensor PCA](https://arxiv.org/abs/1411.1076) 

Emile Richard, Andrea Montanari (2014)

NeurIPS

📍 Section 1 (Introduction), in the “We next summarize our results” discussion contrasting “Ideal estimation” with “Tractable estimators: Unfolding/Power iteration” (computational-statistical gap), p. 2 (NeurIPS 2014 PDF)

 [arXiv ↗](https://arxiv.org/abs/1411.1076) [2]

 [Tensor Principal Component Analysis via Sum-of-Square Proofs](https://arxiv.org/abs/1507.03269) 

Samuel B. Hopkins, Jonathan Shi, David Steurer (2015)

COLT

📍 Abstract and Section 1: polynomial-time tensor-PCA guarantees via degree-4 sum-of-squares / spectral methods at the unfolding-scale threshold (for order-3, near $n^{-1/2}$ up to log factors in the convention used here).

 [arXiv ↗](https://arxiv.org/abs/1507.03269) [3]

 [Notes on computational hardness of hypothesis testing: Predictions using the low-degree likelihood ratio](https://arxiv.org/abs/1907.11636) 

Dmitriy Kunisky, Alexander S. Wein, Afonso S. Bandeira (2019)

📍 Section 2.3 (Tensor PCA), especially Conjecture 2.4: low-degree evidence as a predictive conjecture for hardness near the spectral threshold.

 [arXiv ↗](https://arxiv.org/abs/1907.11636)

## Notes / Progress

_Work log goes here._
