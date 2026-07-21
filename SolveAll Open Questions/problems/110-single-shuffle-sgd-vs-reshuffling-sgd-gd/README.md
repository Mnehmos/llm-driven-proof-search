# Can Single-Shuffle SGD be Better than Reshuffling SGD and GD?

**Status:** Unsolved  
**Source:** Posed by Chulhee Yun et al. (2021)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #110 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $n\ge 2$ , $K\ge 1$ , and $d\ge 1$ . Let $S_n$ denote the set of all permutations of $\{1,\dots,n\}$ . For real symmetric $d\times d$ matrices $X,Y$ , write $X\preceq Y$ for the Loewner order (i.e., $Y-X$ is positive semidefinite), and let $\|\cdot\|_2$ be the spectral (operator) norm. For a sequence of matrices $(B_1,\dots,B_n)$ , use the convention

$
\prod_{i=1}^n B_i := B_n\cdots B_1.
$

Given symmetric matrices $A_1,\dots,A_n$ , define for each $\sigma\in S_n$ the without-replacement product

$
P_\sigma := \prod_{i=1}^n A_{\sigma(i)}.
$

Define the three averaged quantities (all powers are matrix powers)

$
W_{\mathrm{SS}} := \frac{1}{n!}\sum_{\sigma\in S_n} \left(P_\sigma\right)^K,\qquad
W_{\mathrm{RS}} := \left(\frac{1}{n!}\sum_{\sigma\in S_n} P_\sigma\right)^K,\qquad
W_{\mathrm{GD}} := \left(\frac{1}{n}\sum_{i=1}^n A_i\right)^{nK}.
$

### Unsolved Problem

Is it true that for every $n\ge 2$ and $K\ge 1$ there exists a constant $\eta_{n,K}\in(0,1]$ (depending only on $n$ and $K$ , not on $d$ or on the specific matrices) such that, whenever

$
(1-\eta_{n,K})I \preceq A_i \preceq I\quad\text{for all } i\in\{1,\dots,n\},
$

one has

$
\|W_{\mathrm{SS}}\|_2 \le \|W_{\mathrm{RS}}\|_2 \le \|W_{\mathrm{GD}}\|_2\ ?
$

Equivalently: under uniform near-identity well-conditioning, does single-shuffle (expectation outside the $K$ -th power) never yield a larger spectral norm than random reshuffling (expectation inside the $K$ -th power), and is random reshuffling never worse than the full-gradient proxy $W_{\mathrm{GD}}$ , with constants uniform over dimension and instances?

## Significance & Implications

The conjecture asks for a dimension-free, instance-uniform ordering between three concrete noncommutative averages of epoch-wise update matrices. In finite-sum optimization analyses where one epoch corresponds to multiplying near-identity factors (e.g., $A_i=I-\alpha M_i$ with small step size $\alpha$ ), bounds on $\|W_{\mathrm{SS}}\|_2,\|W_{\mathrm{RS}}\|_2,\|W_{\mathrm{GD}}\|_2$ translate into quantitative comparisons of expected contraction under single-shuffle, per-epoch reshuffling, and a full-gradient baseline for quadratic/linear models. Establishing existence of $\eta_{n,K}$ depending only on $(n,K)$ would provide a clean matrix-inequality tool that separates the algorithmic difference "where the expectation is taken" (before vs after the $K$ -th power) and links without-replacement sampling effects to strengthened noncommutative AM-GM-type inequalities in a regime (uniformly well-conditioned, near-identity factors) tailored to SGD step-size constraints.

## Known Partial Results

- The problem is motivated by extensions of the Recht-Re noncommutative AM-GM conjecture, augmented to include a term capturing the single-shuffle (shuffle-once) sampling scheme that is not covered by the original conjecture.

- Existing counterexamples to the most general PSD-matrix versions of related AM-GM-type conjectures rely on rank-deficient (singular) matrices; this motivates restricting attention to positive definite matrices with uniformly bounded condition number, modeled here by $(1-\eta)I\preceq A_i\preceq I$ .

- The near-identity constraint $(1-\eta)I\preceq A_i\preceq I$ matches common SGD linearization forms $A_i=I-\alpha M_i$ under small step sizes, and the conjecture seeks an $\eta_{n,K}$ that is uniform over all such instances and all dimensions.

- In the commuting (simultaneously diagonalizable) case, all products $P_\sigma$ coincide, so $W_{\mathrm{SS}}=W_{\mathrm{RS}}$ , and the comparison to $W_{\mathrm{GD}}$ reduces to scalar inequalities.

- As reported in the open-problem note, one can prove $\|W_{\mathrm{SS}}\|_2\le \|W_{\mathrm{RS}}\|_2$ for sufficiently small step sizes in the structured form $A_i=I-\alpha M_i$ , but the allowable smallness may depend on the specific instance; the open problem asks for a bound depending only on $(n,K)$ .

- Suggested by special cases discussed in the note, a scaling like $\eta_{n,K}=O(1/(nK))$ is plausible, but no dimension-free, instance-uniform choice is currently established in general.

## References

[1]

 [Open Problem: Can Single-Shuffle SGD be Better than Reshuffling SGD and GD?](https://proceedings.mlr.press/v134/open-problem-yun21a.html) 

Chulhee Yun, Suvrit Sra, Ali Jadbabaie (2021)

Conference on Learning Theory (COLT), PMLR 134

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v134/open-problem-yun21a.html) [2]

 [Open Problem: Can Single-Shuffle SGD be Better than Reshuffling SGD and GD? (PDF)](http://proceedings.mlr.press/v134/yun21a/yun21a.pdf) 

Chulhee Yun, Suvrit Sra, Ali Jadbabaie (2021)

Conference on Learning Theory (COLT), PMLR 134

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v134/yun21a/yun21a.pdf)

## Notes / Progress

_Work log goes here._
