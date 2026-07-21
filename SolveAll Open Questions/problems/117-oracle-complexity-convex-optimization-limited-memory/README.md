# The Oracle Complexity of Convex Optimization with Limited Memory

**Status:** Partially Resolved  
**Source:** Posed by Blake Woodworth et al. (2019)

## Categories

- Learning Theory
- Optimization & Variational Methods
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #117 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix dimension $d\in\mathbb{N}$ and parameters $L,B,\epsilon>0$ . Let $\mathcal{F}_{L,B}$ be the class of convex functions $F:B_2(B)\to\mathbb{R}$ on the Euclidean ball $B_2(B)=\{x\in\mathbb{R}^d:\|x\|_2\le B\}$ that are $L$ -Lipschitz in $\|\cdot\|_2$ , i.e., $|F(x)-F(y)|\le L\|x-y\|_2$ for all $x,y\in B_2(B)$ (equivalently, every subgradient satisfies $\|g\|_2\le L$ wherever it exists). A first-order oracle, queried at $x\in B_2(B)$ , returns a pair $(F(x),g)$ where $g\in\partial F(x)$ is an arbitrary valid subgradient.

A deterministic first-order algorithm with memory budget $M$ bits and $T$ oracle queries is an interactive procedure that, between queries, retains only a state $\mu_t\in\{0,1\}^M$ (initialized to $\mu_1=0$ ). At round $t$ , it chooses $x_t=\phi_t(\mu_t)\in B_2(B)$ , receives $(F(x_t),g_t)$ with $g_t\in\partial F(x_t)$ , updates $\mu_{t+1}=\psi_t(\mu_t,F(x_t),g_t)$ , and after $T$ rounds outputs $\hat x=\zeta(\mu_{T+1})\in B_2(B)$ . The algorithm may perform arbitrary computation during a round, but only $M$ bits persist across rounds.

Define the minimax memory-bounded oracle complexity $T_{L,B}(d,M,\epsilon)$ as the smallest $T\in\mathbb{N}$ for which there exists such an $M$ -bit deterministic algorithm guaranteeing

$
\sup_{F\in\mathcal{F}_{L,B}}\ \sup_{g_1\in\partial F(x_1),\ldots,g_T\in\partial F(x_T)}\ \Big(F(\hat x)-\min_{x\in B_2(B)}F(x)\Big)\le\epsilon.
$

(If no such $T$ exists, set $T_{L,B}(d,M,\epsilon)=\infty$ .)

### Unsolved Problem

 **Problem 2019.** Characterize $T_{L,B}(d,M,\epsilon)$ , i.e., the achievable query-memory tradeoffs $(T,M)$ , up to constant factors (and at most polylogarithmic factors). In particular, determine whether one can achieve near-optimal first-order query complexity $T=\tilde O\big(d\,\mathrm{polylog}(LB/\epsilon)\big)$ with subquadratic memory $M=O(d^{2-\delta})$ for some fixed $\delta>0$ , or whether achieving such $T$ inherently requires (up to logarithmic factors) $\Omega(d^2)$ bits of memory.

## Significance & Implications

For nonsmooth convex optimization with an $L$ -Lipschitz objective over a radius- $B$ Euclidean ball, the optimal first-order oracle query complexity (without memory constraints) scales as $\Theta\big(d\log(LB/\epsilon)\big)$ in the worst case, and is achieved by cutting-plane/center-of-mass type methods. However, known near-optimal-query methods maintain rich geometric information (e.g., an evolving polytope/ellipsoid defined by many past cuts), suggesting a quadratic-in- $d$ memory footprint. This problem asks whether that quadratic memory is an artifact of current implementations or an information-theoretic necessity, thereby isolating the fundamental tradeoff between two core resources for first-order optimization: number of oracle queries versus persistent memory.

## Known Partial Results

- Near-optimal query rates are achievable without memory limits: classical cutting-plane methods (e.g., center-of-mass) attain $O\big(d\log(LB/\epsilon)\big)$ first-order queries for Lipschitz convex optimization over $B_2(B)$ , and this dependence is minimax-optimal in the regime considered by the note.

- Low-memory, simple iterative methods can be made memory-efficient but require many more queries: a discretized, memory-bounded gradient-descent-type scheme achieves $\epsilon$ -suboptimality using $O\big((L^2B^2)/\epsilon^2\big)$ oracle queries with $O\big(d\log(LB/\epsilon)\big)$ bits of persistent memory (note Appendix A, Theorem 1).

- Any method that succeeds uniformly over all $F\in\mathcal{F}_{L,B}$ must store nontrivial information: for $\epsilon\le LB/2$ , at least $\Omega\big(d\log(LB/(2\epsilon))\big)$ bits of memory are necessary even to output an $\epsilon$ -suboptimal point in the worst case (note Appendix C, Theorem 5).

- The note gives an explicit finite-precision/memory accounting showing that a center-of-mass-style method can retain the $O\big(d\log(LB/\epsilon)\big)$ query bound while using $O\big(d^2\log^2(LB/\epsilon)\big)$ bits of memory (note Appendix B).

- Blanchard, Zhang, and Jaillet (COLT 2023) prove that deterministic first-order algorithms need quadratic memory to attain optimal $\tilde O(d)$ query complexity, resolving the headline near-optimal-query/subquadratic-memory question negatively.

- The full query-memory tradeoff outside that headline regime remains only partially characterized.

## References

[1]

 [Open Problem: The Oracle Complexity of Convex Optimization with Limited Memory](https://proceedings.mlr.press/v99/woodworth19a.html) 

Blake Woodworth, Nathan Srebro (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v99/woodworth19a.html) [2]

 [Open Problem: The Oracle Complexity of Convex Optimization with Limited Memory (PDF)](http://proceedings.mlr.press/v99/woodworth19a/woodworth19a.pdf) 

Blake Woodworth, Nathan Srebro (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v99/woodworth19a/woodworth19a.pdf)

## Notes / Progress

_Work log goes here._
