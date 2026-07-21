# Fixed-Parameter Tractability of Zonotope Problems

**Status:** Partially Resolved  
**Source:** Posed by Vincent Froese et al. (2025)

## Categories

- Learning Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #86 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d,m \in \mathbb{Z}_{>0}$ . A (centrally symmetric) zonotope in $\mathbb{R}^d$ given in generator form is

$
Z(c,G) := \{c+G\lambda : \lambda \in [-1,1]^m\} = \left\{c+\sum_{i=1}^m \lambda_i g_i : \lambda_i \in [-1,1]\right\},
$

where $c \in \mathbb{Q}^d$ and $G=[g_1\ \cdots\ g_m] \in \mathbb{Q}^{d\times m}$ are encoded in binary. Let $N$ be the total input bit-length of all rational data (including thresholds).

Consider the following decision problems, parameterized by the ambient dimension $d$ .

(1) ( $\ell_p$ -zonotope norm maximization, decision version.) Fix a constant $p \in [1,\infty]$ that is not part of the input. Given $(c,G)$ and a threshold $T\in\mathbb{Q}$ , decide whether

$
\max_{z\in Z(c,G)} \|z\|_p \ge T,
$

where $\|\cdot\|_p$ is the standard $\ell_p$ norm on $\mathbb{R}^d$ (in particular, $\|z\|_\infty = \max_{i\in[d]} |z_i|$ ).

(2) (Zonotope containment.) Given two zonotopes $Z_1=Z(c_1,G_1)\subseteq\mathbb{R}^d$ and $Z_2=Z(c_2,G_2)\subseteq\mathbb{R}^d$ (with rational data encoded in binary), decide whether $Z_1 \subseteq Z_2$ .

### Unsolved Problem

Is (1) and/or (2) fixed-parameter tractable with respect to $d$ ? Concretely, does there exist an algorithm with running time $f(d)\cdot N^{O(1)}$ (for some computable function $f$ depending only on $d$ ) that solves the corresponding decision problem? If not, can one prove parameterized intractability in $d$ (e.g., W[1]-hardness under standard parameterized reductions)?

## Significance & Implications

These are basic geometric primitives on zonotopes whose classical complexity changes sharply with the dimension: both problems are NP-hard when $d$ is part of the input, yet admit polynomial-time algorithms when $d$ is fixed. Determining whether the dependence on $d$ can be isolated into an $f(d)$ factor (FPT in $d$ ) would clarify whether dimension-parameterized algorithms are possible for zonotope subroutines that arise in analyses of one-hidden-layer ReLU networks (norm maximization for Lipschitz-type quantities; (non-)containment for reachability/positivity-type questions) and in other application areas where the ambient dimension can be substantially smaller than the number of generators.

## Known Partial Results

- Motivating reductions: for one-hidden-layer ReLU networks, computing a Lipschitz constant can be formulated as maximizing an $\ell_p$ norm over an associated zonotope, and deciding whether a positive output is attainable can be formulated via zonotope (non-)containment.

- Worst-case complexity: both $\ell_p$ -norm maximization over a zonotope (for fixed constant $p$ ) and zonotope containment are NP-hard when the dimension $d$ is part of the input.

- Fixed-dimension tractability: for every fixed constant $d$ , both problems admit algorithms running in time polynomial in the input encoding length $N$ .

- Froese, Grillo, Hertrich, and Stargalla (arXiv 2509.22849, September 26, 2025) show that zonotope (non-)containment is W[1]-hard with respect to $d$ , negatively resolving that part of the COLT 2025 question.

- The parameterized status of $\ell_p$ norm maximization over zonotopes, especially for fixed $p\in(1,\infty)$ , remains open.

## References

[1]

 [Open Problem: Fixed-Parameter Tractability of Zonotope Problems](https://proceedings.mlr.press/v291/froese25b.html) 

Vincent Froese, Moritz Grillo, Christoph Hertrich, Martin Skutella (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v291/froese25b.html) [2]

 [Open Problem: Fixed-Parameter Tractability of Zonotope Problems (PDF)](https://raw.githubusercontent.com/mlresearch/v291/main/assets/froese25b/froese25b.pdf) 

Vincent Froese, Moritz Grillo, Christoph Hertrich, Martin Skutella (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Proceedings PDF.

 [Link ↗](https://raw.githubusercontent.com/mlresearch/v291/main/assets/froese25b/froese25b.pdf) [3]

 [The zonotope containment problem](https://doi.org/10.1016/j.ejcon.2021.06.028) 

Hendrik Kulmburg, Matthias Althoff (2021)

European Journal of Control

📍 Related algorithmic and complexity background for zonotope containment.

 [Link ↗](https://doi.org/10.1016/j.ejcon.2021.06.028) [DOI ↗](https://doi.org/10.1016/j.ejcon.2021.06.028)

## Notes / Progress

_Work log goes here._
