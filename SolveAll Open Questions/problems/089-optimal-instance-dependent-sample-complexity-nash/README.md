# Optimal Instance-Dependent Sample Complexity for finding Nash Equilibrium in Two Player Zero-Sum Matrix games

**Status:** Unsolved  
**Source:** Posed by Arnab Maiti (2025)

## Categories

- Learning Theory
- Mathematical Statistics
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #89 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $A \in [-1,1]^{n \times m}$ be an unknown payoff matrix of a two-player zero-sum matrix game. The row player chooses $x \in \Delta_n := \{x \in \mathbb{R}^n_{\ge 0}: \sum_{i=1}^n x_i = 1\}$ and the column player chooses $y \in \Delta_m$ ; the expected payoff to the row player is $x^\top A y$ . The (minimax) value is

$
v(A) := \max_{x \in \Delta_n}\min_{y \in \Delta_m} x^\top A y = \min_{y \in \Delta_m}\max_{x \in \Delta_n} x^\top A y.
$

The algorithm does not observe $A$ directly. On each round $t$ , it adaptively selects an entry $(i_t,j_t) \in [n] \times [m]$ and receives a random sample $X_t$ such that $\mathbb{E}[X_t \mid i_t,j_t] = A_{i_t j_t}$ and the noise $X_t - A_{i_t j_t}$ is (say) conditionally 1-sub-Gaussian. For accuracy $\varepsilon>0$ and confidence $\delta \in (0,1)$ , an output pair $(\hat x,\hat y) \in \Delta_n \times \Delta_m$ is an $\varepsilon$ -approximate Nash equilibrium (equivalently, an $\varepsilon$ -approximate saddle point) if its exploitability is at most $\varepsilon$ :

$
\max_{x\in\Delta_n} x^\top A\hat y - \hat x^\top A\hat y \le \varepsilon
\quad\text{and}\quad
\hat x^\top A\hat y - \min_{y\in\Delta_m} \hat x^\top A y \le \varepsilon.
$

Define the instance-dependent sample complexity $T^*(A,\varepsilon,\delta)$ as the smallest integer $T$ for which there exists an adaptive algorithm that, on instance $A$ , makes at most $T$ noisy entry queries and outputs an $\varepsilon$ -approximate Nash equilibrium with probability at least $1-\delta$ .

### Unsolved Problem

Characterize $T^*(A,\varepsilon,\delta)$ for general two-player zero-sum matrix games under this noisy-entry sampling model by proving matching (up to universal constants and/or logarithmic factors) information-theoretic lower bounds and achievable upper bounds that depend on the specific matrix $A$ (not only on $n,m,\varepsilon,\delta$ ).

## Significance & Implications

An instance-dependent characterization would identify which concrete properties of a particular payoff matrix $A$ (e.g., entry-wise separations relevant to equilibrium optimality) control the minimal number of noisy samples needed for equilibrium identification, rather than only providing worst-case rates over all $A$ . This would extend the "gap-dependent" perspective from stochastic bandits to strategic decision problems where performance depends on a coupled minimax structure, and would yield algorithms with provably optimal adaptive sampling behavior on easy instances while certifying unavoidable difficulty on hard instances.

## Known Partial Results

- Instance-dependent (gap-dependent) sample complexity is well studied for stochastic multi-armed bandits; the COLT 2025 note highlights that an analogous sharp instance-dependent theory for noisy two-player zero-sum matrix games is largely unexplored.

- The COLT 2025 open-problem note formulates the above noisy-entry model and explicitly asks for matching instance-dependent lower and upper bounds for identifying an $\varepsilon$ -approximate Nash equilibrium in general $n \times m$ zero-sum matrix games.

## References

[1]

 [Open Problem: Optimal Instance-Dependent Sample Complexity for finding Nash Equilibrium in Two Player Zero-Sum Matrix games](https://proceedings.mlr.press/v291/maiti25b.html) 

Arnab Maiti (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v291/maiti25b.html) [2]

 [Open Problem: Optimal Instance-Dependent Sample Complexity for finding Nash Equilibrium in Two Player Zero-Sum Matrix games (PDF)](https://raw.githubusercontent.com/mlresearch/v291/main/assets/maiti25b/maiti25b.pdf) 

Arnab Maiti (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Proceedings PDF.

 [Link ↗](https://raw.githubusercontent.com/mlresearch/v291/main/assets/maiti25b/maiti25b.pdf)

## Notes / Progress

_Work log goes here._
