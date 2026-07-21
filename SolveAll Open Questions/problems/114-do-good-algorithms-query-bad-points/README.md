# Do Good Algorithms Necessarily Query Bad Points?

**Status:** Unsolved  
**Source:** Posed by Rong Ge et al. (2019)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #114 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal{W}\subseteq\mathbb{R}^d$ be a closed convex set. Consider stochastic convex optimization of

$
F(w)=\mathbb{E}_{\xi\sim D}[f(w;\xi)]
$

where $F$ is convex on $\mathcal{W}$ and attains its minimum at some $w^*\in\arg\min_{w\in\mathcal{W}}F(w)$ . A stochastic first-order oracle, when queried at $w_t\in\mathcal{W}$ , returns $g_t=\nabla f(w_t;\xi_t)$ such that (unbiasedness)

$
\mathbb{E}[g_t\mid \mathcal{F}_{t-1},w_t]=\nabla F(w_t),
$

where $\mathcal{F}_{t-1}=\sigma(\xi_1,\ldots,\xi_{t-1})$ ; the problem class $\mathcal{P}$ further specifies regularity/noise assumptions (e.g. a uniform second-moment bound $\mathbb{E}[\|g_t\|^2\mid \mathcal{F}_{t-1},w_t]\le G^2$ for all $t$ and $w_t\in\mathcal{W}$ ).

For $t\ge 1$ , define the minimax expected excess-risk rate after $t$ oracle calls by

$
R_t^*:=\inf_{A}\ \sup_{(F,D)\in\mathcal{P}}\ \mathbb{E}\bigl[F(\hat w_t)-F(w^*)\bigr],
$

where the infimum ranges over all (possibly randomized) algorithms $A$ that make $t$ oracle queries and output $\hat w_t\in\mathcal{W}$ measurable with respect to $\mathcal{F}_t$ .

Define a (stochastic) first-order algorithm to be non-adaptive if its query points are affine functions of past observed gradients with coefficients fixed before the run: there exist deterministic vectors $b_t\in\mathbb{R}^d$ and deterministic matrices $A_{t,j}\in\mathbb{R}^{d\times d}$ (allowed to depend on $t$ and on known problem parameters, but not on the realized oracle randomness) such that for all $t\ge 1$ ,

$
w_t\ =\ \Pi_{\mathcal{W}}\Bigl(b_t+\sum_{j=1}^{t-1}A_{t,j}g_j\Bigr),
$

where $\Pi_{\mathcal{W}}$ is Euclidean projection onto $\mathcal{W}$ .

### Unsolved Problem

 **Problem 2019.** For a given class $\mathcal{P}$ , is it information-theoretically impossible for a non-adaptive algorithm to have uniformly minimax-optimal query points at all sufficiently large times? Concretely, must it be the case that for every non-adaptive algorithm and every constant $C<\infty$ there exist arbitrarily large $t$ for which

$
\sup_{(F,D)\in\mathcal{P}}\ \mathbb{E}[F(w_t)-F(w^*)]\ >\ C\,R_t^*?
$

Equivalently, is it necessary that

$
\limsup_{t\to\infty}\ \frac{\sup_{(F,D)\in\mathcal{P}}\mathbb{E}[F(w_t)-F(w^*)]}{R_t^*}\ >\ 1,
$

possibly with a gap that grows (e.g. polylogarithmically) with $t$ for some natural choices of $\mathcal{P}$ ?

## Significance & Implications

Minimax rates $R_t^*$ are defined for an algorithm's output after $t$ oracle calls, but many stochastic-approximation methods are used in "anytime" or streaming settings where the current iterate $w_t$ itself is deployed. This problem isolates whether non-adaptivity (fixed, pre-scheduled linear use of past gradients) fundamentally prevents having all query points achieve minimax-order excess risk, even when some function of the history (e.g. an averaged iterate) can be minimax-optimal. A negative answer would justify algorithmic designs that explicitly trade off statistical optimality against the reliability of intermediate iterates; a positive answer would imply that, at least information-theoretically, minimax-optimal performance need not require repeatedly querying provably bad points.

## Known Partial Results

- Classical stochastic-approximation results show that, for standard convex/noise classes $\mathcal{P}$ , SGD with polynomially decaying step sizes combined with iterate averaging can achieve minimax-order excess risk (for the averaged output) under unbiased-gradient and moment conditions.

- The COLT 2019 open problem asks whether such minimax-optimality of an output statistic can coexist with minimax-optimality of the raw query points $\{w_t\}$ for non-adaptive first-order methods, or whether some $w_t$ must remain separated from $R_t^*$ infinitely often in the worst case over $\mathcal{P}$ .

## References

[1]

 [Open Problem: Do Good Algorithms Necessarily Query Bad Points?](https://proceedings.mlr.press/v99/ge19b.html) 

Rong Ge, Prateek Jain, Sham M. Kakade, Rahul Kidambi, Dheeraj M. Nagaraj, Praneeth Netrapalli (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v99/ge19b.html) [2]

 [Open Problem: Do Good Algorithms Necessarily Query Bad Points? (PDF)](http://proceedings.mlr.press/v99/ge19b/ge19b.pdf) 

Rong Ge, Prateek Jain, Sham M. Kakade, Rahul Kidambi, Dheeraj M. Nagaraj, Praneeth Netrapalli (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v99/ge19b/ge19b.pdf)

## Notes / Progress

_Work log goes here._
