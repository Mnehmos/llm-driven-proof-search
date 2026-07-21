# AdaBoost Always Cycles? (Global Dynamics Conjecture)

**Status:** Resolved  
**Importance:** Notable
**Source:** Posed by Rudin, Daubechies, and Schapire (2004)

## Categories

- Learning Theory
- Dynamical Systems & Ergodic Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #9 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $S=\{(x_i,y_i)\}_{i=1}^m$ be a fixed binary-labeled dataset with $y_i\in\{-1,+1\}$ , and let $\mathcal H$ be a weak-hypothesis class. Consider the discrete AdaBoost update of [Freund & Schapire (1997)](#references) , in the exhaustive weak-learner regime used in [Rudin et al. (2012)](#references) , with weight vectors $w_t\in\Delta^{m-1}$ (the probability simplex). At iteration $t$ , choose

$
h_t\in\arg\max_{h\in\mathcal H}\sum_{i=1}^m w_{t,i}\,y_i\,h(x_i),
$

define weighted error

$
\varepsilon_t=\sum_{i=1}^m w_{t,i}\,\mathbf 1\{h_t(x_i)\neq y_i\},
$

and update with

$
\alpha_t=\frac12\log\frac{1-\varepsilon_t}{\varepsilon_t},\qquad
w_{t+1,i}=\frac{w_{t,i}\exp(-\alpha_t y_i h_t(x_i))}{Z_t},
$

where $Z_t$ normalizes to $\sum_i w_{t+1,i}=1$ .

Equivalently, with finite hypothesis set $\mathcal H=\{\tilde h_1,\dots,\tilde h_N\}$ and matrix $M\in\{-1,+1\}^{m\times N}$ defined by $M_{ij}=y_i\tilde h_j(x_i)$ , step $t$ selects

$
j_t\in\arg\max_{j\in[N]}(w_t^\top M)_j,\qquad h_t=\tilde h_{j_t}.
$

As specified in [Rudin et al. (2012)](#references) , if this argmax is not unique, ties are broken in a fixed deterministic way (for concreteness: pick the smallest index $j$ ). The generic no-tie condition means the argmax is unique at every iterate, i.e.

$
(w_t^\top M)_j\neq (w_t^\top M)_{j'}\quad\text{for all }j\neq j'\text{ and all }t,
$

equivalently, $w_t$ never lands on a tie boundary between weak-hypothesis regions of the simplex.

This induces a discrete dynamical system $\,T:\Delta^{m-1}\to\Delta^{m-1}$ by $w_{t+1}=T(w_t)$ .

### Unsolved Problem

Does every trajectory converge to a cycle under natural genericity conditions?

## Significance & Implications

A full resolution would pin down the long-run behavior of one of the most influential learning algorithms, with direct implications for stopping rules, margin evolution, and stability explanations for boosting in practice. The problem also links learning-theory analysis to core tools from dynamical systems and ergodic theory.

## Known Partial Results

- [Rudin et al. (2004)](#references) : established a dynamical-systems framework and documented cyclic behavior in important regimes.

- [Choromanska & Langford (2012)](#references) : proved strong convergence properties under no-tie-type conditions and gave evidence supporting the cycling conjecture.

- [Scovel et al. (2022)](#references) : developed a direct limit-cycle analysis and structural correspondence results.

- No general theorem is known that Optimal AdaBoost always cycles for all relevant settings.

## References

[1]

 [A Decision-Theoretic Generalization of On-Line Learning and an Application to Boosting](https://doi.org/10.1006/jcss.1997.1504) 

Yoav Freund, Robert E. Schapire (1997)

Journal of Computer and System Sciences

📍 Original AdaBoost paper introducing the discrete boosting update used here.

 [Link ↗](https://doi.org/10.1006/jcss.1997.1504) [DOI ↗](https://doi.org/10.1006/jcss.1997.1504) [2]

 [The Dynamics of AdaBoost: Cyclic Behavior and Convergence of Margins](https://www.jmlr.org/papers/v5/rudin04a.html) 

Cynthia Rudin, Ingrid Daubechies, Robert E. Schapire (2004)

Journal of Machine Learning Research

📍 Introduces the dynamical-systems perspective on AdaBoost and studies cyclic behavior.

 [Link ↗](https://www.jmlr.org/papers/v5/rudin04a.html) [DOI ↗](https://doi.org/10.5555/1005332.1044712) [3]

 [Open Problem: Does AdaBoost Always Cycle?](https://proceedings.mlr.press/v23/rudin12/rudin12.pdf) 

Cynthia Rudin, Robert E. Schapire, Ingrid Daubechies (2012)

COLT 2012 Proceedings

📍 Short open-problem note explicitly posing the global cycling question.

 [Link ↗](https://proceedings.mlr.press/v23/rudin12/rudin12.pdf) [4]

 [On the Convergence Properties of Optimal AdaBoost](https://arxiv.org/abs/0803.4092) 

Anna Choromanska, John Langford (2012)

arXiv preprint

📍 Provides conditional convergence/ergodic-style results and evidence, not full closure.

 [Link ↗](https://arxiv.org/abs/0803.4092) [arXiv ↗](https://arxiv.org/abs/0803.4092) [5]

 [Limit Cycles of AdaBoost](https://arxiv.org/abs/2209.06928) 

Clint Scovel, Michael Cullen, Javier Beslin (2022)

arXiv preprint

📍 Analyzes explicit limit-cycle structure and continued-fractions correspondence for cycling dynamics.

 [Link ↗](https://arxiv.org/abs/2209.06928) [arXiv ↗](https://arxiv.org/abs/2209.06928)

## Notes / Progress

_Work log goes here._
