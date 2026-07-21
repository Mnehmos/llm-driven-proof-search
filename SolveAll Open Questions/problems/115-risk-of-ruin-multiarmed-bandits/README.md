# Risk of Ruin in Multiarmed Bandits

**Status:** Unsolved  
**Source:** Posed by Filipo S. Perotto et al. (2019)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #115 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Define a stochastic $K$ -armed bandit with arms $i\in\{1,\dots,K\}$ . Pulling arm $i$ at round $t$ yields a reward $X_{i,t}\sim \nu_i$ , where $\nu_i$ is an unknown distribution on $\mathbb{R}$ ; rewards may be positive or negative. A (non-anticipating) policy selects an arm $A_t$ each round based on past actions and observed rewards. The agent maintains a budget process $(B_t)_{t=0}^T$ with initial budget $B_0=b_0>0$ and update

$
B_t = B_{t-1} + X_{A_t,t}\quad (t\ge 1).
$

For a finite horizon $T$ , define the (path-dependent) ruin event

$
\mathsf{R}_T := \{\exists t\in\{1,\dots,T\}:\; B_t<0\},
$

and denote its probability under the policy and instance $(\nu_1,\dots,\nu_K)$ by $\mathbb{P}(\mathsf{R}_T)$ . A survival multiarmed bandit (S-MAB) problem asks to learn an exploration/exploitation strategy while controlling ruin risk: the objective is inherently multi-criteria, trading off reward (e.g., expected cumulative reward $\mathbb{E}[\sum_{t=1}^T X_{A_t,t}]$ ) against safety as quantified by $\mathbb{P}(\mathsf{R}_T)$ .

### Unsolved Problem

(a) Regret definition. Provide a formal regret notion for S-MAB that captures the reward--survival trade-off, including (i) a comparator class (e.g., policies that satisfy a specified ruin-risk target) and (ii) a loss/objective (e.g., constrained reward shortfall, Lagrangian trade-off, or Pareto regret) that is compatible with the path-dependent event $\mathsf{R}_T$ . (b) Reductions. Determine whether, and under what conditions, an S-MAB can be reduced to a risk-averse MAB (RA-MAB) or a budgeted MAB (B-MAB) formulation so that existing theoretical guarantees transfer, without losing the essential feature that safety is a hitting-probability constraint/event for $(B_t)$ . (c) Optimal strategy and guarantees. Characterize strategies that are optimal for the chosen regret/trade-off criterion in (a), and establish instance-dependent and/or worst-case performance guarantees that jointly address learning (exploration) and control of $\mathbb{P}(\mathsf{R}_T)$ .

## Significance & Implications

S-MAB makes safety a first-class, path-dependent criterion: a single unfavorable sequence of observed rewards can trigger irreversible failure via the hitting event $\mathsf{R}_T$ . This differs from objectives based only on expectations or terminal/budget constraints because controlling $\mathbb{P}(\mathsf{R}_T)$ depends on the entire trajectory of $(B_t)$ and interacts directly with exploration. A precise regret/trade-off formalism and matching algorithms would clarify what guarantees are achievable (and when) for sequential learning problems where exploration can itself create catastrophic risk.

## Known Partial Results

- Perotto, Bourgais, Silva, and Vercouter (2019) introduce and formalize survival multiarmed bandits (S-MAB), where an evolving budget with both positive and negative rewards is coupled to an explicit ruin event defined by hitting a negative budget.

- The note motivates S-MAB as distinct from (and potentially related to) budgeted MAB and risk-averse MAB formulations because the safety objective is the probability of a path-dependent ruin event.

- The source explicitly identifies three open directions: (a) defining an appropriate regret notion for the multiobjective reward/survival setting, (b) establishing reductions to RA-MAB or B-MAB that would transfer known guarantees, and (c) developing strategies and analytical tools tailored to controlling $\mathbb{P}(\mathsf{R}_T)$ while learning.

## References

[1]

 [Open Problem: Risk of Ruin in Multiarmed Bandits](https://proceedings.mlr.press/v99/perotto19a.html) 

Filipo S. Perotto, Mathieu Bourgais, Bruno C. Silva, Laurent Vercouter (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v99/perotto19a.html) [2]

 [Open Problem: Risk of Ruin in Multiarmed Bandits (PDF)](http://proceedings.mlr.press/v99/perotto19a/perotto19a.pdf) 

Filipo S. Perotto, Mathieu Bourgais, Bruno C. Silva, Laurent Vercouter (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v99/perotto19a/perotto19a.pdf)

## Notes / Progress

_Work log goes here._
