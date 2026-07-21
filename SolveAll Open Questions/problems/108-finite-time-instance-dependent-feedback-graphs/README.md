# Finite-Time Instance Dependent Optimality for Stochastic Online Learning with Feedback Graphs

**Status:** Unsolved  
**Source:** Posed by Teodor Vanislavov Marinov et al. (2022)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #108 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider stochastic online learning with a known directed feedback graph $G=([K],E)$ on $K\ge 2$ actions, where every node has a self-loop $(i,i)\in E$ . At each round $t=1,\dots,T$ , the environment draws a loss vector $X_t=(X_{t,1},\dots,X_{t,K})\in[0,1]^K$ i.i.d. from an unknown distribution $\nu$ . The learner selects an action $I_t\in[K]$ , suffers loss $X_{t,I_t}$ , and observes the losses $\{X_{t,j}: j\in\mathcal O(I_t)\}$ where $\mathcal O(i)=\{j\in[K]:(i,j)\in E\}$ is the out-neighborhood.

Let $\mu_i=\mathbb E_{\nu}[X_{t,i}]$ and assume there is a unique optimal action $i^*\in\arg\min_i \mu_i$ . Define gaps $\Delta_i=\mu_i-\mu_{i^*}\ge 0$ , and for an algorithm (policy) $\pi$ define expected regret

$
R_T(\pi;\nu,G)=\mathbb E\Big[\sum_{t=1}^T (X_{t,I_t}-X_{t,i^*})\Big]=\sum_{i\ne i^*} \Delta_i\,\mathbb E[N_i(T)],
$

where $N_i(T)=\sum_{t=1}^T \mathbf 1\{I_t=i\}$ . Define the instance-wise finite-horizon optimum

$
R_T^*(\nu,G)=\inf_{\pi} R_T(\pi;\nu,G).
$

It is known that (under standard stochastic assumptions) there are instance-dependent algorithms whose regret matches the leading $\log T$ term in known information-theoretic lower bounds for feedback graphs as $T\to\infty$ .

### Unsolved Problem

- 

Finite-time characterization: Characterize $R_T^*(\nu,G)$ (or, if one restricts to a natural class of "globally reasonable" algorithms, the corresponding restricted infimum) for finite $T$ in terms of (i) the instance $\nu$ (e.g., gaps $\{\Delta_i\}$ and distributional distinguishability quantities such as KL divergences between arm-loss distributions) and (ii) the graph structure $G$ .

- 

When does the asymptotic rate control finite time?: Characterize the class of graphs $G$ for which, for every instance $\nu$ and for horizons $T$ in a non-asymptotic ("moderate") regime, the finite-time optimum is already controlled (up to lower-order terms) by the asymptotically optimal instance-dependent $\log T$ benchmark from existing lower bounds; and characterize graphs for which some instances and horizons necessarily exhibit a finite-time separation from that asymptotic $\log T$ benchmark.

## Significance & Implications

Feedback graphs formalize structured side-observations, interpolating between bandit feedback (only the played action observed) and full information (all actions observed). For feedback graphs, asymptotic instance-dependent theory identifies the leading $\log T$ growth rate dictated by information-theoretic lower bounds, but the COLT 2022 open-problem note highlights that this asymptotic benchmark does not uniquely pin down what "optimal" means at a fixed horizon and can be decoupled from finite-time optimality. A finite-time, instance-and-graph-specific characterization would clarify the correct performance target at horizon $T$ , determine when asymptotically optimal algorithms are already near-optimal at realistic sample sizes, and isolate graph structures that intrinsically force additional exploration cost beyond the asymptotic leading term.

## Known Partial Results

- In the classical stochastic multi-armed bandit setting (no side-observations beyond the played arm), both asymptotic and non-asymptotic instance-dependent regret bounds are available; for Gaussian rewards, bounds matching the instance-dependent lower bounds are known up to lower-order terms (as cited in the COLT 2022 open-problem abstract).

- For stochastic online learning with feedback graphs, instance-dependent algorithms are known that are asymptotically optimal in the sense of matching the leading $\log T$ term in known information-theoretic lower bounds for this model (as stated in the COLT 2022 open-problem abstract).

- The COLT 2022 open-problem note reports that, unlike in standard bandits, finite-time instance-dependent optimality is not uniquely determined by the asymptotic theory for feedback graphs and can be decoupled from the asymptotic rate, motivating a dedicated finite-time characterization.

- The COLT 2022 open-problem note poses two concrete directions: (i) characterize the finite-horizon instance-dependent optimal regret in this model, and (ii) determine which graphs do (and do not) admit finite-time regret controlled by the asymptotically optimal instance-dependent $\log T$ benchmark for reasonable horizons.

## References

[1]

 [Open Problem: Finite-Time Instance Dependent Optimality for Stochastic Online Learning with Feedback Graphs](https://proceedings.mlr.press/v178/open-problem-marinov22a.html) 

Teodor Vanislavov Marinov, Mehryar Mohri, Julian Zimmert (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-marinov22a.html) [2]

 [Open Problem: Finite-Time Instance Dependent Optimality for Stochastic Online Learning with Feedback Graphs (PDF)](https://proceedings.mlr.press/v178/open-problem-marinov22a/open-problem-marinov22a.pdf) 

Teodor Vanislavov Marinov, Mehryar Mohri, Julian Zimmert (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-marinov22a/open-problem-marinov22a.pdf)

## Notes / Progress

_Work log goes here._
