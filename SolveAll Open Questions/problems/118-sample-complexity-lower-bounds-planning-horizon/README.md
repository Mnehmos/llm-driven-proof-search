# The Dependence of Sample Complexity Lower Bounds on Planning Horizon

**Status:** Partially Resolved  
**Source:** Posed by Nan Jiang et al. (2018)

## Categories

- Learning Theory
- Mathematical Statistics
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #118 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $H\in\mathbb{N}$ . Consider episodic reinforcement learning in an unknown, finite-horizon Markov decision process (MDP) $M=(\mathcal{S},\mathcal{A},H,\{P_t\}_{t=1}^H,\{r_t\}_{t=1}^H,\rho)$ where $\rho$ is an initial-state distribution over $\mathcal{S}$ , each reward function satisfies $r_t(s,a)\in[0,1]$ , and $P_t(\cdot\mid s,a)$ is the stage- $t$ transition kernel. A (possibly nonstationary) policy is $\pi=(\pi_1,\ldots,\pi_H)$ , and its value is

$
V_M^\pi(\rho)=\mathbb{E}\Big[\sum_{t=1}^H r_t(S_t,A_t)\Big],
$

with $S_1\sim\rho$ , $A_t\sim\pi_t(\cdot\mid S_t)$ , and $S_{t+1}\sim P_t(\cdot\mid S_t,A_t)$ . An algorithm interacts with $M$ for $n$ episodes (observing the resulting trajectories) and outputs a policy $\hat\pi$ .

Fix $(\varepsilon,\delta)\in(0,1)\times(0,1)$ . For a class of MDPs $\mathcal{M}$ , define the episodic PAC sample complexity as the smallest $n$ for which there exists an algorithm such that for all $M\in\mathcal{M}$ ,

$
\Pr\big[V_M^{\pi^*}(\rho)-V_M^{\hat\pi}(\rho)\le \varepsilon\big]\ge 1-\delta,
$

where $\pi^*$ is an optimal policy for $M$ .

### Unsolved Problem

Identify a suitable, natural family of MDP classes $\{\mathcal{M}_H\}_{H\ge 1}$ and prove an information-theoretic lower bound on PAC sample complexity that has an unavoidable, nontrivial dependence on the planning horizon $H$ once strong technical assumptions used in recent horizon-light PAC-RL upper bounds are removed. Concretely, can one construct $\mathcal{M}_H$ so that, after controlling other measures of problem size/complexity so they do not grow rapidly with $H$ (e.g., keeping $|\mathcal{S}|,|\mathcal{A}|$ or an appropriate function-approximation complexity measure fixed or only mildly growing), every PAC algorithm still requires at least $n\ge f(H,\varepsilon,\delta)$ episodes with $f$ increasing in $H$ (e.g., polynomial or stronger), and such $H$ -dependence cannot be eliminated without reinstating those strong assumptions?

## Significance & Implications

Long-horizon RL is widely viewed as difficult due to delayed consequences and multi-step uncertainty, yet several modern PAC-RL results exhibit only weak ("superficial") horizon dependence under additional technical assumptions. A rigorous lower bound that forces increasing sample complexity with $H$ for assumption-light MDP classes would clarify whether these horizon-light guarantees rely on restrictive modeling choices, and would delineate when long-horizon learning is statistically harder even before computational considerations.

## Known Partial Results

- Jiang and Agarwal (COLT 2018) highlight a tension between the perceived difficulty of long planning horizons and recent PAC-RL upper bounds whose horizon dependence appears only superficial, and they pose the question of whether stronger $H$ -dependence emerges when key assumptions are removed.

- The note emphasizes that a meaningful horizon-dependent lower bound should not obtain $H$ -dependence merely by encoding longer horizons via larger state spaces; instead, the construction should isolate difficulty attributable to long-horizon interaction itself.

- The note sketches desired characteristics for hard instances, informally pointing to compounding multi-step uncertainty and delayed effects as mechanisms by which distinguishing near-optimal from suboptimal behavior could require more data as $H$ grows.

- Wang, Du, Yang, and Kakade (NeurIPS 2020) refute the conjectured polynomial horizon lower bound for tabular episodic PAC RL with normalized episode value, proving that logarithmic dependence on $H$ is achievable in that regime.

- Any remaining open version of the COLT 2018 question must therefore be scoped beyond this normalized tabular setting.

## References

[1]

 [Open Problem: The Dependence of Sample Complexity Lower Bounds on Planning Horizon](https://proceedings.mlr.press/v75/jiang18a.html) 

Nan Jiang, Alekh Agarwal (2018)

Conference on Learning Theory (COLT), PMLR 75

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v75/jiang18a.html) [2]

 [Open Problem: The Dependence of Sample Complexity Lower Bounds on Planning Horizon (PDF)](http://proceedings.mlr.press/v75/jiang18a/jiang18a.pdf) 

Nan Jiang, Alekh Agarwal (2018)

Conference on Learning Theory (COLT), PMLR 75

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v75/jiang18a/jiang18a.pdf)

## Notes / Progress

_Work log goes here._
