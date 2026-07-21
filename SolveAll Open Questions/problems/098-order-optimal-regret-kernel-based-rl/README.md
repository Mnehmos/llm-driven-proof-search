# Order Optimal Regret Bounds for Kernel-Based Reinforcement Learning

**Status:** Unsolved  
**Source:** Posed by Sattar Vakili (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #98 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider an episodic finite-horizon Markov decision process (MDP) with horizon $H$ , (possibly infinite) state space $\mathcal S$ , finite action space $\mathcal A$ , and unknown time-dependent reward and transition operators $r_h:\mathcal S\times\mathcal A\to[0,1]$ and $P_h(\cdot\mid s,a)$ for $h\in\{1,\dots,H\}$ . Let $\mathcal X=\mathcal S\times\mathcal A$ and let $k:\mathcal X\times\mathcal X\to\mathbb R$ be a positive semidefinite kernel with reproducing kernel Hilbert space (RKHS) $\mathcal H_k$ and norm $\|\cdot\|_{\mathcal H_k}$ . Assume the following kernel-based function approximation structure:

- 

(Rewards in RKHS) For each $h$ , $r_h\in\mathcal H_k$ and $\|r_h\|_{\mathcal H_k}\le B_r$ .

- 

(Kernelized transitions via test functions) Fix a normed function class $\mathcal G$ of bounded real-valued functions on $\mathcal S$ with norm $\|\cdot\|_{\mathcal G}$ . For each $h$ and each $f\in\mathcal G$ , define

$
(P_h f)(s,a):=\mathbb E[f(S_{h+1})\mid S_h=s, A_h=a].
$

Assume $P_h f\in\mathcal H_k$ for all $f\in\mathcal G$ , and there exists $B_p$ such that for all $h$ and all $f$ with $\|f\|_{\mathcal G}\le 1$ , one has $\|P_h f\|_{\mathcal H_k}\le B_p$ .

An agent interacts with the MDP for $T$ episodes. In episode $t$ , it chooses a (possibly history-dependent) policy $\pi_t$ and observes a trajectory $(S_{t,1},A_{t,1},R_{t,1},\dots,S_{t,H},A_{t,H},R_{t,H},S_{t,H+1})$ . Define the expected regret after $T$ episodes by

$
\mathrm{Regret}(T):=\sum_{t=1}^T \big( V_1^*(S_{t,1})-V_1^{\pi_t}(S_{t,1}) \big),
$

where $V_1^*$ is the optimal value function and $V_1^{\pi_t}$ is the value function of $\pi_t$ under the true MDP.

### Unsolved Problem

Characterize the minimax expected regret

$
\inf_{\text{algorithms}}\ \sup_{\text{MDPs satisfying (1)-(2)}}\ \mathbb E[\mathrm{Regret}(T)]
$

as a function of $T$ , $H$ , $B_r$ , $B_p$ , and a kernel complexity measure associated with $k$ over $\mathcal X$ (e.g., an effective dimension or an information-gain quantity). In particular, provide matching upper and lower bounds up to at most polylogarithmic factors, and determine whether the best known kernel-based RL upper bounds have the correct dependence on $T$ , $H$ , and the kernel complexity term (or improve either the upper bounds and/or the lower bounds to close any gap).

## Significance & Implications

This problem asks for sharp sample-efficiency limits for exploration and control when rewards and transition-related quantities admit RKHS structure on state-action pairs. A resolved minimax rate would identify which kernel complexity measure (and which dependence on horizon $H$ ) fundamentally governs achievable regret in multi-step decision making, beyond what is known for prediction or bandits, where uncertainty does not propagate through Bellman recursion. Such a characterization would also provide a clean nonparametric benchmark that strictly extends linear-structure MDP theory while remaining analyzable with RKHS tools.

## Known Partial Results

- For tabular episodic MDPs and for linear-structure MDP models, there are well-established minimax-style regret benchmarks (including explicit dependence on horizon and model dimension), which serve as reference points for what order-optimality should mean in simpler classes.

- For kernelized nonlinear prediction and contextual bandits, regret bounds commonly scale as $\tilde O(\sqrt{T\,\Gamma_T})$ for a kernel complexity term $\Gamma_T$ (often phrased via effective dimension or information gain), motivating the conjecture that an analogous complexity term should control kernel-based RL rates as well.

- Existing analyses for kernel-based RL under RKHS/kernelized-MDP assumptions achieve sublinear regret, but the best available bounds are not known to match lower bounds in their dependence on $H$ and/or the kernel complexity term.

- A central difficulty relative to bandits is error propagation through Bellman recursion: transition uncertainty affects multi-step value estimates, so confidence sets must control both function approximation error and its compounding across time steps.

- The COLT 2024 open-problem note frames closing the remaining upper/lower-bound gap (including the correct role of kernel complexity and horizon) as unresolved.

## References

[1]

 [Open Problem: Order Optimal Regret Bounds for Kernel-Based Reinforcement Learning](https://proceedings.mlr.press/v247/vakili24a.html) 

Sattar Vakili (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/vakili24a.html) [2]

 [Open Problem: Order Optimal Regret Bounds for Kernel-Based Reinforcement Learning (PDF)](https://proceedings.mlr.press/v247/vakili24a/vakili24a.pdf) 

Sattar Vakili (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/vakili24a/vakili24a.pdf)

## Notes / Progress

_Work log goes here._
