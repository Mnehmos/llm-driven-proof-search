# Regret Minimization in Heavy-Tailed Bandits with Unknown Distributional Parameters

**Status:** Unsolved  
**Source:** Posed by Gianmarco Genalti et al. (2025)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #90 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Stochastic heavy-tailed bandits with unknown tail parameters. Fix integers $K\ge 2$ and horizon $T\ge 1$ . For each arm $i\in\{1,\dots,K\}$ , pulling arm $i$ at time $t$ yields an independent reward $X_{i,t}\sim P_i$ with mean $\mu_i:=\mathbb{E}[X_{i,t}]$ (well-defined under the moment condition below). Let $i^*\in\arg\max_i \mu_i$ . For a (possibly randomized) policy $\pi$ selecting arms $I_t$ , define the expected cumulative regret

$
R_T(\pi;P_1,\dots,P_K):=\mathbb{E}\Big[\sum_{t=1}^T (\mu_{i^*}-\mu_{I_t})\Big],
$

where the expectation is over rewards and the internal randomness of $\pi$ .

Assume heavy-tailed rewards in the sense that there exist unknown parameters $\epsilon\in(0,1]$ and $u\in(0,\infty)$ such that, for every arm $i$ and every $t$ ,

$
\mathbb{E}[|X_{i,t}|^{1+\epsilon}]\le u.
$

The learner is not given $\epsilon$ or $u$ , and no further assumptions on the $P_i$ are imposed.

### Unsolved Problem

Open question 1 (minimax, parameter-free): Determine tight (up to constants and polylog factors, if appropriate) upper and lower bounds on

$
\inf_{\pi\ \text{independent of }(\epsilon,u)}\ \sup_{\epsilon\in(0,1],\ u>0}\ \sup_{(P_1,\dots,P_K):\ \forall i\ \mathbb{E}|X_i|^{1+\epsilon}\le u}\ R_T(\pi;P_1,\dots,P_K),
$

as a function of $(K,T)$ . Equivalently, characterize the best attainable regret when algorithms must be agnostic to the unknown moment order $\epsilon$ and moment bound $u$ .

Open question 2 (assumptions enabling adaptation): Identify and compare additional distributional assumptions under which a single parameter-free algorithm can (nearly) match the best-known regret rates achievable when $(\epsilon,u)$ are known, and clarify which such assumptions are genuinely weaker/stronger (or incomparable).

## Significance & Implications

Known-parameter heavy-tailed bandit algorithms tune robust mean estimators and confidence radii using $\epsilon$ and/or $u$ , so removing access to these quantities directly challenges how exploration bonuses are calibrated. This problem asks for the sharp information-theoretic price (in minimax regret) of not knowing the tail parameters under only a finite- $(1+\epsilon)$ -moment condition, and for a principled delineation of what extra structural assumptions are sufficient to restore near-known-parameter regret guarantees.

## Known Partial Results

- In the heavy-tailed bandit model with a uniform finite $(1+\epsilon)$ moment bound, robust mean-estimation techniques (e.g., truncation or median-of-means ideas) yield regret guarantees whose rates depend explicitly on $\epsilon$ and the moment bound $u$ .

- Existing approaches in this setting typically require knowing $\epsilon$ and/or $u$ to set estimator truncation/robustness levels and corresponding confidence widths.

- It is known that, without additional assumptions, one cannot generally adapt to either $\epsilon$ or $u$ without (i) paying extra regret relative to the known-parameter guarantees or (ii) imposing further distributional conditions; determining the best achievable regret with no extra assumptions remains open.

- The literature proposes multiple non-equivalent distributional assumptions that can enable parameter-free guarantees, and these assumptions are not ordered by implication in general (i.e., none is strictly weaker than all others).

## References

[1]

 [Open Problem: Regret Minimization in Heavy-Tailed Bandits with Unknown Distributional Parameters](https://proceedings.mlr.press/v291/genalti25a.html) 

Gianmarco Genalti, Alberto Maria Metelli (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v291/genalti25a.html) [2]

 [Open Problem: Regret Minimization in Heavy-Tailed Bandits with Unknown Distributional Parameters (PDF)](https://raw.githubusercontent.com/mlresearch/v291/main/assets/genalti25a/genalti25a.pdf) 

Gianmarco Genalti, Alberto Maria Metelli (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Proceedings PDF.

 [Link ↗](https://raw.githubusercontent.com/mlresearch/v291/main/assets/genalti25a/genalti25a.pdf)

## Notes / Progress

_Work log goes here._
