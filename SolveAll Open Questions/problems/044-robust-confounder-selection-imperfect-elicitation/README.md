# Robust Confounder Selection Under Imperfect Primary-Set Elicitation

**Status:** Unsolved  
**Source:** Sourced from the work of F. Richard Guo, Qingyuan Zhao

## Categories

- Information Theory
- Combinatorics & Graph Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #44 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix two distinct observed variables $X$ (treatment) and $Y$ (outcome). Let $\tilde G$ be a causal directed acyclic graph on vertex set $V\cup U$ , where $V$ are observed variables (including $X,Y$ ) and $U$ are latent (unobserved) variables. For any observational distribution $P$ that is Markov and faithful to $\tilde G$ and satisfies positivity, call a set $S\subseteq V\setminus\{X,Y\}$ a valid covariate-adjustment set for the total causal effect of $X$ on $Y$ if the adjustment formula

$
P(y\mid do(x))=\sum_{s} P(y\mid x,s)P(s)
$

holds for all $x,y$ (with integral form for continuous $S$ ) for every such $P$ . Let

$
\mathcal A(X,Y;\tilde G):=\{S\subseteq V\setminus\{X,Y\}: S \text{ is a valid adjustment set}\}.
$

Consider an interactive algorithm that can ask at most $B$ queries. At round $t$ , there is a target set $P_t^\star$ (the exact primary set that would be provided in the noiseless/oracle procedure), but the algorithm receives a noisy response $\widehat P_t$ . Let $H_{t-1}$ be the full interaction history before round $t$ . Two noise models of interest are: (i) mis-elicitation probability bound $\Pr(\widehat P_t\neq P_t^\star\mid H_{t-1})\le \varepsilon$ for all $t$ ; (ii) bounded set-error model with metric $d(A,B):=|A\triangle B|$ and either deterministic bound $d(\widehat P_t,P_t^\star)\le \delta$ or high-probability bound $\Pr(d(\widehat P_t,P_t^\star)>\delta\mid H_{t-1})\le \varepsilon$ .

### Unsolved Problem

Characterize whether there exists an interactive procedure $\Pi$ (possibly randomized), using at most $B$ noisy queries, that outputs either a set $S\subseteq V\setminus\{X,Y\}$ or a failure symbol $\bot$ , and satisfies a uniform correctness guarantee

$
\Pr\Big(\big[\Pi \text{ outputs some } S\in\mathcal A(X,Y;\tilde G)\big]\iff\big[\mathcal A(X,Y;\tilde G)\neq\varnothing\big]\Big)\ge 1-\eta
$

for every causal graph $\tilde G$ and every noise process obeying the chosen $(\varepsilon,\delta)$ constraints. In particular, determine necessary and sufficient conditions, and explicit quantitative bounds, relating $(\varepsilon,\delta,\eta,B)$ under which such robust soundness-and-completeness is achievable.

## Significance & Implications

The paper's proved guarantee is in an ideal-oracle setting with perfectly correct primary-set input at each step. A noisy-elicitation robustness theory is a natural downstream extension for practical deployment, but should be treated as extrapolative framing unless broader literature verification is completed. See [Guo & Zhao (2023)](#references) for the oracle formulation.

## Known Partial Results

Guo and Zhao establish soundness/completeness in the ideal-oracle setting where primary adjustment sets are correctly specified at each iteration. A full theory for bounded/noisy elicitation appears not established in this source and is framed here as an extension.

## References

[1]

 [Confounder Selection via Iterative Graph Expansion](https://arxiv.org/abs/2309.06053) 

F. Richard Guo, Qingyuan Zhao (2023)

Annals of Statistics (to appear)

📍 Abstract (arXiv PDF): guarantee is stated for the case where the user correctly specifies the primary adjustment sets at each step.

Primary source for the oracle interactive method and its soundness/completeness guarantees; the noisy-elicitation robustness formulation here is a downstream proposed extension rather than a directly stated theorem/problem in the paper.

 [Link ↗](https://arxiv.org/abs/2309.06053) [arXiv ↗](https://arxiv.org/abs/2309.06053)

## Notes / Progress

_Work log goes here._
