# Optimal Rates for Stochastic Decision-Theoretic Online Learning Under Differentially Privacy

**Status:** Partially Resolved  
**Source:** Posed by Bingshan Hu et al. (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #96 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Stochastic decision-theoretic online learning (full information) with privacy. Fix an integer $K\ge 2$ and horizon $T\ge 1$ . On each round $t=1,\dots,T$ , the learner outputs an action $I_t\in[K]:=\{1,\dots,K\}$ (possibly randomized). Then a loss vector $\ell_t=(\ell_{1,t},\dots,\ell_{K,t})\in[0,1]^K$ is realized and fully revealed to the learner. For each action $j\in[K]$ , the losses $(\ell_{j,t})_{t=1}^T$ are i.i.d. draws from an unknown distribution $P_j$ on $[0,1]$ , and the draws are independent across actions and rounds. Let $\mu_j:=\mathbb E[\ell_{j,1}]$ , assume the optimal action is unique with $j^*:=\arg\min_{j\in[K]}\mu_j$ , define gaps $\Delta_j:=\mu_j-\mu_{j^*}$ and $\Delta_{\min}:=\min_{j\ne j^*}\Delta_j>0$ . The (expected) pseudo-regret is

$
\mathrm{Reg}_T:=\mathbb E\Big[\sum_{t=1}^T \ell_{I_t,t}\Big]-\min_{j\in[K]}\mathbb E\Big[\sum_{t=1}^T \ell_{j,t}\Big]
=\mathbb E\Big[\sum_{t=1}^T (\mu_{I_t}-\mu_{j^*})\Big]=\sum_{j\ne j^*}\Delta_j\,\mathbb E[N_j(T)],
$

where $N_j(T):=|\{t\le T: I_t=j\}|$ and the expectation is over both the losses and the learner's randomness. An online algorithm $M$ is $\varepsilon$ -differentially private in the prefix (online) sense if for every $t\le T$ , for every pair of loss prefixes $(\ell_1,\dots,\ell_t)$ and $(\ell_1',\dots,\ell_t')$ that differ in at most one round, and for every measurable set $D\subseteq[K]^t$ of action prefixes,

$
\Pr\big((I_1,\dots,I_t)\in D\mid \ell_1,\dots,\ell_t\big)\le e^{\varepsilon}\,\Pr\big((I_1,\dots,I_t)\in D\mid \ell_1',\dots,\ell_t'\big).
$

In the non-private case ( $\varepsilon=\infty$ ), the optimal gap-dependent rate is $\mathrm{Reg}_T=\Theta\big((\log K)/\Delta_{\min}\big)$ (up to constants) in this stochastic full-information model.

### Unsolved Problem

Characterize, as a function of $(K,T,\Delta_{\min},\varepsilon)$ , the optimal achievable gap-dependent pseudo-regret among all $\varepsilon$ -DP algorithms: give matching (up to universal constants and at most logarithmic factors) upper and lower bounds on

$
\inf_{M\ \varepsilon\text{-DP}}\ \sup_{\text{instances with given }(K,T,\Delta_{\min})}\ \mathrm{Reg}_T(M).
$

## Significance & Implications

This problem asks for the sharp privacy-utility tradeoff in one of the cleanest stochastic online learning settings where full loss vectors are observed. Without privacy, the gap-dependent rate essentially does not grow with $T$ once $\Delta_{\min}>0$ (only logarithmically in $K$ ), so any unavoidable privacy penalty can be isolated and quantified. A precise characterization would (i) identify the correct dependence on $\varepsilon$ and how it interacts with $\Delta_{\min}$ (e.g., whether there are distinct regimes $\Delta_{\min}\ll\varepsilon$ vs. $\Delta_{\min}\gg\varepsilon$ ), and (ii) determine whether extra factors sometimes seen in private analyses (such as $\log T$ terms from repeated private selection/leader updates) are information-theoretically necessary or merely artifacts of existing algorithmic templates. The answer would directly inform the design of instance-optimal private learners in full-information environments and provide a baseline for more complex private online decision problems.

## Known Partial Results

- Non-private baseline: in the stochastic full-information model described above, the optimal gap-dependent pseudo-regret rate is $O\big((\log K)/\Delta_{\min}\big)$ , and this dependence on $(K,\Delta_{\min})$ is known to be unimprovable up to constants.

- Privacy notion: the open problem uses an online (prefix) $\varepsilon$ -DP guarantee that must hold for the distribution of the entire action prefix $(I_1,\dots,I_t)$ at every time $t$ , under a single-round change in the observed loss sequence.

- Existing private bounds (as summarized in the COLT 2024 open-problem entry): known $\varepsilon$ -DP algorithms achieve worst-case (gap-independent) pseudo-regret bounds that add an explicit privacy-dependent term scaling on the order of $(\log K\,\log T)/\varepsilon$ (up to constants and other problem-dependent factors).

- Existing private gap-dependent analyses (as summarized in the COLT 2024 open-problem entry): refined gap-dependent upper bounds are known for private leader/selection-style methods, but in the worst case these can still include privacy penalties comparable to $(\log K\,\log T)/\varepsilon$ even when $\Delta_{\min}>0$ .

- Existing lower bound (as summarized in the COLT 2024 open-problem entry): there is a gap-dependent lower bound of the form $\Omega\big((\log K)/\min\{\Delta_{\min},\varepsilon\}\big)$ , suggesting that privacy can force regret to scale at least like $(\log K)/\varepsilon$ when $\varepsilon\ll\Delta_{\min}$ .

- Wu and Wang (arXiv 2502.10997, revised June 18, 2025) improve the upper bound to $O\big((\log K)/\Delta_{\min} + \log^2 K / \varepsilon\big)$ , removing the $\log T$ factor, and prove matching $\Theta((\log K)/\varepsilon)$ bounds in a deterministic special case.

- The full stochastic minimax gap between $\log^2 K/\varepsilon$ and $(\log K)/\varepsilon$ remains open.

## References

[1]

 [Open Problem: Optimal Rates for Stochastic Decision-Theoretic Online Learning Under Differentially Privacy](https://proceedings.mlr.press/v247/hu24a.html) 

Bingshan Hu, Nishant A. Mehta (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/hu24a.html) [2]

 [Open Problem: Optimal Rates for Stochastic Decision-Theoretic Online Learning Under Differentially Privacy (PDF)](https://proceedings.mlr.press/v247/hu24a/hu24a.pdf) 

Bingshan Hu, Nishant A. Mehta (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/hu24a/hu24a.pdf)

## Notes / Progress

_Work log goes here._
