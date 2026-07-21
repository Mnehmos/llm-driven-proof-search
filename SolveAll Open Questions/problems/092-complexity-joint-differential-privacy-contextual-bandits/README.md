# What is the Complexity of Joint Differential Privacy in Linear Contextual Bandits?

**Status:** Unsolved  
**Source:** Posed by Achraf Azize et al. (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #92 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $d,T,K \ge 1$ and privacy parameters $\epsilon>0$ , $\delta\in[0,1)$ . Consider a stochastic $K$ -armed linear contextual bandit over $T$ rounds with unknown parameter $\theta^*\in\mathbb{R}^d$ satisfying $\|\theta^*\|_2\le 1$ . In each round $t\in\{1,\dots,T\}$ , the learner observes context vectors $x_{t,1},\dots,x_{t,K}\in\mathbb{R}^d$ with $\|x_{t,a}\|_2\le 1$ , selects an action $a_t\in\{1,\dots,K\}$ , and then receives reward

$
r_t=\langle x_{t,a_t},\theta^*\rangle+\eta_t,
$

where $\eta_t$ is mean-zero noise (e.g., conditionally sub-Gaussian) independent across rounds. The (pseudo-)regret is

$
\mathrm{Regret}(T)=\sum_{t=1}^T\Big(\max_{a\in[K]}\langle x_{t,a},\theta^*\rangle-\langle x_{t,a_t},\theta^*\rangle\Big).
$

Model each round as a "user" with data tuple $z_t=(x_{t,1:K},r_t)$ , and let the full dataset be $D=(z_1,\dots,z_T)$ . A randomized bandit algorithm induces a distribution over the entire action sequence $a_{1:T}=(a_1,\dots,a_T)$ . The algorithm is $(\epsilon,\delta)$ -jointly differentially private (JDP) if for every index $i\in[T]$ , for all neighboring datasets $D,D'$ that differ only in $z_i$ , and for every measurable set $S\subseteq [K]^{T-1}$ ,

$
\Pr[a_{-i}\in S\mid D] \le e^{\epsilon}\Pr[a_{-i}\in S\mid D']+\delta,
$

where $a_{-i}=(a_1,\dots,a_{i-1},a_{i+1},\dots,a_T)$ and the probability is over the algorithm's internal randomness (and any randomness in the interaction/noise model).

### Unsolved Problem

Determine, up to at most polylogarithmic factors, the minimax expected regret under JDP,

$
R^*_{\mathrm{JDP}}(d,T,K,\epsilon,\delta)=\inf_{\text{$(\epsilon,\delta)$-JDP alg.}}\ \sup_{\theta^*,\{x_{t,a}\},\text{noise}}\ \mathbb{E}[\mathrm{Regret}(T)],
$

including the correct dependence on $d,T,K,\epsilon,\delta$ . In particular, close the gap between the best reported upper bound

$
O\!\left(d\sqrt{T}\log T+\frac{d^{3/4}\sqrt{T\log(1/\delta)}}{\sqrt{\epsilon}}\right)
$

and the reported lower bound

$
\Omega\!\left(\sqrt{dT\log K}+\frac{d}{\epsilon+\delta}\right)
$

by improving algorithms, strengthening lower bounds, or both.

## Significance & Implications

Linear contextual bandits are a canonical model for sequential recommendation with user-specific (and potentially sensitive) feedback. Joint differential privacy is tailored to this setting: it requires that changing one user's data has limited effect on the recommendations made to all other users, while allowing the recommendation shown to the changed user to vary freely. A tight characterization of $R^*_{\mathrm{JDP}}(d,T,K,\epsilon,\delta)$ would quantify the unavoidable privacy cost beyond the nonprivate benchmark (typically scaling like $d\sqrt{T}$ up to logs), and would determine whether the privacy-dependent regret term must grow on the order of $\sqrt{T}/\sqrt{\epsilon}$ (as in current upper bounds) or can be substantially smaller in its $T$ -dependence (not ruled out by the stated lower bound).

## Known Partial Results

- The COLT 2024 open-problem note reports an $(\epsilon,\delta)$ -JDP regret upper bound of $O\!\left(d\sqrt{T}\log T+\frac{d^{3/4}\sqrt{T\log(1/\delta)}}{\sqrt{\epsilon}}\right)$ for linear contextual bandits.

- The same note reports a lower bound of $\Omega\!\left(\sqrt{dT\log K}+\frac{d}{\epsilon+\delta}\right)$ .

- Comparing these bounds leaves a gap in the privacy-dependent contribution: the upper bound includes a term scaling as $\frac{d^{3/4}\sqrt{T}}{\sqrt{\epsilon}}$ (up to logs in $T$ and $1/\delta$ ), whereas the stated privacy-dependent lower-bound term $\frac{d}{\epsilon+\delta}$ has no $\sqrt{T}$ factor.

- The note highlights two directions to resolve the gap: (i) design JDP algorithms with improved dependence on $(d,T,\epsilon,\delta)$ , and/or (ii) develop sharper lower-bound techniques specific to the JDP constraint in linear contextual bandits.

## References

[1]

 [Open Problem: What is the Complexity of Joint Differential Privacy in Linear Contextual Bandits?](https://proceedings.mlr.press/v247/azize24a.html) 

Achraf Azize, Debabrota Basu (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/azize24a.html) [2]

 [Open Problem: What is the Complexity of Joint Differential Privacy in Linear Contextual Bandits? (PDF)](https://proceedings.mlr.press/v247/azize24a/azize24a.pdf) 

Achraf Azize, Debabrota Basu (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/azize24a/azize24a.pdf)

## Notes / Progress

_Work log goes here._
