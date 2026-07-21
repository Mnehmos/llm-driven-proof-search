# Decision-Optimal Prediction Sets with Group/Label-Conditional Guarantees

**Status:** Unsolved  
**Importance:** Major
**Source:** Posed by Wang and Dobriban (2026)

## Categories

- Mathematical Statistics
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #5 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal X$ be a feature space, $\mathcal Y$ an outcome space, and $\mathcal A$ an action space, with loss $\ell:\mathcal A\times\mathcal Y\to[0,\infty)$ . A prediction set is a map $C:\mathcal X\to 2^{\mathcal Y}$ . For a fixed miscoverage level $\alpha\in(0,1)$ , define the robust in-set decision loss for action $a$ and set $S\subseteq\mathcal Y$ :

$
L_S(a;\alpha):=\sup_{Q:\,Q(S)\ge 1-\alpha}\mathbb E_{Y\sim Q}[\ell(a,Y)].
$

The source paper derives

$
L_S(a;\alpha)=\ell_S^{\mathrm{in}}(a)+\alpha\big(\ell_S^{\mathrm{out}}(a)-\ell_S^{\mathrm{in}}(a)\big)_+,
$

where $\ell_S^{\mathrm{in}}(a):=\sup_{y\in S}\ell(a,y)$ and $\ell_S^{\mathrm{out}}(a):=\sup_{y\notin S}\ell(a,y)$ , and studies robust action selection

$
a_C(x)\in\arg\min_{a\in\mathcal A}L_{C(x)}(a;\alpha).
$

It also proposes a conformal construction (ROCP) with finite-sample marginal coverage under exchangeability.

### Unsolved Problem

Construct and analyze decision-optimal conformal procedures that preserve the robust decision-theoretic objective while enforcing stronger subgroup guarantees, such as group-conditional, label-conditional, or localized coverage constraints. For example, given a class of groups $\mathcal G\subseteq 2^{\mathcal X}$ and possibly label subsets $\mathcal H\subseteq 2^{\mathcal Y}$ , achieve finite-sample guarantees of the form

$
\Pr\{Y\in C(X)\mid X\in g\}\ge 1-\alpha_g\quad(\forall g\in\mathcal G),
$

and/or

$
\Pr\{Y\in C(X)\mid Y\in h\}\ge 1-\tilde\alpha_h\quad(\forall h\in\mathcal H),
$

while minimizing decision risk criteria induced by $L_{C(X)}(a;\cdot)$ (or their empirical counterparts) with explicit sample-complexity and computational guarantees.

## Significance & Implications

This problem links distribution-free uncertainty quantification to downstream decision quality on heterogeneous subpopulations. A solution would make conformal decision rules more reliable in safety-critical settings where aggregate marginal validity is insufficient.

## Known Partial Results

- [Wang & Dobriban (2026)](#references) : derives robust action formulas from prediction sets and proposes ROCP with finite-sample marginal coverage under exchangeability.

- The same source explicitly identifies subgroup-conditional extensions (group, label, localized) as future work in its Discussion section.

- Conditional-coverage impossibility results imply that any full solution must carefully specify feasible structural assumptions and target classes.

## References

[1]

 [Optimal Decision-Making Based on Prediction Sets](https://arxiv.org/abs/2602.00989) 

Tianrui Wang, Edgar Dobriban (2026)

arXiv preprint

📍 Section 2 (setting and robust loss formulation), Section 5 (ROCP construction), and Section 7 (Discussion: extension to group-conditional/label-conditional/localized guarantees).

 [arXiv ↗](https://arxiv.org/abs/2602.00989) [2]

 [The limits of distribution-free conditional predictive inference](https://doi.org/10.1093/imaiai/iaaa017) 

Rina Foygel Barber, Emmanuel Candès, Aaditya Ramdas, Ryan Tibshirani (2021)

Information and Inference

📍 Impossibility frontiers for exact distribution-free conditional guarantees; motivation for structured or approximate conditional goals.

 [DOI ↗](https://doi.org/10.1093/imaiai/iaaa017) [arXiv ↗](https://arxiv.org/abs/1903.04684) [3]

 [Algorithmic Learning in a Random World](https://doi.org/10.1007/b106715) 

Vladimir Vovk, Alexander Gammerman, Glenn Shafer (2005)

Springer

📍 Foundational conformal prediction framework for finite-sample marginal validity.

 [DOI ↗](https://doi.org/10.1007/b106715)

## Notes / Progress

_Work log goes here._
