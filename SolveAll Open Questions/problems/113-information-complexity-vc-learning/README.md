# Information Complexity of VC Learning

**Status:** Partially Resolved  
**Source:** Posed by Thomas Steinke et al. (2020)

## Categories

- Learning Theory
- Mathematical Statistics
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #113 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal{X}$ be a domain and $\mathcal{H}\subseteq\{0,1\}^{\mathcal{X}}$ a binary hypothesis class with VC dimension $d:=\mathrm{VCdim}(\mathcal{H})<\infty$ . For a distribution $\mathcal{D}$ over $\mathcal{X}\times\{0,1\}$ and classifier $f\in\{0,1\}^{\mathcal{X}}$ , define the (0-1) risk $L_{\mathcal{D}}(f):=\Pr_{(x,y)\sim\mathcal{D}}[f(x)\neq y]$ .

A (possibly randomized, possibly improper) learner is a mapping $A$ that, on an i.i.d. sample $S=((x_1,y_1),\dots,(x_n,y_n))\sim\mathcal{D}^n$ , outputs a classifier $A(S)\in\{0,1\}^{\mathcal{X}}$ .

Define the conditional mutual information (CMI) of $A$ at sample size $n$ on $\mathcal{D}$ via the following experiment. Draw a supersample $\tilde S=((Z_{i,0},Z_{i,1}))_{i=1}^n\sim\mathcal{D}^{2n}$ (so each $Z_{i,j}\in\mathcal{X}\times\{0,1\}$ ). Draw independent selector bits $U=(U_1,\dots,U_n)$ with $U_i\sim\mathrm{Bernoulli}(1/2)$ , form the training sample $S=(Z_{1,U_1},\dots,Z_{n,U_n})$ , run the learner on $S$ , and set

$
\mathrm{CMI}_{\mathcal{D}}(A,n):= I(A(S);\,U\mid\tilde S),
$

where $I(\cdot;\cdot\mid\cdot)$ is conditional mutual information over the randomness of $\tilde S$ , $U$ , and the internal randomness of $A$ .

It is known from classical VC theory that there exist learners achieving distribution-free excess-risk bounds of the form

$
L_{\mathcal{D}}(A(S)) \le \inf_{h\in\mathcal{H}} L_{\mathcal{D}}(h) + O\!\left(\sqrt{\frac{d\log(n/d)+\log(1/\delta)}{n}}\right)
$

with probability at least $1-\delta$ (up to universal constants).

### Unsolved Problem

For every VC class $\mathcal{H}$ with $\mathrm{VCdim}(\mathcal{H})=d$ , do there exist learners $A$ that simultaneously (i) achieve the standard VC-type distribution-free excess-risk guarantee above for all distributions $\mathcal{D}$ and all $n$ , and (ii) have low information complexity as measured by CMI, e.g., $\sup_{\mathcal{D}}\mathrm{CMI}_{\mathcal{D}}(A,n)$ bounded by a function as small as possible in terms of $d$ (and $n$ )? More generally, determine tight (asymptotically best-possible) upper and lower bounds, as functions of $(d,n)$ , on

$
\inf_{A\ \text{s.t. VC-type excess-risk holds}}\ \sup_{\mathcal{D}}\ \mathrm{CMI}_{\mathcal{D}}(A,n).
$

## Significance & Implications

VC dimension characterizes learnability via distribution-free generalization/excess-risk rates, while information-based analyses aim to quantify how much a learner's output depends on its sample. This problem asks whether one can always realize the classical VC rates using learners whose dependence on the sample is small in the precise CMI sense, and to pin down the minimal worst-case CMI needed (as a function of $d$ and $n$ ) among algorithms that achieve VC-optimal learning guarantees.

## Known Partial Results

- Classical VC theory gives distribution-free excess-risk rates for VC classes, on the order of $\sqrt{(d\log(n/d)+\log(1/\delta))/n}$ up to constants.

- The open-problem note states that if one restricts to proper and consistent learners and measures information complexity using standard mutual information (MI), then one cannot in general obtain the desired low-information guarantees (citing Bassily et al., 2018).

- Conditional mutual information (CMI), as defined via a supersample and selector bits $U$ , was introduced by Steinke and Zakynthinou (2020) as an alternative information measure for learning algorithms, motivated by its connection to generalization.

- The COLT 2020 open problem asks for (i) existence of VC-rate learners with small CMI for every VC class, and (ii) tight upper/lower bounds on the minimal achievable worst-case CMI in terms of $d$ (and possibly $n$ ) under VC-type excess-risk requirements.

- Subsequent work negatively resolves some proper-learning small-CMI conjectures and gives realizable-setting progress via leave-one-out CMI, but the full minimax CMI characterization for VC learning remains open.

## References

[1]

 [Open Problem: Information Complexity of VC Learning](https://proceedings.mlr.press/v125/steinke20b.html) 

Thomas Steinke, Lydia Zakynthinou (2020)

Conference on Learning Theory (COLT), PMLR 125

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v125/steinke20b.html) [2]

 [Open Problem: Information Complexity of VC Learning (PDF)](http://proceedings.mlr.press/v125/steinke20b/steinke20b.pdf) 

Thomas Steinke, Lydia Zakynthinou (2020)

Conference on Learning Theory (COLT), PMLR 125

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v125/steinke20b/steinke20b.pdf)

## Notes / Progress

_Work log goes here._
