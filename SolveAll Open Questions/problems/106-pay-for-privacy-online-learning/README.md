# Do you pay for Privacy in Online learning?

**Status:** Partially Resolved  
**Source:** Posed by Amartya Sanyal et al. (2022)

## Categories

- Learning Theory
- Optimization & Variational Methods
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #106 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix an instance domain $\mathcal{X}$ and a binary hypothesis class $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ . In the realizable online (mistake-bound) model, an adversary chooses a length- $T$ labeled sequence $S=((x_1,y_1),\dots,(x_T,y_T))$ such that there exists $h^*\in\mathcal{H}$ with $y_t=h^*(x_t)$ for all $t\in[T]$ . An (interactive, possibly randomized) learner $\mathcal{A}$ operates for $t=1,\dots,T$ : it observes $x_t$ , outputs a prediction $\hat y_t\in\{0,1\}$ , then observes $y_t$ , incurring a mistake if $\hat y_t\neq y_t$ . Let the transcript (output) of $\mathcal{A}$ on $S$ be the full prediction sequence $\mathcal{A}(S)=(\hat y_1,\dots,\hat y_T)$ (a random variable over the learner's internal randomness).

Adjacency: Two labeled sequences $S,S'$ of the same length $T$ are adjacent if they differ in exactly one position, i.e., there exists a unique $t\in[T]$ with $(x_t,y_t)\neq (x'_t,y'_t)$ and $(x_s,y_s)=(x'_s,y'_s)$ for all $s\neq t$ .

Online differential privacy (transcript DP): $\mathcal{A}$ is $(\varepsilon,\delta)$ -differentially private if for all adjacent $S,S'$ and all measurable events $E$ over transcripts,

$
\Pr[\mathcal{A}(S)\in E] \le e^{\varepsilon}\Pr[\mathcal{A}(S')\in E] + \delta.
$

Mistake-bound learnability: $\mathcal{H}$ is (non-privately) learnable in the mistake-bound sense if there exists a finite $M(\mathcal{H})$ and an online algorithm $\mathcal{A}$ such that for every realizable sequence (any $T$ ), the expected number of mistakes of $\mathcal{A}$ is at most $M(\mathcal{H})$ .

Online-DP mistake-bound learnability: $\mathcal{H}$ is online-DP-learnable if for every $\varepsilon>0$ and $\delta\in[0,1)$ there exists an online algorithm $\mathcal{A}_{\varepsilon,\delta}$ that is $(\varepsilon,\delta)$ -DP (as above) and has a finite mistake bound $M_{\varepsilon,\delta}(\mathcal{H})$ on every realizable sequence (uniformly over $T$ ).

### Unsolved Problem

 **Problem 2022.** Is privacy for free in this setting? Concretely, is the set of hypothesis classes that admit a finite (non-private) mistake bound exactly the set that admit a finite $(\varepsilon,\delta)$ -DP mistake bound for all $\varepsilon>0,\delta\in[0,1)$ ? If the sets coincide, what (tight) quantitative relationship is unavoidable between the optimal non-private mistake bound $M(\mathcal{H})$ and the optimal private mistake bound $M_{\varepsilon,\delta}(\mathcal{H})$ as a function of $(\varepsilon,\delta)$ ?

## Significance & Implications

The mistake-bound model gives a sharp, distribution-free notion of online learnability (finite number of errors on every realizable adversarial sequence). Requiring $(\varepsilon,\delta)$ -differential privacy for the entire prediction transcript asks whether one can guarantee this form of sequential learnability while limiting how much any single labeled example can influence the released sequence of predictions. An equivalence would yield a structural characterization: every realizably learnable class would remain learnable under transcript-level DP (possibly with an explicit dependence of $M_{\varepsilon,\delta}(\mathcal{H})$ on $(\varepsilon,\delta)$ ). A separation would exhibit an intrinsic privacy cost in online prediction by identifying a class with a finite non-private mistake bound but no finite DP mistake bound (for some fixed privacy parameters), pinpointing a concrete barrier for private sequential learning.

## Known Partial Results

- Sanyal and Ramponi (COLT 2022) explicitly pose the question of whether realizable mistake-bound online learnability coincides with online transcript-level $(\varepsilon,\delta)$ -differentially private learnability.

- Their open-problem note formulates the privacy requirement as differential privacy of the full prediction transcript under single-example adjacency in the labeled sequence.

- The note (as provided here) motivates the question and asks for a qualitative equivalence and a quantitative relationship between the optimal non-private and private mistake bounds, but does not claim an equivalence theorem or a separating counterexample.

- Cohen et al. and Dmitriev et al. (COLT 2024) give new lower bounds and separations under continual observation and private online learning, providing partial evidence that privacy can strictly worsen online learnability even when the full equivalence question remains open.

## References

[1]

 [Open Problem: Do you pay for Privacy in Online learning?](https://proceedings.mlr.press/v178/open-problem-sanyal22a.html) 

Amartya Sanyal, Giorgia Ramponi (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-sanyal22a.html) [2]

 [Open Problem: Do you pay for Privacy in Online learning? (PDF)](https://proceedings.mlr.press/v178/open-problem-sanyal22a/open-problem-sanyal22a.pdf) 

Amartya Sanyal, Giorgia Ramponi (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-sanyal22a/open-problem-sanyal22a.pdf)

## Notes / Progress

_Work log goes here._
