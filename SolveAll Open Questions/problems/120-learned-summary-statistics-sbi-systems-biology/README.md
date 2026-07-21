# Learned Summary Statistics for Simulation-Based Inference in Systems Biology

**Status:** Unsolved  
**Source:** Posed by Abolfazl Ahmadi et al. (2025)

## Categories

- Computational Biology
- Mathematical Statistics
- Dynamical Systems & Ergodic Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #120 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\Theta$ be a parameter space and let $\mathcal{X}$ be a space of observable datasets, such as time series, snapshot collections, or stochastic reaction-network trajectories. For each $\theta \in \Theta$ , let $P_\theta$ be the distribution of $X \in \mathcal{X}$ under a mechanistic systems-biology model, and let $p_\theta(x)$ denote the corresponding likelihood when it exists. Assume that one can efficiently simulate $X \sim P_\theta$ , but that evaluating $p_\theta(x)$ exactly is unavailable or computationally prohibitive.

In Bayesian simulation-based inference, one specifies a prior density $\pi_0(\theta)$ and aims to approximate the posterior

$
\pi(\theta\mid x_{\mathrm{obs}}) \propto \pi_0(\theta)p_\theta(x_{\mathrm{obs}})
$

for the observed dataset $x_{\mathrm{obs}} \in \mathcal{X}$ .

A common strategy is to replace the full data by a learned summary map

$
S : \mathcal{X} \to \mathbb{R}^d
$

and then approximate the posterior of $\theta$ using only $S(x_{\mathrm{obs}})$ rather than the full observation $x_{\mathrm{obs}}$ . The central tension is that lower-dimensional summaries can dramatically reduce simulation and optimization cost, but may destroy inferential sufficiency, calibration, or robustness under model misspecification.

### Unsolved Problem

Design and analyze learned-summary-statistic pipelines for systems-biology models that are simultaneously simulation-efficient, approximately sufficient for the target parameters, robust to moderate model misspecification, and equipped with calibrated uncertainty quantification. In particular, determine the tradeoffs among summary dimension $d$ , simulation budget, approximation error, and posterior calibration for broad families of ODE, stochastic biochemical-network, and hybrid mechanistic models, and develop benchmark criteria that certify when a learned summary is genuinely adequate for downstream inference rather than merely convenient.

## Significance & Implications

Mechanistic systems-biology models are often rich enough to simulate but too complex for direct likelihood-based inference. Learned summaries offer a plausible way to make Bayesian calibration practical, but only if they preserve the scientifically relevant information. Solving this problem would improve parameter inference, model comparison, and experimental design across signaling, gene regulation, and cellular decision-making models.

## Known Partial Results

- [Ahmadi et al. (2025)](#references) review recent progress on machine-learned summary statistics for Bayesian parameter inference in systems biology and make clear that scalability gains come with unresolved questions about sufficiency, robustness, and benchmark design.

- The simulation-based-inference literature already provides flexible amortized and likelihood-free estimators, surveyed by [Cranmer, Brehmer, and Louppe (2020)](#references) , but those advances do not by themselves guarantee that the learned summaries used in mechanistic biology models preserve the parameter information scientists actually care about.

- The open gap is therefore not only algorithmic speed, but a combined theory-and-benchmark problem for when learned summaries remain scientifically trustworthy.

## References

[1]

 [Machine-learned summary statistics for Bayesian inference of systems biology-model parameters: Opportunities and challenges](https://doi.org/10.1016/j.coisb.2025.100560) 

Abolfazl Ahmadi, Larisa Podina, Stefanie Hopfl, Brian P. Ingalls (2025)

Current Opinion in Systems Biology

📍 Abstract and perspective discussion on summary-statistic sufficiency, robustness, simulation-budget tradeoffs, and benchmarking challenges.

Primary source and recent perspective on open issues for learned summary statistics in Bayesian inference for systems-biology models.

 [Link ↗](https://doi.org/10.1016/j.coisb.2025.100560) [DOI ↗](https://doi.org/10.1016/j.coisb.2025.100560) [2]

 [The frontier of simulation-based inference](https://doi.org/10.1073/pnas.1912789117) 

Kyle Cranmer, Johann Brehmer, Gilles Louppe (2020)

Proceedings of the National Academy of Sciences

📍 Overview article on simulation-based inference frontiers and methodological tradeoffs.

General background on simulation-based inference and why summary design is central when likelihoods are unavailable.

 [Link ↗](https://doi.org/10.1073/pnas.1912789117) [DOI ↗](https://doi.org/10.1073/pnas.1912789117)

## Notes / Progress

_Work log goes here._
