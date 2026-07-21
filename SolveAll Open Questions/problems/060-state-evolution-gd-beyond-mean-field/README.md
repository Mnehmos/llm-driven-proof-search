# State evolution for gradient descent beyond the mean-field scaling

**Status:** Unsolved  
**Source:** Sourced from the work of Qiyang Han, Xiaocong Xu

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #60 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider high-dimensional empirical-risk minimization solved by gradient descent in random-design settings where the aspect ratio is allowed to deviate from the proportional mean-field regime. Existing non-asymptotic joint state-evolution guarantees in this line of work are proved under proportional scaling assumptions used in the source, together with its structured response-model conditions.

This setup follows [Han & Xu (2025)](#references) .

### Unsolved Problem

Extend a comparable joint state-evolution theorem, with explicit finite-sample error control and time-uniform guarantees up to horizon $T$ , to non-mean-field regimes such as $n/p\to\infty$ and $n/p\to 0$ , and identify the corresponding Onsager correction operators/matrices under clearly stated assumptions for those regimes.

## Significance & Implications

Interpreting the source discussion as motivation, this problem asks whether the Onsager-corrected dependency structure developed in the mean-field analysis persists, changes form, or breaks down outside that regime, which would help relate the paper's high-dimensional theory to more classical or extreme aspect-ratio limits.

## Known Partial Results

The paper proves a non-asymptotic joint state-evolution theorem with two Onsager correction matrices in its mean-field proportional regime under its specified modeling assumptions. This entry is treated as open beyond the scope established in the cited source.

## References

[1]

 [Gradient descent inference in empirical risk minimization](https://doi.org/10.1214/25-AOS2492) 

Qiyang Han, Xiaocong Xu (2025)

Annals of Statistics

📍 Section 2.1 (Assumption A1: proportional/mean-field regime of main interest), and Section 2.3 discussion after Theorem 2.3 around Eqs. (2.14)-(2.15), where behavior beyond mean-field/approximate low-dimensional regimes is flagged as different and not covered by the proved theorem.

Primary source; 2025 online publication in Annals of Statistics (preprint available as arXiv:2412.09498).

 [Link ↗](https://doi.org/10.1214/25-AOS2492) [DOI ↗](https://doi.org/10.1214/25-AOS2492) [arXiv ↗](https://arxiv.org/abs/2412.09498)

## Notes / Progress

_Work log goes here._
