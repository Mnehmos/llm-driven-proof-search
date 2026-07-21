# General-k threshold for testing correlated SBMs against independent SBMs

**Status:** Unsolved  
**Source:** Sourced from the work of Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li

## Categories

- Probability Theory
- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #34 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix an integer $k \ge 2$ and constants $\lambda>0$ , $\epsilon \in \big(-\frac{1}{k-1},1\big)$ , and $s\in(0,1]$ , with $k,\lambda,\epsilon$ independent of $n$ . Let $P_n$ be the correlated pair model obtained by subsampling (edge-retention probability $s$ in each child) from a parent symmetric sparse SBM $\mathcal S(n,\lambda/n;k,\epsilon)$ , and let $\widetilde Q_n$ be two independent draws from the matching marginal SBM $\mathcal S(n,\lambda s/n;k,\epsilon)$ . Given one sample $(G_1,G_2)$ , test $H_0:(G_1,G_2)\sim \widetilde Q_n$ versus $H_1:(G_1,G_2)\sim P_n$ , and define information-theoretic and polynomial-time thresholds $s_{\mathrm{IT}}^{\mathrm{SBM}}(\lambda,\epsilon,k)$ and $s_{\mathrm{comp}}^{\mathrm{SBM}}(\lambda,\epsilon,k)$ in the usual vanishing-risk sense.

### Unsolved Problem

Determine sharp thresholds for general constant $k$ against the independent-SBM null, including a full characterization of what is possible/impossible across regimes above and below the KS boundary ( $\lambda\epsilon^2 s=1$ ) and relative to the Otter barrier ( $s=\sqrt{\alpha}$ , $\alpha\approx 0.338$ ). In particular, resolve matching achievability/converse results for general $k$ , rather than only currently understood special regimes.

## Significance & Implications

Testing against an independent SBM null isolates correlation signal from marginal community structure, making it stricter than Erdos-Renyi-null formulations. Post-2024 work substantially sharpened both algorithmic upper bounds (notably for $k=2$ supercritical regimes) and conditional lower bounds in subcritical/below-Otter regimes, but a general- $k$ sharp picture is still missing.

## Known Partial Results

Historical (2024): Chen-Ding-Gong-Li (arXiv:2409.00966) established a sharp low-degree transition for testing correlated SBMs versus independent Erdos-Renyi nulls, and explicitly suggested extension to independent-SBM nulls as future work (with heuristic plausibility above $\sqrt{\alpha}$ ).

Current status (2026): there is substantial progress but not a complete resolution of this general- $k$ problem. In particular, arXiv:2503.06464 provides stronger polynomial-time positive results in supercritical regimes (notably breaking the previous Otter barrier in a broadened $k=2$ setting), while arXiv:2502.09832 / APPROX-RANDOM 2025 gives conditional computational lower bounds below KS and below Otter for the independent-SBM testing formulation. A full sharp characterization for general constant $k$ across all above/below KS and Otter regimes remains open.

## References

[1]

 [A Computational Transition for Detecting Correlated Stochastic Block Models by Low-Degree Polynomials](https://arxiv.org/abs/2409.00966v2) 

Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li (2024)

Annals of Statistics (to appear)

📍 Section 1 (Introduction), Remark 1.7, p. 4 in arXiv v2 PDF (submitted 2024-09-02; revised 2025-07-22); with setup in Remark 1.6 (pp. 3-4).

Primary source where the independent-SBM follow-up question is raised. Metadata convention used here: `year` = first public appearance year (v1), while `arxiv_id` pins the exact cited version.

 [Link ↗](https://arxiv.org/abs/2409.00966v2) [arXiv ↗](https://arxiv.org/abs/2409.00966v2) [2]

 [Detecting Correlation Efficiently in Stochastic Block Models: Breaking Otter's Threshold in the Entire Supercritical Regime](https://arxiv.org/abs/2503.06464v2) 

Guanyi Chen, Jian Ding, Shuyang Gong, Zhangsong Li (2025)

arXiv preprint

📍 Abstract and introduction statements on improved/broadened supercritical detection guarantees.

Post-2024 algorithmic progress; gives improved efficient detection guarantees for correlated-vs-independent SBM in supercritical settings (not yet a full general-$k$ sharp characterization).

 [Link ↗](https://arxiv.org/abs/2503.06464v2) [arXiv ↗](https://arxiv.org/abs/2503.06464v2) [3]

 [Computational Lower Bounds for Correlated Random Graphs via Algorithmic Contiguity](https://arxiv.org/abs/2502.09832v4) 

Zhangsong Li (2025)

arXiv preprint

📍 Abstract, item (2): hardness for SBM testing when $\epsilon^2\lambda s<1$ and $s<\sqrt{\alpha}$.

Gives conditional computational lower bounds (under low-degree conjecture) including the correlated-vs-independent SBM testing regime below KS and below Otter.

 [Link ↗](https://arxiv.org/abs/2502.09832v4) [arXiv ↗](https://arxiv.org/abs/2502.09832v4) [4]

 [Algorithmic Contiguity from Low-Degree Conjecture and Applications in Correlated Random Graphs](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2025.30) 

Zhangsong Li (2025)

LIPIcs, APPROX/RANDOM 2025

📍 DROPS metadata page: abstract and 'Related Versions' entry (full version arXiv:2502.09832).

Conference version of the algorithmic-contiguity framework and applications; related version metadata explicitly links full version arXiv:2502.09832.

 [Link ↗](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2025.30)

## Notes / Progress

_Work log goes here._
