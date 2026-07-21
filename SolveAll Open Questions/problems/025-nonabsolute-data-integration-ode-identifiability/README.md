# Flexible Nonabsolute-Data Integration for ODE Models with Structural Identifiability Guarantees

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Domagoj Doresic et al. (2025)

## Categories

- Computational Biology
- Dynamical Systems & Ergodic Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #25 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $x(t) \in \mathbb{R}^r$ denote the latent state of a biological system and let

$
\dot x(t)=f(x(t),\phi), \qquad x(0)=x_0(\phi),
$

be an ordinary differential equation model of a biological process, with unknown mechanistic parameters $\phi$ . Let the quantity of interest be

$
q(t,\phi)=h(x(t),\phi).
$

At observation times $t_1,\dots,t_n$ , idealized absolute measurements would observe $q(t_i,\phi)$ directly. In many biological assays, however, the observation is nonabsolute: one instead observes

$
\tilde y_i \sim \mathcal{P}\big(g_{\psi}(q(t_i,\phi))\big),
$

where $g_{\psi}$ is an unknown or only partially known recording function with nuisance parameters $\psi$ , and $\mathcal{P}$ is a suitable noise model (for example Gaussian or count-valued). Examples include semiquantitative measurements with unknown scaling or saturation, ordinal categories such as low/medium/high, and censored observations that only specify inequalities relative to detection thresholds.

Current flexible data-integration approaches can fit such data, but the most expressive ones either do not provide an explicit smooth recording function or use parameterizations that fall outside the reach of standard structural identifiability tools.

### Unsolved Problem

Construct a practically useful family of recording-function models $g_{\psi}$ , together with scalable inference algorithms, that simultaneously satisfy all four goals below:

- 

support semiquantitative, qualitative, and censored data encountered in systems biology;

- 

remain flexible enough to capture unknown nonlinear assay effects;

- 

admit rigorous structural identifiability analysis for both mechanistic parameters $\phi$ and recording-function parameters $\psi$ ; and

- 

support likelihood-based practical identifiability analysis and uncertainty quantification.

Equivalently, determine whether one can obtain an explicit analytic nonabsolute-data integration framework that is both biologically flexible and compatible with the full identifiability-and-uncertainty workflow used for ODE model calibration.

## Significance & Implications

Mechanistic ODE models are central in systems biology, but many experiments produce only relative, ordinal, or censored observations rather than calibrated concentrations. If flexible recording-function models destroy identifiability or calibrated uncertainty quantification, then fitted parameters may look precise while remaining scientifically ambiguous. Solving this problem would substantially widen the range of experiments that can be used for principled mechanistic inference.

## Known Partial Results

- [Doresic et al. (2025)](#references) survey current approaches for qualitative, semiquantitative, and censored observations in ODE calibration and make the gap explicit: flexible methods exist, but structural identifiability analysis is unavailable for the current flexible nonabsolute-data integration methods.

- The review also emphasizes that likelihood-based formulations already support practical identifiability analysis and uncertainty quantification in several settings, so the remaining obstacle is not only fitting the data, but reconciling flexibility with structural identifiability.

- On the method side, spline-based recording-function models such as [Doresic, Grein, and Hasenauer (2024)](#references) improve semiquantitative-data flexibility and computational efficiency, but the 2025 review still treats a fully flexible, explicit, structurally identifiable framework as open.

- Standardized benchmarks are also still missing, which makes it harder to compare competing nonabsolute-data integration strategies on equal footing.

## References

[1]

 [Identifiability and uncertainty for ordinary differential equation models with qualitative or semiquantitative data](https://www.sciencedirect.com/science/article/pii/S2452310025000186) 

Domagoj Doresic, Dilan Pathirana, Daniel Weindl, Jan Hasenauer (2025)

Current Opinion in Systems Biology

📍 Highlights, problem statement, structural/practical identifiability discussion, and final Discussion section.

Primary source and recent status review; explicitly identifies the lack of flexible analytic recording-function methods compatible with structural identifiability analysis.

 [Link ↗](https://www.sciencedirect.com/science/article/pii/S2452310025000186) [DOI ↗](https://doi.org/10.1016/j.coisb.2025.100558) [2]

 [Efficient parameter estimation for ODE models of cellular processes using semi-quantitative data](https://doi.org/10.1093/bioinformatics/btae210) 

Domagoj Doresic, Simon Grein, Jan Hasenauer (2024)

Bioinformatics

📍 Cited in the 2025 review as a spline-based recording-function approach that improves flexibility and efficiency but does not close the structural-identifiability gap.

Example of a recent flexible semiquantitative-data integration method based on monotone splines.

 [DOI ↗](https://doi.org/10.1093/bioinformatics/btae210)

## Notes / Progress

_Work log goes here._
