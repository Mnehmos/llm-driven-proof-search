# Non-asymptotic oracle inequalities for fully data-driven generalized-inverse shrinkage

**Status:** Unsolved  
**Source:** Sourced from the work of Taras Bodnar, Nestor Parolya

## Categories

- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #63 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X_1,\dots,X_n\in\mathbb R^{p}$ be i.i.d. with $\mathbb E[X_i]=0$ and

$
X_i=\Sigma^{1/2}Z_i,\qquad \mathbb E[Z_i]=0,\ \mathbb E[Z_iZ_i^\top]=I_p,
$

where $\Sigma$ is symmetric positive definite. Work in the high-dimensional regime $p>n$ with $p/n\to c>1$ . Assume a bounded $4+\varepsilon$ moment bound for some $\varepsilon>0$ , e.g.

$
\sup_{\|u\|_2=1}\mathbb E\,|u^\top Z_i|^{4+\varepsilon}\le K_{4+\varepsilon}<\infty.
$

(If one imposes stronger tails such as sub-Gaussianity, treat that as a deliberate strengthening.)

This setup follows [Bodnar & Parolya (2024)](#references) .

Define

$
S_n=\frac1n\sum_{i=1}^n X_iX_i^\top,
$

its Moore-Penrose inverse $S_n^\dagger$ , and ridge inverse $G_n(\lambda)=(S_n+\lambda I_p)^{-1}$ for $\lambda>0$ . Let $\Theta_\star=\Sigma^{-1}$ and fix a deterministic symmetric target $T_n$ with bounded operator norm. For $\alpha\in\mathcal A\subset[0,1]$ and $\lambda\in\Lambda\subset(0,\infty)$ , define

$
\widehat\Theta_n^{\mathrm{MP}}(\alpha)=\alpha S_n^\dagger+(1-\alpha)T_n,\qquad \widehat\Theta_n^{\mathrm{R}}(\alpha,\lambda)=\alpha G_n(\lambda)+(1-\alpha)T_n.
$

### Unsolved Problem

With loss $L_n(\Theta)=p^{-1}\|\Theta-\Theta_\star\|_F^2$ and risk $\mathcal R_n(\Theta)=\mathbb E[L_n(\Theta)]$ , seek fully data-driven selectors $(\hat\alpha_n,\hat\lambda_n)$ (measurable in the sample, no population oracle input) such that finite-sample oracle inequalities hold:

$
\mathcal R_n\!\left(\widehat\Theta_n^{\mathrm{MP}}(\hat\alpha_n)\right)-\inf_{\alpha\in\mathcal A}\mathcal R_n\!\left(\widehat\Theta_n^{\mathrm{MP}}(\alpha)\right)\le C\psi_{n,p},
$

and

$
\mathcal R_n\!\left(\widehat\Theta_n^{\mathrm{R}}(\hat\alpha_n,\hat\lambda_n)\right)-\inf_{\alpha\in\mathcal A,\lambda\in\Lambda}\mathcal R_n\!\left(\widehat\Theta_n^{\mathrm{R}}(\alpha,\lambda)\right)\le C\psi_{n,p},
$

with explicit non-asymptotic $\psi_{n,p}$ and transparent constants under the stated moment/regime assumptions.

## Significance & Implications

The source establishes asymptotic behavior in large-dimensional settings, but practical tuning still needs explicit finite-sample guarantees. Non-asymptotic oracle inequalities would quantify reliability gaps for pseudo-inverse and ridge-type precision estimation in the $c>1$ regime.

## Known Partial Results

This problem remains open in the specific scope above: fully data-driven tuning with explicit finite-sample oracle inequalities for both Moore-Penrose and ridge-type shrinkage under the $p/n\to c>1$ and bounded $4+\varepsilon$ -moment framework. Nearby 2025 non-asymptotic ridge-related results (risk/concentration bounds in adjacent models) reduce technical uncertainty but do not by themselves close this exact oracle-inequality target.

## References

[1]

 [Reviving pseudo-inverses: Asymptotic properties of large dimensional Moore-Penrose and Ridge-type inverses with applications](https://arxiv.org/abs/2403.15792) 

Taras Bodnar, Nestor Parolya (2024)

arXiv preprint

📍 Section 1 (Introduction), p. 2, second paragraph: “No other results have been derived either for the Moore-Penrose inverse or for the ridge-type inverse in the non-asymptotic setting…”

Primary source motivating this synthesized open problem.

 [Link ↗](https://arxiv.org/abs/2403.15792) [DOI ↗](https://doi.org/10.48550/arXiv.2403.15792) [arXiv ↗](https://arxiv.org/abs/2403.15792)

## Notes / Progress

_Work log goes here._
