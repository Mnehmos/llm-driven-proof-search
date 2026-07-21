# Universality for Wigner Matrices: Optimal Moment Conditions

**Status:** Partially Resolved  
**Importance:** Notable

## Categories

- Probability Theory
- Mathematical Statistics
- Mathematical Physics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #10 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X=(x_{ij})_{1\le i,j\le n}$ be either a real symmetric matrix ( $x_{ji}=x_{ij}$ ) or a complex Hermitian matrix ( $x_{ji}=\overline{x_{ij}}$ ), and define the Wigner matrix

$
W_n:=\frac{1}{\sqrt n}X.
$

Assume $\{x_{ij}:1\le i are i.i.d. (real case) or i.i.d. complex (Hermitian case), independent of the diagonal entries $\{x_{ii}\}_{i=1}^n$ , with

$
\mathbb E\,x_{ij}=0,\qquad \mathbb E\,|x_{ij}|^2=1.
$

(For complex entries, one may impose the standard normalization $\mathbb E\,x_{ij}^2=0$ .) Assume also $\mathbb E\,x_{ii}=0$ and $\mathbb E\,|x_{ii}|^2<\infty$ . Let $\lambda_1\le\cdots\le\lambda_n$ be the eigenvalues of $W_n$ . The empirical spectral measure converges to the semicircle law ( [Wigner (1958)](#references) ) with density $\rho_{\mathrm{sc}}(x)=\frac1{2\pi}\sqrt{(4-x^2)_+}$ .

### Unsolved Problem

Determine the weakest possible assumptions on the entry distribution (stated in terms of moments or tail decay of $x_{ij}$ , and if needed of $x_{ii}$ ) that guarantee universality of local spectral statistics, namely:

- 

Bulk universality: for every fixed bulk energy $E\in(-2,2)$ , after rescaling by the local spacing scale $(n\rho_{\mathrm{sc}}(E))^{-1}$ , the limiting local $k$ -point statistics (equivalently, limits of smooth observables of finitely many consecutive rescaled gaps) coincide with those of the Gaussian ensemble of the same symmetry class (GOE for real symmetric, GUE for complex Hermitian).

- 

Edge universality: for the top eigenvalue (and similarly the bottom eigenvalue),

$
n^{2/3}(\lambda_n-2)\ \xrightarrow{d}\ F_\beta,
$

where $F_\beta$ is the [Tracy & Widom (1994)](#references) law with $\beta=1$ (real) or $\beta=2$ (complex). By [Lee–Yin (2014)](#references) , this is governed by a necessary-and-sufficient tail criterion (equivalently, finite fourth moment is sufficient but not necessary).

Thus the edge threshold is essentially settled, while the main remaining issue is to identify the optimal minimal assumptions for full bulk universality in the most general Wigner setting. See [Erdős & Yau (2012)](#references) and the complementary comparison approach of [Tao & Vu (2011)](#references) .

## Significance & Implications

Random matrix universality is a deep phenomenon connecting probability, mathematical physics, and number theory. The [Tracy & Widom (1994)](#references) appears in growth models, longest increasing subsequences, and statistical tests. Pinning down truly minimal hypotheses for universality, especially in the bulk, remains a central structural question in modern probability theory (see [Erdős & Yau (2012)](#references) ).

## Known Partial Results

- [Erdős–Schlein–Yau (2009)](#references) : bulk universality for Wigner matrices under strong tail assumptions (sub-exponential decay) via local relaxation flow.

- [Tao–Vu (2011)](#references) : comparison/four-moment framework yielding local universality (including up to the edge) under high-regularity/tail hypotheses, by matching low-order moments with Gaussian-type ensembles.

- [Lee–Yin (2014)](#references) : necessary-and-sufficient criterion for Tracy–Widom edge fluctuations in terms of entry-tail behavior; in particular, finite fourth moment is sufficient but not necessary.

- [Aggarwal (2019)](#references) : bulk universality for broad Wigner classes under finite fourth-moment-type hypotheses, substantially weakening earlier tail conditions.

## References

[1]

 [Universality of local spectral statistics of random matrices](https://doi.org/10.1090/S0273-0979-2012-01372-1) 

László Erdős, Horng-Tzer Yau (2012)

Bulletin of the AMS

📍 Section 11 (Historical Remarks), discussion of then-open edge moment assumptions and broader universality program, p. 408 (Bull. Amer. Math. Soc. 49 (2012), 377–414).

 [DOI ↗](https://doi.org/10.1090/S0273-0979-2012-01372-1) [2]

 [Random matrices: Universality of local eigenvalue statistics](https://doi.org/10.1007/s11511-011-0061-3) 

Terence Tao, Van Vu (2011)

Acta Mathematica

📍 Main universality/comparison results for local eigenvalue statistics up to the edge via the Tao–Vu method (Acta Math. 206 (2011), 127–204).

 [DOI ↗](https://doi.org/10.1007/s11511-011-0061-3) [3]

 [On the distribution of the roots of certain symmetric matrices](https://doi.org/10.2307/1970008) 

Eugene P. Wigner (1958)

Annals of Mathematics

📍 Main theorem (semicircle law for eigenvalue distribution of real symmetric random matrices), pp. 325–327.

 [DOI ↗](https://doi.org/10.2307/1970008) [4]

 [Level-spacing distributions and the Airy kernel](https://doi.org/10.1007/BF02100489) 

Craig A. Tracy, Harold Widom (1994)

Communications in Mathematical Physics

📍 Section 1 (Introduction), Theorem 1 (Tracy–Widom distribution F₂ for GUE largest eigenvalue fluctuations), p. 152.

 [DOI ↗](https://doi.org/10.1007/BF02100489)

## Notes / Progress

_Work log goes here._
