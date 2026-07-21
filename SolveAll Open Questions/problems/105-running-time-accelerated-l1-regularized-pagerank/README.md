# Running time complexity of accelerated l1-regularized PageRank

**Status:** Resolved  
**Source:** Posed by Kimon Fountoulakis et al. (2022)

## Categories

- Learning Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #105 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $G=(V,E)$ be a (possibly directed) graph with $n=|V|$ and let $P\in\mathbb{R}^{n\times n}$ be a row-stochastic random-walk matrix (so $P\mathbf{1}=\mathbf{1}$ and $P_{ij}\ge 0$ ). Fix a teleportation parameter $\alpha\in(0,1]$ and a preference distribution $s\in\mathbb{R}^n$ with $s\ge 0$ and $\mathbf{1}^\top s=1$ . The Personalized PageRank (PPR) vector $p\in\mathbb{R}^n$ is the unique solution of

$
p=\alpha s+(1-\alpha)Pp,\qquad\text{equivalently }(I-(1-\alpha)P)p=\alpha s.
$

For a sparsity/regularization parameter $\rho>0$ , define the $\ell_1$ -regularized PPR objective

$
F(x):=\tfrac12\left\|(I-(1-\alpha)P)x-\alpha s\right\|_2^2+\rho\|x\|_1,
$

and let $x_\rho\in\arg\min_{x\in\mathbb{R}^n} F(x)$ . Consider computing an approximate minimizer $\hat x$ by first-order composite optimization methods, e.g. guaranteeing a prescribed accuracy such as $F(\hat x)-F(x_\rho)\le \varepsilon$ for a chosen $\varepsilon>0$ .

The COLT 2022 open-problem note reports that the best currently analyzed method for this task is (non-accelerated) proximal gradient, with total running time $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ (up to logarithmic factors) and, importantly, a bound that does not depend on $n$ .

### Unsolved Problem

Determine the worst-case total running time complexity of an accelerated proximal gradient method (e.g. a Nesterov/FISTA-type scheme) applied to $F$ under a comparable accuracy criterion. In particular:

- Can one prove an $n$ -independent worst-case bound of the form

$
\tilde{\mathcal{O}}\left((\sqrt{\alpha}\,\rho)^{-1}\right)
$

thereby achieving a $1/\sqrt{\alpha}$ improvement over $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ ?

- Failing that, can one at least prove that acceleration cannot be asymptotically worse in the worst case than $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ , or else exhibit a family of instances for which accelerated proximal gradient is provably worse (in worst-case total running time) than the non-accelerated proximal gradient method?

## Significance & Implications

The appeal of $\ell_1$ -regularized PPR is that it targets sparse/thresholded solutions and admits algorithms whose proven total running time can be independent of the ambient graph size $n$ , which is critical in large-scale network settings. The currently best analyzed complexity $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ scales poorly as $\alpha\to 0$ , a regime emphasized as practically relevant in the COLT 2022 note. Establishing (or refuting) an accelerated $n$ -independent guarantee around $\tilde{\mathcal{O}}((\sqrt{\alpha}\,\rho)^{-1})$ would clarify whether one can obtain a principled $1/\sqrt{\alpha}$ speedup for this widely used regularized PPR primitive without sacrificing the key property of size-independent worst-case bounds.

## Known Partial Results

- Prior work (as summarized in the COLT 2022 open-problem note) motivates $\ell_1$ -regularization for PPR as a mechanism that automatically thresholds small PPR probabilities, and relates this to early termination, yielding approximate (sparse) PPR computations.

- The COLT 2022 note states that the fastest currently analyzed method for computing $\ell_1$ -regularized PPR is a proximal gradient method with total running time $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ .

- A key feature emphasized in the note is that this $\tilde{\mathcal{O}}((\alpha\rho)^{-1})$ guarantee does not depend on $n$ (the dimension/graph size), which is treated as a prerequisite for modern large-scale networks.

- A natural idea is to apply acceleration (e.g. FISTA-type) to proximal gradient, with the goal of improving the dependence on $\alpha$ to $\tilde{\mathcal{O}}((\sqrt{\alpha}\,\rho)^{-1})$ .

- The note cautions that the existing proximal-gradient analysis in the cited prior work does not directly carry over to the accelerated variant.

- The note reports empirical evidence that accelerated proximal gradient can reduce total running time in practice, but leaves open whether acceleration has a provable worst-case improvement, or could even be worse in the worst case.

## References

[1]

 [Open Problem: Running time complexity of accelerated $\ell_1$-regularized PageRank](https://proceedings.mlr.press/v178/open-problem-fountoulakis22a.html) 

Kimon Fountoulakis, Shenghao Yang (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-fountoulakis22a.html) [2]

 [Open Problem: Running time complexity of accelerated $\ell_1$-regularized PageRank (PDF)](https://proceedings.mlr.press/v178/open-problem-fountoulakis22a/open-problem-fountoulakis22a.pdf) 

Kimon Fountoulakis, Shenghao Yang (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-fountoulakis22a/open-problem-fountoulakis22a.pdf)

## Notes / Progress

_Work log goes here._
