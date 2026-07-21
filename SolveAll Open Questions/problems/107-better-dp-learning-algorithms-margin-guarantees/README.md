# Better Differentially Private Learning Algorithms with Margin Guarantees

**Status:** Unsolved  
**Source:** Posed by Raef Bassily et al. (2022)

## Categories

- Learning Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #107 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix sample size $m\in\mathbb{N}$ , privacy parameters $\epsilon>0$ and $\delta\ge 0$ , a margin parameter $\rho>0$ , and a distribution $D$ over $Z=X\times Y$ with $Y=\{-1,+1\}$ . Let $S=((x_1,y_1),\ldots,(x_m,y_m))\sim D^m$ .

(Margin losses.) For any measurable score function $h:X\to\mathbb{R}$ define the (population) $0$ - $1$ error and its empirical counterpart

$
R_D(h)=\Pr_{(x,y)\sim D}[y\,h(x)\le 0],\qquad \hat R_S(h)=\frac{1}{m}\sum_{i=1}^m \mathbf{1}[y_i h(x_i)\le 0].
$

For $\rho\ge 0$ define the $\rho$ -margin losses

$
R_D^{\rho}(h)=\Pr_{(x,y)\sim D}[y\,h(x)\le \rho],\qquad \hat R_S^{\rho}(h)=\frac{1}{m}\sum_{i=1}^m \mathbf{1}[y_i h(x_i)\le \rho].
$

For linear prediction, with $h_w(x)=\langle w,x\rangle$ , define the $\rho$ -hinge loss $\ell_\rho(u)=\max(1-u/\rho,0)$ and

$
L_D^{\rho}(w)=\mathbb{E}_{(x,y)\sim D}[\ell_\rho(y\langle w,x\rangle)],\qquad \hat L_S^{\rho}(w)=\frac{1}{m}\sum_{i=1}^m \ell_\rho(y_i\langle w,x_i\rangle).
$

(Differential privacy.) A randomized algorithm $\mathcal{A}:(X\times Y)^m\to\mathcal{H}$ is $(\epsilon,\delta)$ -differentially private if for all neighboring datasets $S,S'$ differing in exactly one example and all measurable $\mathcal{O}\subseteq\mathcal{H}$ ,

$
\Pr[\mathcal{A}(S)\in\mathcal{O}]\le e^{\epsilon}\Pr[\mathcal{A}(S')\in\mathcal{O}]+\delta.
$

Write $\tilde O(\cdot)$ for bounds hiding polylogarithmic factors in the relevant parameters.

### Unsolved Problem

Differentially private learners achieving confidence-margin (dimension-independent) generalization guarantees with improved computational or size-dependence, in two settings:

- Faster DP margin-based learning for linear and kernel classifiers. Assume $X\subseteq B_d(r)=\{x\in\mathbb{R}^d:\|x\|_2\le r\}$ and consider

$
H_{\mathrm{Lin}}=\{h_w:x\mapsto \langle w,x\rangle\mid w\in B_d(\Lambda)\}.
$

The COLT 2022 open-problem note describes an $(\epsilon,\delta)$ -DP algorithm outputting $w_{\mathrm{priv}}\in B_d(\Lambda)$ such that, with high probability over $S\sim D^m$ and the algorithm randomness,

$
R_D(h_{w_{\mathrm{priv}}})\le \min_{w\in B_d(\Lambda)} \hat L_S^{\rho}(w)+\tilde O\!\left(\frac{\Lambda r}{\rho\sqrt{\min(1,\epsilon)m}}\right),
$

with running time about $\tilde O(md)$ . For kernel classification with a continuous, positive definite, shift-invariant kernel $K$ with RKHS $(\mathcal{H},\|\cdot\|_{\mathcal{H}})$ and class $\mathcal{H}_\Lambda=\{h\in\mathcal{H}:\|h\|_{\mathcal{H}}\le \Lambda\}$ , the note describes an $(\epsilon,\delta)$ -DP algorithm outputting $h_{\mathrm{priv}}$ such that, with high probability,

$
R_D(h_{\mathrm{priv}})\le \min_{h\in\mathcal{H}_\Lambda} \hat L_S^{\rho}(h)+\tilde O\!\left(\frac{\Lambda r}{\rho\sqrt{\min(1,\epsilon)m}}\right),
$

with running time about $\tilde O(m^3 d)$ .

Question 1 (computational): Do there exist $(\epsilon,\delta)$ -DP algorithms for these linear and kernel problems that achieve essentially the same margin-based guarantees while having strictly better running time (as a polynomial in $m$ and $d$ ) than $\tilde O(md)$ for linear predictors and $\tilde O(m^3 d)$ for the above kernel approach?

- Neural networks: DP margin guarantees with no explicit size dependence. Let $H_{\mathrm{NN}}$ be a family of feed-forward neural networks of depth $L$ on inputs in $B_d(r)$ , and let $H_{\mathrm{NN},\Lambda}\subseteq H_{\mathrm{NN}}$ be those networks whose weight matrices are each bounded in Frobenius norm by $\Lambda>0$ . Suppose each hidden layer has width $N$ (so total size scales with $NL$ ). The note describes a pure $\epsilon$ -DP algorithm outputting $h_{\mathrm{priv}}\in H_{\mathrm{NN}}$ such that, with high probability,

$
R_D(h_{\mathrm{priv}})\le \min_{h\in H_{\mathrm{NN},\Lambda}} \hat R_S^{\rho}(h) + O\!\left(\frac{r\Lambda L\sqrt{NL}}{\rho\sqrt{m}} + \frac{r^2(2\Lambda)^{2L}NL}{\rho^2\epsilon m}\right),
$

which is independent of the input dimension $d$ but depends explicitly on $NL$ .

Question 2 (size dependence): Is it possible to design a DP learning algorithm for $H_{\mathrm{NN}}$ with a margin-based generalization guarantee that has no explicit dependence on network size, e.g. achieving (with high probability)

$
R_D(h_{\mathrm{priv}})\le \min_{h\in H_{\mathrm{NN},\Lambda}} \hat R_S^{\rho}(h) + O\!\left(\frac{r\Lambda L}{\rho\sqrt{m}} + \frac{r^2\Lambda^{2L}}{\rho^2\epsilon m}\right)?
$

## Significance & Implications

Margin-based guarantees are a central route to dimension-independent generalization bounds in classification. Under differential privacy, the COLT 2022 open-problem note highlights that existing approaches either incur substantial computational cost (even when the statistical guarantee is favorable) or, for neural networks, achieve dimension independence at the price of an explicit dependence on network size. Progress on Question 1 would turn the best-known DP margin guarantees for linear and kernel methods into algorithms with genuinely scalable polynomial-time dependence on $m$ and $d$ . Progress on Question 2 would clarify whether DP learning for neural networks can attain margin bounds controlled by norm/geometry parameters (e.g., $r,\Lambda,L,\rho,\epsilon,m$ ) without an explicit width/parameter-count term, which would align DP generalization guarantees more closely with the kind of size-insensitive margin theory studied in non-private settings.

## Known Partial Results

- The COLT 2022 open-problem note (Bassily, Mohri, Suresh) formulates DP confidence-margin learning as a route to dimension-independent guarantees and identifies two main gaps: computational efficiency for linear/kernel methods and network-size dependence for neural networks.

- For linear predictors with $X\subseteq B_d(r)$ and $\|w\|_2\le \Lambda$ , the note describes an $(\epsilon,\delta)$ -DP learner achieving a high-probability guarantee of the form $R_D(h_{w_{\mathrm{priv}}})\le \min_{\|w\|\le \Lambda} \hat L_S^{\rho}(w)+\tilde O\!\left(\tfrac{\Lambda r}{\rho\sqrt{\min(1,\epsilon)m}}\right)$ with running time about $\tilde O(md)$ .

- For shift-invariant kernels with RKHS norm constraint $\|h\|_{\mathcal{H}}\le \Lambda$ , the note describes an $(\epsilon,\delta)$ -DP learner achieving an analogous margin-based guarantee with running time about $\tilde O(m^3 d)$ .

- For depth- $L$ feed-forward neural networks with Frobenius-norm-bounded weight matrices (bound $\Lambda$ ) and width $N$ , the note describes a pure $\epsilon$ -DP learner that is independent of the input dimension $d$ but whose bound includes explicit dependence on $NL$ (e.g., terms scaling like $\frac{r\Lambda L\sqrt{NL}}{\rho\sqrt{m}}$ and $\frac{r^2(2\Lambda)^{2L}NL}{\rho^2\epsilon m}$ ).

- The note poses as open whether the explicit network-size dependence in such DP margin guarantees is inherent, and whether comparable guarantees can be achieved with substantially better computational complexity for linear/kernel margin-based learners.

## References

[1]

 [Open Problem: Better Differentially Private Learning Algorithms with Margin Guarantees](https://proceedings.mlr.press/v178/open-problem-bassily22a.html) 

Raef Bassily, Mehryar Mohri, Ananda Theertha Suresh (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-bassily22a.html) [2]

 [Open Problem: Better Differentially Private Learning Algorithms with Margin Guarantees (PDF)](https://proceedings.mlr.press/v178/open-problem-bassily22a/open-problem-bassily22a.pdf) 

Raef Bassily, Mehryar Mohri, Ananda Theertha Suresh (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-bassily22a/open-problem-bassily22a.pdf) [3]

 [Spectrally-normalized margin bounds for neural networks](https://arxiv.org/abs/1706.08498) 

Peter L. Bartlett, Dylan J. Foster, Matus J. Telgarsky (2017)

📍 Mentioned in the open-problem note as a non-private margin-bound comparator.

 [Link ↗](https://arxiv.org/abs/1706.08498) [arXiv ↗](https://arxiv.org/abs/1706.08498)

## Notes / Progress

_Work log goes here._
