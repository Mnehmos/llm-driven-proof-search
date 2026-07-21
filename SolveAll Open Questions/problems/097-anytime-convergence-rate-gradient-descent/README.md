# Anytime Convergence Rate of Gradient Descent

**Status:** Partially Resolved  
**Source:** Posed by Guy Kornowski et al. (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #97 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $f: \mathbb{R}^d \to \mathbb{R}$ be a convex differentiable function with $L$ -Lipschitz gradient (" $L$ -smooth"), i.e., $\|\nabla f(x)-\nabla f(y)\| \le L\|x-y\|$ for all $x,y$ . Assume $f$ attains its minimum, and fix an initialization $x_0 \in \mathbb{R}^d$ with some minimizer $x^* \in \arg\min f$ and value $f^* = f(x^*)$ . Consider vanilla gradient descent with a predetermined (oblivious) stepsize sequence $(\eta_t)_{t\ge 0}$ (possibly depending on $L$ but not on the stopping time $T$ ):

$
x_{t+1} = x_t - \eta_t \nabla f(x_t), \qquad t=0,1,2,\dots.
$

The classical worst-case guarantee for suitable constant stepsizes gives an anytime bound of order $f(x_T)-f^* \le C\,L\|x_0-x^*\|^2/T$ holding for all $T\in\mathbb{N}$ and all $L$ -smooth convex $f$ , with a universal constant $C$ .

### Unsolved Problem

Do stepsizes alone yield a strictly faster worst-case anytime rate on the actual iterate $x_T$ ? Equivalently, does there exist a stepsize sequence $(\eta_t)_{t\ge 0}$ and an exponent $\alpha>1$ such that for some universal constant $C<\infty$ , for every dimension $d$ , every $L$ -smooth convex $f$ attaining its minimum, every initialization $x_0$ , every choice of minimizer $x^*\in\arg\min f$ , and every $T\in\mathbb{N}$ ,

$
f(x_T)-f^* \le C\,\frac{L\|x_0-x^*\|^2}{T^\alpha}?
$

More generally, what is the best function $r(T)$ for which there exists an oblivious stepsize schedule such that $f(x_T)-f^* \le C\,L\|x_0-x^*\|^2\,r(T)$ holds simultaneously for all $T$ and all $L$ -smooth convex $f$ ?

## Significance & Implications

This problem isolates the power and limits of "stepsize-only" design for the most basic first-order method. An affirmative answer would show that, without momentum, restarts, or changing the update rule, gradient descent can achieve a worst-case guarantee that decays faster than $1/T$ at every time $T$ using a single oblivious schedule. A negative answer would establish an intrinsic separation between plain gradient descent and accelerated methods in the anytime (per-iterate) sense, pinpointing that any apparent acceleration from clever stepsizes must fail at some times or for some smooth convex objectives.

## Known Partial Results

- With constant stepsize $\eta_t\equiv\eta\in(0,2/L)$ , standard analysis yields an anytime worst-case bound of the form $f(x_T)-f^* \le C\,L\|x_0-x^*\|^2/T$ for all $T\in\mathbb{N}$ .

- There exist non-constant stepsize schedules that achieve an accelerated bound at selected, pre-specified horizons (e.g., along a sparse subsequence of times), but such horizon-specific acceleration does not by itself imply an anytime bound for the specific iterate $x_T$ at every $T$ .

- A horizon-specific guarantee can be converted into an anytime guarantee only for best-so-far performance (e.g., $\min_{t\le T} f(x_t)-f^*$ by selecting a nearby special horizon), which is strictly weaker than bounding $f(x_T)-f^*$ for each $T$ .

- Any oblivious schedule that would improve the anytime worst-case rate beyond $O(1/T)$ uniformly over all $L$ -smooth convex objectives (in the sense $f(x_T)-f^* = o(L\|x_0-x^*\|^2/T)$ for all $T$ ) must use unbounded stepsizes, i.e., $\limsup_{t\to\infty} \eta_t = \infty$ .

- Large individual steps can cause persistent large errors: in dimension $d=1$ , if at some time $T$ one has $\eta_T\ge 2/L$ and also $\sum_{t=0}^{T-1}\eta_t\ge 1/L$ , then there exists an $L$ -smooth convex $f$ such that

$
f(x_{T+1})-f^* \ge \frac{1}{32L}\,\|x_0-x^*\|^2\left(\frac{\eta_T}{\sum_{t=0}^{T-1}\eta_t}\right)^2.
$

- Consequently, if a schedule has infinitely many times where the ratio $\eta_T/\sum_{t is bounded away from $0$ while taking such long steps, then $f(x_T)-f^*$ can remain on the order of $L\|x_0-x^*\|^2$ at arbitrarily large times, ruling out any decaying anytime bound for that schedule.

- Zhang, Lee, Du, and Chen (COLT 2025) give an oblivious stepsize schedule with anytime rate $O(T^{-1.119})$ , providing an affirmative answer to the existential $o(1/T)$ question; the exact optimal anytime rate remains open.

## References

[1]

 [Open Problem: Anytime Convergence Rate of Gradient Descent](https://proceedings.mlr.press/v247/kornowski24a.html) 

Guy Kornowski, Ohad Shamir (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/kornowski24a.html) [2]

 [Open Problem: Anytime Convergence Rate of Gradient Descent (PDF)](https://proceedings.mlr.press/v247/kornowski24a/kornowski24a.pdf) 

Guy Kornowski, Ohad Shamir (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/kornowski24a/kornowski24a.pdf)

## Notes / Progress

_Work log goes here._
