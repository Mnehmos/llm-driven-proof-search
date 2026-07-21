# IMO 2026 Problem 1

**Day 1 · Number theory**

There are $2026$ integers greater than $1$ written on a blackboard, not
necessarily different. In a move, Confucius chooses two integers $m > 1$ and
$n > 1$ from different places on the blackboard and replaces these two integers
with

$$\gcd(m, n) \qquad \text{and} \qquad \frac{\operatorname{lcm}(m, n)}{\gcd(m, n)}.$$

He continues to make moves while it is possible to do so.

**(a)** Prove that, regardless of the choices of Confucius, after finitely many
moves, exactly one integer $M$ on the blackboard is greater than $1$.

**(b)** Prove that the value of $M$ does not depend on the choices of
Confucius.

*(Note that $\gcd(x, y)$ denotes the greatest common divisor of positive
integers $x$ and $y$, and $\operatorname{lcm}(x, y)$ denotes the least common
multiple of $x$ and $y$.)*

---

Transcription notes:

- A move requires **both** chosen integers to exceed $1$; the process halts
  exactly when at most one entry on the board is greater than $1$.
- The replacement is $\gcd(m,n)$ and $\operatorname{lcm}(m,n)/\gcd(m,n)$ — not
  the classic $\gcd/\operatorname{lcm}$ pair. The product of the pair is *not*
  preserved when $\gcd(m,n) > 1$.
