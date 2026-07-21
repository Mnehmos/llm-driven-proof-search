# IMO 2026 Problem 6

**Day 2 · Number theory**

Let $a_1, a_2, a_3, \ldots$ be an infinite sequence of positive integers
greater than $1$. Suppose that for all positive integers $n$, the number
$a_{n+1}$ is the smallest positive integer greater than $a_n$ such that
$\gcd(a_{n+1}, a_i) > 1$ for every $i = 1, 2, \ldots, n$. Prove that there
exist positive integers $T$ and $L$ such that

$$a_{n+T} = a_n + L$$

for every positive integer $n$.

*(Note that $\gcd(x, y)$ denotes the greatest common divisor of positive
integers $x$ and $y$.)*

---

Transcription notes:

- Only $a_1 > 1$ is freely chosen; every later term is forced by the greedy
  rule (smallest successor sharing a factor with **all** previous terms), so
  the claim is that every such greedy sequence is eventually — in fact from
  $n = 1$ — arithmetic-periodic with shift $L$ and period $T$.
