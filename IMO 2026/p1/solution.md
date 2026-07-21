# IMO 2026 Problem 1 — Solution

Let the current board entries be positive integers. Write

$$P=\prod_{x\text{ on the board}}x,
\qquad
k=\#\{x\text{ on the board}:x>1\}.$$

## Part (a)

Suppose a move selects $m,n>1$, and put

$$g=\gcd(m,n),
\qquad
q=\frac{\operatorname{lcm}(m,n)}{g}.$$

Because $mn=g\operatorname{lcm}(m,n)$, the product of the two new entries is

$$gq=\operatorname{lcm}(m,n)=\frac{mn}{g}.$$

Thus the board product changes from $P$ to $P/g$.

Consider the positive-integer potential

$$\Phi=P\,2^k.$$

If $g=1$, the chosen pair is replaced by $1$ and $mn$. Hence $P$ is unchanged,
while $k$ decreases by exactly $1$. Therefore $\Phi$ is divided by $2$.

If $g>1$, then $g\ge2$, so the new product satisfies $P/g\le P/2$. Moreover,
two entries greater than $1$ are replaced by at most two such entries, so $k$
does not increase. Again $\Phi$ decreases, in fact to at most $\Phi/2$.

Consequently every move strictly decreases the positive integer $\Phi$.
There can therefore be only finitely many moves.

It remains to determine how many entries greater than $1$ are present when the
process stops. After a move, the product of the two new entries is
$\operatorname{lcm}(m,n)\ge\max(m,n)>1$. Hence the product of all board entries
is always greater than $1$, so at least one board entry is greater than $1$.
On the other hand, the process stops precisely when fewer than two such entries
remain. Thus at termination there is exactly one entry $M>1$.

## Part (b)

Fix a prime $p$, and let $v_p(x)$ denote the exponent of $p$ in $x$. If

$$a=v_p(m),\qquad b=v_p(n),$$

then

$$v_p(g)=\min(a,b)$$

and

$$v_p(q)
=v_p(\operatorname{lcm}(m,n))-v_p(g)
=\max(a,b)-\min(a,b).$$

For this prime, define the board invariant candidate

$$G_p=\gcd\bigl(v_p(x):x\text{ is on the board}\bigr),$$

where zeros are included and $\gcd(0,r)=r$. A move replaces the two relevant
valuations $a,b$ by

$$\min(a,b),\qquad \max(a,b)-\min(a,b).$$

These two new numbers have the same gcd as the old pair. Indeed, if $a\le b$,

$$\gcd(a,b-a)=\gcd(a,b),$$

and the other case is symmetric. Since all other valuations are unchanged,
$G_p$ is invariant under every move.

At termination the board is

$$M,1,1,\ldots,1.$$

Its $p$-valuations are $v_p(M),0,0,\ldots,0$, whose gcd is $v_p(M)$. Therefore,
if the initial entries are $a_1,\ldots,a_{2026}$, then for every prime $p$,

$$v_p(M)=\gcd\bigl(v_p(a_1),\ldots,v_p(a_{2026})\bigr).$$

Hence the terminal value is forced to be

$$
\boxed{
M=\prod_p p^{\gcd_i v_p(a_i)}
},
$$

where only primes dividing the initial board product contribute. This formula
depends only on the initial entries, not on any choices made during the
process. Therefore $M$ is independent of Confucius's moves.

∎

## Verification status

The mathematical proof above is complete. The proof-search campaign has now
kernel-verified the prime-local identity

```lean
∀ a b : ℕ,
  Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b
```

as well as the valuation bridge, whole-multiset exponent-gcd preservation,
replacement-pair product lemma, move-local measure decrease, and
well-foundedness of the 2026-entry move relation. See
[`evidence.md`](evidence.md) for the tracked episode records. The
terminal-state and choice-independence assembly is now kernel-verified as one
faithful root theorem in [Final.lean](proof/Final.lean).
