# IMO 2026 P1 — Attack Plan & Solution Draft

**Status:** solved and fully formalized. The polished proof is in
[`solution.md`](solution.md); the kernel-verified complete root is
[`proof/Final.lean`](proof/Final.lean).

## Setup

Board = multiset $B$ of 2026 integers $\ge 2$. A move picks $m, n$ from two
positions with $m > 1$ and $n > 1$ and replaces them with

$$g = \gcd(m,n) \qquad \text{and} \qquad q = \frac{\operatorname{lcm}(m,n)}{\gcd(m,n)}.$$

Moves continue while two entries $> 1$ exist.

## The prime-local picture (engine of the whole problem)

Fix a prime $p$. Write $a = v_p(m)$, $b = v_p(n)$. Then

$$v_p(g) = \min(a,b), \qquad v_p(q) = \max(a,b) - \min(a,b).$$

So on the exponent vector of each prime, a move is exactly a **subtractive
Euclidean step** $(a, b) \mapsto (\min(a,b),\ \max(a,b) - \min(a,b))$, applied
independently for every prime, with all other board entries untouched.

## Part (a): termination + exactly one survivor

**Potential.** Let $P$ = product of all board entries, $k$ = number of entries
$> 1$, and $\Phi = P \cdot 2^k \in \mathbb{Z}_{\ge 1}$.

- Product of the new pair: $g \cdot q = \operatorname{lcm}(m,n) = mn/g$, so a
  move sends $P \mapsto P/g$ (an integer).
- **Case $g = 1$:** the new pair is $(1, mn)$ with $mn \ge 4$. $P$ is
  unchanged, $k$ drops by exactly 1. $\Phi \mapsto \Phi/2$.
- **Case $g \ge 2$:** $P \mapsto P/g \le P/2$, and $k$ never increases (two
  entries $> 1$ are replaced by at most two entries $> 1$). $\Phi$ shrinks by
  a factor $\ge 2$.

$\Phi$ is a strictly decreasing positive integer, so only finitely many moves
occur.

**At least one entry $> 1$ survives forever.** After any move the board product
is (product of untouched entries) $\cdot \operatorname{lcm}(m,n) \ge 1 \cdot
\max(m,n) \ge 2$. So $P \ge 2$ at every stage, hence some entry is $\ge 2$.

**Conclusion.** The process halts exactly when at most one entry is $> 1$;
since at least one entry is always $> 1$, the terminal board has **exactly
one** entry $M > 1$. $\blacksquare$

## Part (b): $M$ is choice-independent

For a prime $p$ let $V_p(B)$ be the multiset of valuations $\{v_p(x) : x \in
B\}$ and let

$$G_p(B) = \gcd\text{ of all elements of } V_p(B)$$

(with the conventions $\gcd(0, x) = x$; $G_p = 0$ iff $p$ divides no entry —
zero valuations are neutral, they do not force $G_p = 0$).

**Invariance.** A move changes $V_p$ only on the chosen pair:
$\{a, b\} \mapsto \{\min(a,b),\ \max(a,b)-\min(a,b)\}$, and

$$\gcd\bigl(\min(a,b),\ \max(a,b)-\min(a,b)\bigr) = \gcd(a, b)$$

(the subtractive-Euclid identity $\gcd(x, y-x) = \gcd(x,y)$). Hence $G_p(B)$
is invariant under every move, for every prime $p$.

**Reading off the terminal state.** At termination the board is
$\{M, 1, 1, \ldots, 1\}$, so $V_p = \{v_p(M), 0, \ldots, 0\}$ and $G_p =
v_p(M)$. Therefore, for every prime $p$,

$$v_p(M) = G_p(B_0) = \gcd\bigl(v_p(a_1), \ldots, v_p(a_{2026})\bigr),$$

where $a_1, \ldots, a_{2026}$ is the initial board. This determines $M$
completely:

$$\boxed{\,M = \prod_p p^{\gcd_i v_p(a_i)}\,}$$

independent of Confucius's choices. $\blacksquare$

Consistency check with (a): the initial entries are $\ge 2$, so some prime
divides some entry, so some $G_p \ge 1$ and the formula gives $M > 1$, matching
the survivor's existence.

Worked sanity examples (hand-checked): $\{2,3\} \to \{1,6\}$, $M = 6 =
2^{\gcd(1,0)} 3^{\gcd(0,1)}$. $\{4,8\}$: exponents $(2,3) \to (2,1) \to (1,1)
\to (1,0)$, $M = 2 = 2^{\gcd(2,3)}$. $\{4,4,2\}$: both orders of play end at
$M = 2 = 2^{\gcd(2,2,1)}$. $\{6,10\} \to \{2,15\} \to \{1,30\}$, $M = 30$.

## Formalization decomposition (atom ladder)

1. **exponent-euclid-gcd** — `∀ a b : ℕ, gcd (min a b) (max a b - min a b) = gcd a b`.
   **KERNEL-VERIFIED** on 2026-07-16; see
   [`evidence.md`](evidence.md). Pure ℕ arithmetic; the
   (b)-invariance engine.
2. **move-factorization** — **KERNEL-VERIFIED** move-local valuation bridge.
   For `m n ≠ 0`: `v_p (gcd m n) = min`, and since
   `gcd m n ∣ lcm m n`, `v_p (lcm m n / gcd m n) = max − min`. Bridges:
   `Nat.factorization_gcd`, `Nat.factorization_lcm`, factorization-of-division.
3. **pair-product** — **KERNEL-VERIFIED.**
   `gcd m n * (lcm m n / gcd m n) = lcm m n` and
   `lcm m n ≥ max m n ≥ 2` for `m, n ≥ 2` (survivor lemma).
4. **potential-drop** — **KERNEL-VERIFIED** using the Lean-friendly equivalent
   bounded measure $P\cdot2027+k$ and a move-local lexicographic decrease
   (case split on `gcd = 1`).
5. **board model** — the 2026-entry `Multiset ℕ` move relation and its
   well-foundedness are **KERNEL-VERIFIED**, including reachable terminal
   existence and singleton survivor characterization.
6. **per-prime invariant on boards** — the multiset gcd preservation atom and
   the integer valuation bridge are **KERNEL-VERIFIED**, including lifting
   along the reflexive-transitive closure.
7. **assembly** — terminal board = {M,1,…,1}; `v_p M = G_p(initial)`;
   `M = ∏ p ^ G_p` choice-free. **KERNEL-VERIFIED** in `Final.lean`.

Atoms 1–4 are self-contained arithmetic and go first. Atom 5 (well-founded
recursion over multiset moves) is the heaviest Lean lift; keep the measure
integer-valued to use `Nat.lt_wfRel`-style descent.

## Open items

- No mathematical or formal proof obligations remain.
- Independent statement-fidelity review remains optional future audit work.
