# Erdős #672 (Euler) — multi-session marathon attack plan

**Target (corpus `research solved`, shipped `sorry`):**
`erdos_672.variants.euler : Erdos672With 4 2` — the product of a 4-term
arithmetic progression `n, n+d, n+2d, n+3d` with `gcd(n,d)=1` is **never a
perfect square** (Euler).

This is a genuine Fermat-**descent** result. It is being built over multiple
sessions; this file is the resumable spec. Status markers: ☐ todo, ◐ in
progress, ☑ kernel-verified.

## Arithmetic core (the mathematical heart)

```
theorem euler_four_ap (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (q : ℕ) : n * (n + d) * (n + 2*d) * (n + 3*d) ≠ q ^ 2
```

Everything reduces to this. The corpus statement `Erdos672With 4 2` follows via
the bridge (M1).

## Backbone identities (☑ verified, `ring`)

- `P := n(n+d)(n+2d)(n+3d)`,  `A := n(n+3d)`,  `B := (n+d)(n+2d)`.
- `P = A · B`   and   `B = A + 2d²`.
- `P + d⁴ = X²` where `X := n²+3nd+d²`  ⟹  `P = X² − d⁴`.
- gcd: `gcd(n,d)=1 ⟹ gcd(A,d)=1` (since `A ≡ n² mod d`), hence
  `gcd(A,B) = gcd(A, 2d²) = gcd(A,2) ∈ {1,2}`.

## Proof strategy

`P = q²` with `X = n²+3nd+d²` gives `X² − q² = d⁴ = (d²)²`, i.e. `(X−q)(X+q) = d⁴`.
Using `gcd(X,d)=1` (so `gcd(X,q)=1`) the two factors are coprime (d odd) or share
only a factor 2 (d even); by `exists_eq_pow_of_mul_eq_pow` each is a 4th power,
`X−q=a⁴`, `X+q=b⁴`, `ab=d`. Then

- `(b²−a²)² = 2A = 2n(n+3d)` and `(a²+b²)² = 2B = 2(n+d)(n+2d)`.

Closing this is exactly Fermat's **"no four squares in arithmetic progression"**
= **`x⁴ − y⁴ ≠ z²`** (nonzero), the crux obligation below.

## Milestones

- **M0 ☑** Read defs; pin arithmetic core. Backbone identities verified.
- **M1 ☐** Bridge: `euler_four_ap` ⟹ corpus-shaped `Erdos672With 4 2`
  (`Set.IsAPOfLengthWith ↑s 4 n d` + `s.card=4` ⟹ `∏ i∈s = P`). Fiddly but
  routine (Set-builder unfolding, `Finset.coe_injective`, distinctness from
  `d>0`). Define local copies of `Set.IsAPOfLengthWith` / `Erdos672With`.
- **M2 ☑** Recon: Mathlib has `not_fermat_42` (`a⁴+b⁴≠c²`) and
  `PythagoreanTriple.coprime_classification` (primitive-triple parametrization),
  but **NOT** `x⁴−y⁴≠z²` nor "four squares in AP". The crux must be built.
- **M3 ☑ (CRUX) DONE** — `no_fermat_sub : ∀ a b c : ℤ, IsCoprime a b → b≠0 → c≠0
  → a⁴ ≠ b⁴ + c²`, kernel-verified (axioms `[propext, Classical.choice,
  Quot.sound]`), both descent cases complete. Built from three lemmas:
  `beven_factor` (square structure from `2mn=b²`), `beven_step` (second-level
  classification descent), and `no_fermat_sub` (strong induction on `a.natAbs`).
  The `b`-odd case descends via `a²b² = m⁴−n⁴`; the `b`-even case via the double
  classification landing on `u⁴ = v⁴ + n0²`. Original plan retained below.

- **M3 (original plan)** Prove `noFourthPowerDiffSq`: no positive `a,b,c` with
  `a⁴ = b⁴ + c²`, `gcd(a,b)=1`. By **strong induction on `a`** (infinite descent).
  Precise descent (worked out — execute this next session):

  `a⁴ = b⁴ + c²` ⟹ `(a²)² = (b²)² + c²` ⟹ `(b², c, a²)` is a Pythagorean triple.
  It's primitive: if a prime `p ∣ b²` and `p ∣ c` then `p ∣ a⁴` so `p ∣ a`,
  contradicting `gcd(a,b)=1`. Apply `PythagoreanTriple.coprime_classification`
  (over ℤ; cast up). Two parity cases for the leg `b²`:
  - **`b` odd** (`b² = m²−n²`, `c = 2mn`, `a² = m²+n²`, `gcd(m,n)=1`): then
    `b² = m²−n²` ⟹ `a²·b² = (m²+n²)(m²−n²) = m⁴ − n⁴`, i.e.
    **`m⁴ = n⁴ + (a·b)²`** — a *smaller* instance (`m ≤ a²` and in fact
    `m < a` since `a² = m²+n² > m²`), `gcd(m,n)=1`. Descent ⇒ contradiction.
  - **`b` even** (`b² = 2mn`, `a² = m²+n²`): `gcd(m,n)=1`, opposite parity, so
    exactly one of `m,n` even; from `2mn = b²` and coprimality get `m = 2e²`,
    `n = f²` (or swap), giving `a² = 4e⁴ + f⁴`, i.e. `(2e², f², a)` Pythagorean;
    re-apply classification to descend (the standard second-level case).

  Foundations available: `PythagoreanTriple.coprime_classification`,
  `exists_eq_pow_of_mul_eq_pow` (for `2mn = b²` ⟹ each factor a square),
  `Nat`/`Int` gcd + parity lemmas. ~120–180 lines. Do the `b`-odd descent first
  (it's the clean one); the `b`-even case is the fiddly second level.

  NOTE (worked out this session): the whole thing may be cleaner stated over ℤ
  as `a^4 = b^4 + c^2` with a well-founded measure `a.natAbs`, since
  `PythagoreanTriple` is ℤ-native.
- **M4 ◐** Reduce `euler_four_ap` to the (now-proved) crux `no_fermat_sub`.
  Structure worked out this session:
  - `P = q²`, `A·B = q²` with `A = n(n+3d)`, `B = (n+d)(n+2d)`, `gcd(A,B) ∣ 2`.
  - **Coprime case** (`gcd(A,B)=1`): `A, B` both squares (`exists_eq_pow_of_
    mul_eq_pow`). With `gcd(n,3)=1`: `n, n+3d` coprime ⟹ both squares; `n+d,
    n+2d` coprime ⟹ both squares. So `n=e², n+d=g², n+2d=h², n+3d=f²` — **four
    squares in AP**. Parametrizes as `h² = 2g² − e²`, `f² = 3g² − 2e²`.
  - **REMAINING sub-obligation**: connect "four squares in AP" to
    `no_fermat_sub` (`x⁴−y⁴≠z²`). This is Fermat's classical "square-area right
    triangle" reduction; the exact algebraic bridge (produce `a,b,c` with
    `a⁴=b⁴+c²` from `e,g,h,f`) needs to be reconstructed carefully — do NOT guess
    the identity. Also handle the `gcd(A,B)=2` and `gcd(n,3)=3` sub-cases (small
    factor pulled out, reducing to the same core).
  - Note: the crux `no_fermat_sub` is the hard 60% and is DONE; M4 is careful
    classical case-algebra on top of it.

  **M4 progress (kernel-verified reduction, 2 case-descents remain):**
  `euler_four_ap` now carries the verified reduction to two cases via the
  primitive Pythagorean triple `(q, d², X)`:
  - **case (i)** `d²=2MN`: `A=(M−N)²`, `B=(M+N)²` (both squares). Then `d=2uv`
    (since `2MN=d²`, `gcd(M,N)=1`, opp parity ⟹ `{M,N}={2u²,v²}` ⟹ `d=2uv`).
    With `gcd(n,3)=1`: four squares in AP `n=e², n+d=g², n+2d=h², n+3d=f²`.
    Algebraic leads (all `ring`-verifiable): `h⁴−e⁴ = 4d·g²`, `f⁴−g⁴ = 4d·h²`,
    so `(h⁴−e⁴)(f⁴−g⁴) = (4dgh)²`. If `d` were a perfect square, `h⁴−e⁴=(2g√d)²`
    gives a `no_fermat_sub` instance directly — but `d=2uv` isn't square in
    general, so either exploit the `d=2uv` structure or do a **direct infinite
    descent on the common difference** of the four-squares AP (the standard
    Fermat proof; reuse `PythagoreanTriple.coprime_classification`). Two
    Pythagorean triples arise: `((h+e)/2)²+((h−e)/2)²=g²` and
    `((f+g)/2)²+((f−g)/2)²=h²`, with `ps=rt` linking them (`p=(h+e)/2` etc.).
  - **case (ii)** `d²=M²−N²`: `A=2N²=n(n+3d)`, `B=2M²=(n+d)(n+2d)`. Note
    `N²+d²=M²` so `(N,d,M)` is a primitive Pythagorean triple. Needs its own
    2×-square-in-AP descent / sub-split on `gcd(n,3)` and parity of `n`.

  **M4 BOTTLENECK, exactly characterized (case i, `gcd(n,3)=1`):** with
  `d=2uv`, `n(n+3d)=(2u²−v²)²` is a quadratic in `n` whose discriminant is
  `4(u²+v²)(4u²+v²)` (ring-verified). So an integer `n` exists **iff
  `(u²+v²)(4u²+v²)` is a perfect square**, i.e. (when the two coprime factors,
  `gcd = gcd(3,u²+v²)`) **iff `u²+v²` and `4u²+v²` are BOTH perfect squares** —
  a *concordant forms* pair (`v²+u²=P²`, `v²+(2u)²=Q²`, two Pythagorean triples
  sharing leg `v`). This is smaller than `(n,d)`, so #672 ⟸ **"no nonzero `u,v`
  with `u²+v²` and `4u²+v²` both squares"**, a genuine congruent-number-style
  infinite descent. Mathlib has NO congruent-number theory, so this is a real
  multi-lemma formalization (the honest remaining wall). The crux `no_fermat_sub`
  is done; this concordant descent is the piece to build next (do NOT fabricate
  the descent step — derive it).
- **M5 ☐** Full file 0/0; erdos-672 docs; commit; track via MCP.

## Recon notes (Mathlib pins, mathlib@360da6fa)

- `not_fermat_42 {a b c : ℤ} (ha) (hb) : a^4 + b^4 ≠ c^2`  — plus-version only.
- `PythagoreanTriple.coprime_classification` — primitive triples
  `x=m²−n², y=2mn, z=±(m²+n²)`, `gcd(m,n)=1`, opposite parity.
- `exists_eq_pow_of_mul_eq_pow [CommMonoidWithZero][GCDMonoid][Subsingleton αˣ]`
  `: IsUnit (gcd a b) → a*b = c^k → ∃ d, a = d^k` (coprime factor is a k-th power).
- FLT4 (`Mathlib.NumberTheory.FLT.Four`) has an internal descent (`Minimal`,
  `not_minimal`) for `a⁴+b⁴=c²`; structurally analogous but not directly reusable
  for the minus case.

## Honesty — DEFINITIVE STATUS (2026-07-07, corrected)

**#672 is NOT closable by the `no_fermat_sub` crux. This corrects an earlier
over-claim that the crux was "the hard 60% of #672."**

Reference: Keith Conrad, *Arithmetic Progressions of Four Squares* and *Proofs by
Descent*. The facts, now definitive:

- #672 (product of a 4-term AP `=` square, coprime) **implies** "no four rational
  squares in arithmetic progression" (case (i) of our verified reduction lands
  exactly there), so #672 is **at least as hard** as that theorem.
- "No four rational squares in AP" ⟺ the elliptic curve `E : y² = x³ − x² − 4x + 4`
  (j-invariant `35152/9`) has **rank 0** (Conrad Thm 2.3, 3.4). Proved via
  Kolyvagin / `L(E,1) ≠ 0`, or Euler's intricate elementary descent on the pair
  `a²+c²=2b², b²+d²=2c²` (Euler 1780; Conrad does **not** reproduce the explicit
  descent — he uses the EC route).
- Our crux `no_fermat_sub` (`x⁴ − y⁴ ≠ z²`) ⟺ the **different** curve
  `y² = x³ − x` (j = 1728) has rank 0 (Conrad Cor 3.19). The two curves are
  **non-isogenous** (different j), so there is **no elementary reduction** from
  one rank-0 fact to the other. `no_fermat_sub` therefore cannot close #672.

**Consequence:** completing #672 requires either (a) formalizing Euler's
pair-descent — elementary but intricate, construction not readily available, a
fresh ~200-line high-risk effort; or (b) elliptic-curve rank machinery — Mathlib
has **no** congruent-number / rank theory for this curve. Both are large,
genuine projects, honestly out of reach as a "fill."

**What IS banked and correct:** `no_fermat_sub` = Fermat's `x⁴ − y⁴ ≠ z²`, a real
theorem NOT in Mathlib, kernel-verified. Its honest value is standalone (a
Mathlib-worthy companion to `not_fermat_42`), plus Conrad's corollaries
(triangular number = 4th power ⟹ 1; no Pythagorean triple with two square terms).
The verified `euler_four_ap` reduction (primitive Pythagorean triple `(q,d²,X)` →
the two cases) is also correct and reusable — it is just that its endpoint is the
hard four-squares curve, not `no_fermat_sub`.

This file's earlier "M4 reduces to the crux" plan was based on a false premise
(that four-squares-in-AP reduces to `x⁴−y⁴`). Kept above for the record with this
correction on top.
