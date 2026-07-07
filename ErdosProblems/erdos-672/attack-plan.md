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

## Honesty

This is **not yet proved**. It is an in-progress multi-session formalization of a
genuine hard theorem (Euler / Fermat descent), tracked here so progress is
resumable and the exact open obligation (M3) is explicit.
