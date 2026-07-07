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
- **M3 ☐ (CRUX)** Prove `noFourthPowerDiffSq : ∀ x y z : ℤ, 0<x → 0<y → x⁴ − y⁴ ≠ z²`
  (equivalently no 4 squares in AP), by infinite descent on `PythagoreanTriple.
  coprime_classification`. ~150–200 lines; the hard, multi-session part. This is
  Fermat's "right triangle with square area" theorem.
- **M4 ☐** Reduce `euler_four_ap` to M3 via the case analysis (gcd(A,B)∈{1,2},
  parity, `gcd(n,3)`), `exists_eq_pow_of_mul_eq_pow`, and the backbone identities.
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
