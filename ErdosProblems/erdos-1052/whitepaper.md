# Erdős Problem #1052 — Unitary Perfect Numbers

**Problem folder whitepaper — 2026-07-07**

## The problem

[erdosproblems.com/1052](https://www.erdosproblems.com/1052): *are there only
finitely many unitary perfect numbers?* A **unitary divisor** of `n` is a
divisor `d` with `gcd(d, n/d) = 1`; `n` is **unitary perfect** when its
proper unitary divisors sum to `n` (equivalently `σ*(n) = 2n`). Exactly five
are known — 6, 60, 90, 87360, and Wall's
146361946186458562560000 = 2¹⁸·3·5⁴·7·11·13·19·37·79·109·157·313.
Finiteness has been **open since 1966**. Prize: $10.

## What this folder proves (kernel-verified)

**Theorem (Subbarao–Warren 1966).** *Every unitary perfect number is even.*

This is the problem's `research solved` companion statement, which the
canonical Lean corpus (google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1052.lean`) ships with a `sorry`. Our proof
is, to our knowledge, the **first standalone-reproducible Lean proof** of
the statement: the corpus's only prior artifact (AlphaProof-generated,
linked externally) depends on the corpus's custom tactic infrastructure
(e.g. the `valid` macro) and an older toolchain, and does not replay against
plain Mathlib. Ours does.

## Proof idea (one paragraph)

Write `σ*(n)` for the sum over ALL unitary divisors, so unitary perfect
means `σ*(n) = 2n`. At any prime `p ∣ n`, toggling the full `p`-part
`P = p^{ν_p(n)}` on and off is a bijection between the `p`-divisible and
`p`-free unitary divisors, giving the factorization
`σ*(n) = (1 + P) · σ*(m)` with `m` the `p`-free part. Suppose `n` odd and
unitary perfect: `σ*(n) = 2n ≡ 2 (mod 4)`. But `1 + P` is even (P odd), and
if `m > 1` then `σ*(m)` is **also** even — the involution `d ↦ m/d` has no
fixed point and pairs odd values, so the sum splits into even pairs. Two
even factors force `4 ∣ 2n`: contradiction. If `m = 1` then `n = P` is a
prime power and `σ*(n) = 1 + P = 2P` forces `P = 1`: also impossible. ∎

No general multiplicativity of `σ*` is needed — one peel-off plus one
involution. Full details and the failure log of the development are in
[proof-narrative.md](proof-narrative.md).

## Verification record

| field | value |
|---|---|
| statement (corpus defs inlined, definitional) | `∀ n, (∑ i ∈ {d ∈ Ico 1 n \| d ∣ n ∧ d.Coprime (n/d)}, i) = n ∧ 0 < n → Even n` |
| statement hash | `6ea8f9fe2ac827150c04fb425a963ec770d76c7cba34c7c2c2cbba7b238f3b27` |
| suite / problem | `ErdosProblems-FormalConjectures` (`4c2b3e65…`) / `0279379a…` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| episode / result | `2cc1e02a…` / `27534f5e…` — **kernel_verified, pass@1** |
| module_source_hash | `7d29ed5d2d8a8a1157d4c15262fe0da5137970c105c1a8788015f2ebeb567944` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

Full hash-chained ledger: [trace/trajectory.md](trace/trajectory.md).
Evidence detail: [evidence.md](evidence.md). Credit and disclosure:
[credit.md](credit.md).

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean
```

Exit 0 = Lean's kernel accepts every step. The snapshot in
[proof/](proof/) is byte-stamped by the `module_source_hash` above.

## The open problem: our attack

The finiteness question stays open — see [attack-plan.md](attack-plan.md)
for the staged, kernel-verified milestone program (σ*-multiplicativity;
machine-verifying Wall's 25-digit number, currently a corpus `sorry`;
the `ω_odd ≤ ν₂ + 1` structure bound; and an honest map of the wall).
