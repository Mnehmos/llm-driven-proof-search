# Erdős Problem #1113 — infinitely many Sierpiński numbers

**Problem folder whitepaper — 2026-07-07**

> A **Sierpiński number** is a positive odd `k` such that `k·2ⁿ + 1` is
> composite for every `n`. Sierpiński (1960) proved there are **infinitely
> many**; the corpus (`FormalConjectures/ErdosProblems/1113.lean`) ships this
> `research solved` statement as `sorry`. This folder gives a self-contained,
> **purely kernel-verified** Lean proof (no `native_decide`).
>
> The *open* Erdős #1113 — do there exist Sierpiński numbers with **no** finite
> covering set? — is untouched. This is the classical solved companion in the
> same file, not the open question.

## What this folder proves

`Erdos1113.infinitely_many_sierpinski : Set.Infinite {k : ℕ | IsSierpinskiNumber k}`,
where `Composite` and `IsSierpinskiNumber` are byte-for-byte the corpus /
`FormalConjecturesForMathlib` definitions:
`Composite n := 1 < n ∧ ¬ n.Prime`,
`IsSierpinskiNumber k := ¬ 2 ∣ k ∧ ∀ n, Composite (k·2ⁿ+1)`.

## Proof idea (one paragraph)

Selfridge's covering set `P = {3,5,7,13,19,37,73}` works for `78557`: every
`78557·2ⁿ+1` is divisible by some `p ∈ P`. This is a finite check on `n mod 36`,
valid because `2³⁶ ≡ 1 (mod p)` for each `p ∈ P` (their orders of 2 are
`2,4,3,12,18,36,9`, all dividing 36). The key generalization: every `p ∈ P`
divides `M = 3·5·7·13·19·37·73 = 70050435`, so **any** `k ≡ 78557 (mod M)`
satisfies `k·2ⁿ+1 ≡ 78557·2ⁿ+1 (mod p)` — the *same* covering makes every
`k·2ⁿ+1` composite (divisible by `p ≤ 73 < k·2ⁿ+1`). The arithmetic progression
`k = 78557 + j·(2M)` (`j ∈ ℕ`) stays odd and stays `≡ 78557 (mod M)`, and
`j ↦ 78557 + j·2M` is injective — so infinitely many `k` are Sierpiński. ∎

## Why this is stronger than the corpus's own `selfridge_78557`

The corpus proves `Nat.IsSierpinskiNumber 78557` (a single number) via
`native_decide`, which trusts the compiler (`Lean.ofReduceBool`). Our proof
discharges the finite covering checks with kernel `decide` instead, so

```
#print axioms Erdos1113.infinitely_many_sierpinski
-- [propext, Classical.choice, Quot.sound]
```

— only the standard Mathlib axioms, no `ofReduceBool`. So this folder both
strengthens the single-number result to *infinitely many* **and** removes the
compiler-trust dependency.

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1113.lean
```

Exit 0, **0 errors / 0 warnings**. Snapshot:
[proof/Erdos1113_infinitely_many_sierpinski.lean](proof/Erdos1113_infinitely_many_sierpinski.lean)
(sha256 `a484532165643ae4b2479cb9c0047e450d9a78cb6e3cc60cfd964a9e0061b078`).
Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`.
