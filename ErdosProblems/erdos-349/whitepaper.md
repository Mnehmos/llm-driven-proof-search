# Erdős Problem #349 — Binary Expansion Lemma

**Problem folder whitepaper — 2026-07-07**

> **Status: Erdős Problem #349 is still OPEN.** For which `(t,α)` is
> `⌊tαⁿ⌋` additively complete — nobody has the general answer. This folder
> does not touch that question. It proves a **different, elementary,
> already-known** fact (binary expansion) that happens to sit in the same
> corpus file as scaffolding, not a step toward the open case.

## The problem

[erdosproblems.com/349](https://www.erdosproblems.com/349): for what values of
`t, α ∈ (0,∞)` is the sequence `⌊tαⁿ⌋` additively complete (every sufficiently
large integer is a sum of distinct terms)? **Open** in general — the corpus
has a full partial-characterization cluster for integer `(t, α)` pairs
(`integer_isGoodPair_iff`: the only good integer pair is `(1, 2)`, i.e. the
powers of two), each piece linked externally via `formal_proof` to a
different fork (`cepadugato/formal-conjectures`).

This folder does not attack the open problem. It proves the one lemma in
that cluster with no dependency on the others and no real content beyond
elementary number theory:

## What this folder proves (kernel-verified)

**Theorem (`exists_finset_sum_two_pow`).** *Every natural number `k` is a sum
of distinct powers of two: there is a finite set `E` of exponents with
`k = ∑_{i∈E} 2^i`.*

This is the binary-representation theorem — the fact that makes `(1, 2)` a
good pair in the first place (the powers of two additively generate every
positive integer). The corpus ships it with a `sorry` and a `formal_proof`
link to an external fork; this is an **independent** proof through our own
pipeline.

## Proof idea

Mathlib already has this fact in sharper, bijective form, built for an
unrelated purpose: `Finset.Colex` (the colexicographic order development
underlying the Kruskal–Katona theorem) defines `Nat.bitIndices n` — the list
of bit positions of `n` — and proves
`Finset.sum_toFinset_bitIndices_two_pow : ∑ i ∈ n.bitIndices.toFinset, 2^i = n`.
The existential is then one line:

```lean
theorem exists_finset_sum_two_pow (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩
```

No induction needed to be hand-written — the corpus's own docblock
describes an inductive proof ("subtract the largest power ≤ k, recurse on
the remainder"), but that induction is exactly what `Finset.Colex` already
did internally to prove the sharper bijective statement.

**The only real work was locating the lemma.** `Mathlib/Combinatorics/Colex.lean`
opens `namespace Finset`, then `namespace Colex` — but `Colex` closes with
`end Colex` *before* the `section Nat` containing this lemma opens. A
`section` (unlike a `namespace`) does not prefix declaration names, so the
lemma's true qualified name is `Finset.sum_toFinset_bitIndices_two_pow`, not
`Finset.Colex.sum_toFinset_bitIndices_two_pow` as the file's physical
nesting first suggests. Two failed `#check` probes before finding this.

## Verification record

| field | value |
|---|---|
| statement | `∀ (k : ℕ), ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i` |
| statement hash | `2328323a2b3bbeba5fa2318fbc84fd47675231f738edc38166e21687ced920ed` |
| suite / problem | `ErdosProblems-FormalConjectures` (`4c2b3e65…`) / `7c0c927c…` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| episode / result | `844e5846…` / `f6ed83a2…` — **kernel_verified, pass@1** |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

Full hash-chained ledger: [trace/trajectory.md](trace/trajectory.md).
Evidence detail: [evidence.md](evidence.md). Credit: [credit.md](credit.md).

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos349.lean
```

## Discovery method — a new lane

Unlike #1 (calibration) and #1052 (externally-suggested target), this
problem came from a **local corpus scan**: grep every `.lean` file in the
formal-conjectures clone for `research solved` theorems with `sorry`,
score by elementary-proof signals readable directly in the docstring (no
external fetch, no fidelity risk since the statement is already
community-vetted). ~691 hits scanned; this one's docstring said outright
*"Proved by strong induction... "* — an honest, low-effort, zero-risk
production lane. See [evidence.md](evidence.md) for the scan method and
[../shared/](../shared/) for cross-problem notes.
