# Erdős Problem #349 — the integer-characterization cluster (COMPLETE)

**Problem folder whitepaper — 2026-07-07**

> **Status: Erdős Problem #349 is still OPEN.** For which `(t,α)` is
> `⌊tαⁿ⌋` additively complete — nobody has the general answer, and this
> folder does not touch that question. What this folder *does* prove is a
> real, fully-scoped, already-known theorem that lives inside the same
> corpus file: `integer_isGoodPair_iff`, the complete characterization of
> which **integer** `(t,α)` pairs are good (only `(1,2)`). All seven
> theorems in the corpus's dependency chain toward that iff — four named
> component lemmas, one lemma they depend on, one extra result, and the
> final assembly itself — are now kernel-verified in this folder. See
> [attack-plan.md](attack-plan.md) for the full milestone history.

## The problem

[erdosproblems.com/349](https://www.erdosproblems.com/349): for what values of
`t, α ∈ (0,∞)` is the sequence `⌊tαⁿ⌋` additively complete (every sufficiently
large integer is a sum of distinct terms)? **Open** in general — but the
corpus has a full partial-characterization cluster for integer `(t, α)`
pairs (`integer_isGoodPair_iff`: the only good integer pair is `(1, 2)`, i.e.
the powers of two), each piece linked externally via `formal_proof` to a
different fork (`cepadugato/formal-conjectures`).

This folder does not attack the open problem. It reproduces, in standalone
Lean and with kernel verification, **seven** already-solved corpus theorems,
including the culminating `integer_isGoodPair_iff` itself:

## What this folder proves (all kernel-verified)

| theorem | what it says | role |
|---|---|---|
| `exists_finset_sum_two_pow` | every `k : ℕ` is a sum of distinct powers of two | used by `one_two_isGoodPair` |
| `one_two_isGoodPair` | `(1, 2)` is a good pair | assembly piece 1/4 |
| `alpha_le_one_not_isGoodPair` | for `0 < α ≤ 1`, no `t` makes `(t,α)` good | assembly piece 2/4 |
| `int_coeff_ge_two_not_isGoodPair` | for integer `t ≥ 2`, no integer `α` makes `(t,α)` good | assembly piece 3/4 |
| `alpha_gt_two_not_isGoodPair` | for `0 < t` and `2 < α`, `(t,α)` is not good | assembly piece 4/4 |
| `dyadic_two_isGoodPair` | `(1/2^k, 2)` is good for every `k` | extra result, not one of the four (1/2^k isn't an integer for k≥1) |
| **`integer_isGoodPair_iff`** | for integers `t,α ≥ 1`: `(t,α)` is good ⟺ `t=1 ∧ α=2` | **the theorem itself — assembles pieces 1–4** |

`integer_isGoodPair_iff` is a **real, complete, already-known theorem**
(proved by the corpus's external contributors — see the `formal_proof` link),
now independently reproduced end-to-end through this repository's own
kernel-gated pipeline. It settles the *integer* sub-case of Erdős #349 in
full. Full milestone history in [attack-plan.md](attack-plan.md); the
growth-gap proof narrative for piece 4 is
[alpha-gt-two-proof-sketch.md](alpha-gt-two-proof-sketch.md).

## Proof ideas (one paragraph each)

**`exists_finset_sum_two_pow`.** Mathlib already has this in sharper,
bijective form, built for an unrelated purpose: `Finset.Colex` (the
colexicographic order development underlying Kruskal–Katona) defines
`Nat.bitIndices n` and proves
`Finset.sum_toFinset_bitIndices_two_pow : ∑ i ∈ n.bitIndices.toFinset, 2^i = n`.
The existential is one line. (The only real work was locating the lemma's
true qualified name — `Mathlib/Combinatorics/Colex.lean` opens
`namespace Finset`, then `namespace Colex`, but `Colex` closes with `end Colex`
*before* the `section Nat` containing this lemma opens; a `section`, unlike a
`namespace`, doesn't prefix names, so the true name is
`Finset.sum_toFinset_bitIndices_two_pow`, not `Finset.Colex.…`.)

**`one_two_isGoodPair` / `dyadic_two_isGoodPair`.** Direct construction: given
a target `k`, take its binary expansion (via `exists_finset_sum_two_pow`) and
translate the exponent set into a subset of the actual term sequence. For the
dyadic family, index `n = m + k` makes the term exactly `2^m`, so the same
construction reaches every power of two regardless of `k`.

**`alpha_le_one_not_isGoodPair`.** For `0 < α ≤ 1`, every term `⌊tαⁿ⌋` lies in
the *fixed* finite window `[0, ⌊t⌋]` (since `αⁿ ≤ 1`), so every subset sum is
bounded by the constant `∑_{i ∈ [0,⌊t⌋]} i` — no sufficiently large integer
can ever be reached.

**`int_coeff_ge_two_not_isGoodPair`.** For integer `t ≥ 2` and any integer
`α`, every term `(t:ℝ)·(α:ℝ)ⁿ` is already an exact integer (`t·αⁿ`), so
`⌊t·αⁿ⌋ = t·αⁿ`, and every subset sum is a `t`-multiple — divisible by `t`.
But past any threshold `N`, `t·(|N|+1)+1` is both `≥ N` and `≡ 1 (mod t)`
(never a multiple of `t`, since `t ≥ 2`), so it can never be reached.

**`alpha_gt_two_not_isGoodPair`.** Let `a_n = ⌊tα^n⌋` and
`S_n = a_0 + ... + a_n`. For `α > 2`, a geometric-series bound gives
`S_n ≤ tα^(n+1)/(α-1)`, while `a_{n+1} > tα^(n+1)-1`; the difference tends
to infinity because the coefficient `(α-2)/(α-1)` is positive. For
arbitrarily large `n`, `a_{n+1} ≥ S_n + 2`, so `S_n + 1` is a large missed
integer: any subset using a later term is too large, and any subset using
only earlier terms is at most `S_n`.

**`integer_isGoodPair_iff`.** Case split on `α`: rule out `α = 1` via
`alpha_le_one_not_isGoodPair` and rule out `α > 2` via
`alpha_gt_two_not_isGoodPair`, leaving `α = 2`. Then rule out `t ≥ 2` via
`int_coeff_ge_two_not_isGoodPair`, leaving `t = 1`. The converse direction is
exactly `one_two_isGoodPair`. Mechanical once the four pieces exist — no new
mathematical content.

## Verification record

| theorem | statement hash | episode | result |
|---|---|---|---|
| `exists_finset_sum_two_pow` | `2328323a2b3b…` | `844e5846…` | `f6ed83a2…` |
| `int_coeff_ge_two_not_isGoodPair` | `444d78b6081a…` | `f447f17e…` | `ac1fe599…` |
| `alpha_le_one_not_isGoodPair` | `b2eb28f162b5…` | `6766c89d…` | `d8e57141…` |
| `one_two_isGoodPair` | `ec9344f81572…` | `0d2fa763…` | `685c12b8…` |
| `dyadic_two_isGoodPair` | `32303ccb359f…` | `130631aa…` | `a00f0171…` |
| `alpha_gt_two_not_isGoodPair` | `cbf2b02039d…` | `6c0babf6…` | `d986f456…` |
| **`integer_isGoodPair_iff`** | `a020861a7133…` | `4f28677b…` | `2635b554…` |

All seven: `formal_benchmark_hash_alignment` → `canonical_statement_hash_match`,
`kernel_verified`, suite `ErdosProblems-FormalConjectures` (`4c2b3e65…`),
run `575f57b1…`, toolchain lean4:v4.32.0-rc1 + mathlib@360da6fa. Six of seven
are pass@1; `alpha_gt_two_not_isGoodPair` is pass@3 after two
namespace-qualification repairs.

Full hash-chained ledger: [trace/trajectory.md](trace/trajectory.md).
Evidence detail (including two honestly-disclosed submission-format bugs
found and fixed mid-session): [evidence.md](evidence.md). Credit:
[credit.md](credit.md). Full milestone history: [attack-plan.md](attack-plan.md).

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos349.lean
```

## Discovery method — a new lane

Unlike #1 (calibration) and #1052 (externally-suggested target),
`exists_finset_sum_two_pow` came from a **local corpus scan**: grep every
`.lean` file in the formal-conjectures clone for `research solved` theorems
with `sorry`, score by elementary-proof signals readable directly in the
docstring (no external fetch, no fidelity risk since the statement is
already community-vetted). ~691 hits scanned; this one's docstring said
outright *"Proved by strong induction…"* The other theorems in this folder
were found by reading the **rest of the same corpus file** once the first
hit surfaced it — the natural next step once one theorem in a file is proven
is to check whether its neighbors form a real dependency chain, which here
they do (`integer_isGoodPair_iff`'s own docblock names its assembly pieces
explicitly). See [evidence.md](evidence.md) for the scan method and
[../shared/](../shared/) for cross-problem notes.
