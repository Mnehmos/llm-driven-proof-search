# Erdős Problem #291 — denominators of harmonic numbers (part ii)

**Problem folder whitepaper — 2026-07-07**

> **Status: Erdős Problem #291 is still OPEN.** The open question (part i) asks
> whether `gcd(aₙ, Lₙ) = 1` for infinitely many `n`, where `Lₙ = lcm(1,…,n)`
> and `∑_{1≤k≤n} 1/k = aₙ/Lₙ`. This folder does **not** answer that. It proves
> the **different, already-known, easy** companion (part ii): `gcd(aₙ, Lₙ) > 1`
> for infinitely many `n` — an observation attributed to Steinerberger. The
> corpus ships this as `sorry`; this is a self-contained, kernel-verified Lean
> proof.

## The problem

[erdosproblems.com/291](https://www.erdosproblems.com/291). Let `Lₙ` be the
least common multiple of `{1,…,n}` and define `aₙ` by
`∑_{1≤k≤n} 1/k = aₙ/Lₙ`. The **open** question: is `(aₙ, Lₙ) = 1` for
infinitely many `n`? (Heuristics predict yes, with density zero, but no proof
is known.)

The **solved** companion (part ii): is `(aₙ, Lₙ) > 1` for infinitely many `n`?
Trivially yes — Steinerberger observed that any `n` beginning with a `2` in
base 3 has `3 ∣ (aₙ, Lₙ)`.

## What this folder proves (kernel-verified)

`Erdos291.infinite_gcd_gt_one : {n : ℕ | 1 < Nat.gcd (a n) (L n)}.Infinite`,
with `L`, `a` the corpus's own definitions (`L n = (Icc 1 n).lcm id`,
`a n = ∑_{k∈Icc 1 n} L n / k` — matched byte-for-byte and cross-checked against
the corpus's `L_eval`/`a_eval` test values by `decide`).

Also `erdos_291_parts_ii : True ↔ {n | Nat.gcd (a n) (L n) > 1}.Infinite`,
the corpus's exact statement shape (`answer(True)` elaborates to `True`).

## Proof idea (one paragraph)

Take the explicit family `n = 2·3ᵏ` (`k ≥ 1`), for which `v₃(Lₙ) = k`. In
`aₙ = ∑_{j=1}^{n} Lₙ/j`, a term `Lₙ/j` has 3-adic valuation
`v₃(Lₙ) − v₃(j) ≥ k − v₃(j)`, which is `≥ 1` — i.e. `3 ∣ Lₙ/j` — for every `j`
except those with `3ᵏ ∣ j`. The multiples of `3ᵏ` in `{1,…,2·3ᵏ}` are exactly
`3ᵏ` and `2·3ᵏ`. Writing `Lₙ = 2·3ᵏ·t` (valid since `2` and `3ᵏ` are coprime
and both divide `Lₙ`), those two surviving terms are `Lₙ/3ᵏ = 2t` and
`Lₙ/(2·3ᵏ) = t`, summing to `3t`. Hence `3 ∣ aₙ`. Also `3 ∣ Lₙ` (as `3 ≤ n`),
so `3 ∣ gcd(aₙ, Lₙ)` and the gcd exceeds `1`. The map `k ↦ 2·3^{k+1}` is
injective, so the set is infinite. ∎

Notably the proof needs only the **easy lower bound** `v₃(Lₙ) ≥ k` (from
`3ᵏ ∣ Lₙ`, immediate since `3ᵏ ∈ {1,…,n}`); it never needs the harder
lcm-valuation *upper* bound. Everything else is elementary divisibility and one
coprime-factorization step.

## What we did / did not prove

- **Did:** part (ii), `{n | gcd(aₙ,Lₙ) > 1}.Infinite`, kernel-verified, with an
  explicit construction (not the general Steinerberger congruence — a single
  clean infinite family suffices).
- **Did not:** the open part (i), `{n | gcd(aₙ,Lₙ) = 1}.Infinite`. Untouched.
  Nor the general `steinerberger_generalization`, `shiu_heuristic_*` variants.

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos291.lean
```

Exit 0 = Lean's kernel accepts every step. Snapshot:
[proof/Erdos291_infinite_gcd_gt_one.lean](proof/Erdos291_infinite_gcd_gt_one.lean).

Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`.
