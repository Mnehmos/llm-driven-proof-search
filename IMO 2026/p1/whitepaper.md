# IMO 2026 Problem 1 — gcd/lcm blackboard process

**Problem-folder whitepaper — started 2026-07-16, LIVE campaign**

> **Status:** complete human proof and complete kernel-verified Lean root
> theorem. Development attestation is not certification of source-statement
> fidelity.

## The problem

Starting from 2026 integers greater than 1, replace selected `m,n>1` by

```text
gcd(m,n),  lcm(m,n) / gcd(m,n).
```

Prove that every play ends after finitely many moves with exactly one entry
`M>1`, and that `M` is independent of the choices. The faithful statement is
in [`problem.md`](problem.md).

## Mathematical proof architecture

Let `P` be the board product and `k` the number of entries greater than 1.
If `g=gcd(m,n)`, a move changes `P` to `P/g`.

- If `g=1`, the product is unchanged and `k` drops by one.
- If `g>1`, the product strictly decreases and `k` does not increase.

Thus `(P,k)` decreases lexicographically. The human proof uses the equivalent
positive-integer potential `P·2^k`; the Lean proof uses the bounded encoding
`P·2027+k`, since every board has 2026 entries.

For choice independence, fix a prime `p`. A selected valuation pair changes by

```text
(a,b) ↦ (min(a,b), max(a,b)-min(a,b)).
```

This is a subtractive Euclidean step and preserves the pair gcd. Hence the gcd
of all `p`-valuations on the board is invariant. At a terminal board
`{M,1,…,1}`, it equals `v_p(M)`, forcing

$$M=\prod_p p^{\gcd_i v_p(a_i)}.$$

The polished proof is [`solution.md`](solution.md).

## What is kernel-verified

The complete faithful root and seven component targets have outcome
`kernel_verified` in the proof-search ledger:

- scalar exponent gcd preservation;
- replacement-pair product and lcm positivity;
- bounded lexicographic measure encoding;
- integer factorization/valuation bridge;
- whole-multiset exponent-gcd preservation;
- move-local product/count decrease;
- well-foundedness of the 2026-entry multiset move relation.
- reachable terminal existence and singleton non-unit characterization;
- path-level prime invariance and equality of arbitrary terminal survivors.

Exact statements, hashes, IDs, attempts, and standalone exports are indexed by
[`THEOREM-CATALOG.md`](THEOREM-CATALOG.md) and [`evidence.md`](evidence.md).

The assembled result is [Final.lean](proof/Final.lean).

## Formalization choices and limits

The complete root models a board as a positive `Multiset ℕ` of cardinality
2026. Its move relation removes two distinct occurrences greater than 1 and
inserts the prescribed gcd and lcm/gcd values. Reverse-step well-foundedness
formalizes finite termination; reachable terminal existence plus the universal
singleton conclusion formalizes both parts of the problem.

All registrations used `unsafe_dev_attestation=true`. The kernel verdict proves
the registered Lean propositions; it does not independently establish that a
registered proposition is a faithful formalization of the English problem.

## Reproduce

The files under [`proof/`](proof/) are direct `proof_export(format="lean")`
outputs from the accepted episodes. Each is standalone and imports the same
Mathlib umbrella recorded by environment hash
`9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.
