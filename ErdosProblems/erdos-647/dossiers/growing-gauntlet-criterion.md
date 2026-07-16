# Erdős #647 — the growing-gauntlet criterion (theory run, priority 4)

Working formulation, 2026-07-16. Builds on the three kernel-verified
theory-run theorems (`erdos647_budget_transfer`,
`erdos647_shift7_adic_classification`,
`erdos647_gauntlet_pairwise_coprime`) and the failure audit
(`sqrt-prefix-failure-audit.md`). This document states the criterion and
its honest limits; it is a research plan, not a proof.

## The rung anatomy (all formal pieces exist)

For any shift `k ≤ 2520` and `n = 2520N`, with `g = gcd(2520, k)`:

```
n − k = g · (c·N − k')        where c = 2520/g, k' = k/g
```

(the fixed-factor peel formula, being tracked as
`erdos647_shift_fixed_factor_peel`). The budget-transfer theorem then
gives, whenever the full fixed part `f` (i.e. `g` together with any
`p`-adic layers the cofactor contributes at primes of `k'`) is coprime
to the remaining cofactor `m`:

```
τ(m) ≤ (B + k) / τ(f).
```

## The criterion

A shift `k ≤ D` is an **independent low-divisor rung at threshold T** if:

1. **Demand**: `(B + k) / τ(f_k) ≤ T` — the transferred budget forces
   `τ(m_k) ≤ T` (for `T = 3` this is a near-prime demand, `T = 4`
   admits semiprimes). At `B = 2` and `T = 4`, this requires
   `τ(f_k) ≥ (k+2)/4`, which for the plain peel `f_k = g` holds only for
   finitely many `k` — the fixed part grows like a divisor function of
   `k` while the budget grows linearly. **This is the precise reason the
   base gauntlet is the finite set {5, 7, 9, 10, 11} (+ deeper adic
   accidents) and why "prove the fixed gauntlet impossible" is the wrong
   target: at any fixed threshold, only finitely many rungs qualify, and
   a finite family of near-prime demands is prime-tuple-hard to refute.**
2. **Independence**: for every previously selected rung `j`, the
   cofactor pair determinant `c_j·k'_k − c_k·k'_j` has all its prime
   factors absorbed by coefficients (the ten-pair coprimality theorem is
   the base-block instance; the affine determinant lemma
   `erdos647_affine_determinant_interaction` decides each new pair
   mechanically).

## What grows, if not the rung count at fixed threshold

The escape from the finite-set trap is to let the **threshold grow with
k**: every rung `k` demands `τ(m_k) ≤ B + k` (trivially from the budget,
no peel needed), and the *content* of the demand degrades gracefully —
`τ(m) ≤ B + k` for `m ≈ 2520N` is restrictive as long as
`B + k ≪ τ_typical(m) · (spread)`. The accumulation theorem must
therefore not count rungs at a fixed threshold, but weigh each rung's
demand:

```
Σ_{k ≤ D} [structure forced at rung k]  vs  [total structure available in N]
```

with the host-boundedness correction already recorded: forced structure
only accumulates against a contradiction when it lands in a SHARED
bounded host. The pairwise-coprimality theorem is what BLOCKS the naive
shared host (the rung cofactors are disjoint); therefore the shared host
must be `N` itself, through the branch parameterizations:

- rung 5 at 5-adic depth `a` forces `N ≡ r_a (mod 5^a)` — consuming
  5-adic digits of N;
- rung 7 at 7-adic depth `a'` forces `N ≡ r'_{a'} (mod 7^{a'})`;
- the audit shows these depths distribute geometrically (~1/5, ~1/7 per
  level), and `AdicSpineTermination` bounds each spine by its budget.

**Candidate accumulation statement (next formal target):** for a
survivor to depth D with excess B, the total adic depth consumed across
the gauntlet primes is bounded by the budgets
(`Σ_p a_p ≤ f(B, gauntlet)`), while each rung escape at bounded adic
depth forces a fresh near-prime demand on a form coprime to all previous
forms. The recurrence is then: bounded adic escape ⟹ near-prime demand
⟹ next rung, with no factor reuse — the formal shape of "escaping one
early failure mechanism forces entry into another".

## Honest status

- Formally banked: rung anatomy (peel + transfer + adic classification
  for 5/7/9/10-analogues + pairwise coprimality).
- Open (research): the weighing function that makes the accumulation
  count beat the CRT/prime-tuple escape. No claim that it exists at
  currently accessible depth; the frontier search continues to supply
  record survivors as stress tests for any proposed bound.
