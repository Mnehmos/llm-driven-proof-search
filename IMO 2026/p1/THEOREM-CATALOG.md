# IMO 2026 P1 — theorem catalog

Status vocabulary follows the Erdős campaign standard:

- **KERNEL VERIFIED:** the registered Lean proposition was accepted by the
  pinned kernel.
- **OPEN:** no accepted root proof exists.
- **CERTIFIED:** reserved for kernel verification plus verified statement
  fidelity. No target in this campaign currently has this status.

## Verified targets

| # | Target | Status | Attempts | Snapshot |
|---|---|---|---:|---|
| 1 | Exponent Euclidean-step gcd | **KERNEL VERIFIED** | 1 | [IMO2026P1_ExponentEuclidGcd.lean](proof/IMO2026P1_ExponentEuclidGcd.lean) |
| 2 | Replacement-pair product and lcm non-unit | **KERNEL VERIFIED** | 1 | [IMO2026P1_PairProduct.lean](proof/IMO2026P1_PairProduct.lean) |
| 3 | Bounded lexicographic measure encoding | **KERNEL VERIFIED** | 1 | [IMO2026P1_BoundedLexMeasure.lean](proof/IMO2026P1_BoundedLexMeasure.lean) |
| 4 | Integer factorization/valuation bridge | **KERNEL VERIFIED** | 1 | [IMO2026P1_MoveFactorization.lean](proof/IMO2026P1_MoveFactorization.lean) |
| 5 | Whole-multiset exponent-gcd preservation | **KERNEL VERIFIED** | 3 | [IMO2026P1_MultisetExponentGcd.lean](proof/IMO2026P1_MultisetExponentGcd.lean) |
| 6 | Move-local product/count decrease | **KERNEL VERIFIED** | 2 | [IMO2026P1_MoveLocalLexDecrease.lean](proof/IMO2026P1_MoveLocalLexDecrease.lean) |
| 7 | Well-foundedness of the 2026-entry move relation | **KERNEL VERIFIED** | 8 | [IMO2026P1_Termination.lean](proof/IMO2026P1_Termination.lean) |
| 8 | Faithful complete IMO P1 root | **KERNEL VERIFIED** | 6 | [Final.lean](proof/Final.lean) |

## Dependency DAG

```text
ExponentEuclidGcd ──► MultisetExponentGcd ──┐
MoveFactorization ───────────────────────────┤
                                            ├─► path invariant (OPEN)
PairProduct ────────► survivor preservation ┘

PairProduct ──► MoveLocalLexDecrease ──► Termination
BoundedLexMeasure ─────────────────────► Termination

Termination + terminal characterization + path invariant
  ──► complete parts (a) and (b) assembly (KERNEL VERIFIED)
```

## Open targets

No proof obligations remain. Independent fidelity review is still open, so the
correct status is kernel verified rather than certified.
