# Mathlib Gap Map — Erdős 888

## Available in Mathlib (confirmed via `mathlib_search_declarations`)

| Concept | Mathlib Module | Notes |
|---------|---------------|-------|
| `Squarefree` | `Algebra/Squarefree/Basic`, `Data/Nat/Squarefree` | Full API: multiplicativity, dvd, gcd, factorization |
| `squarefree_mul` | `Data/Nat/Squarefree` | Requires coprime |
| `Nat.factorization` | `Data/Nat/Factorization/*` | Full API with padicValNat |
| `Nat.Prime` | `Data/Nat/Prime` | Full API |
| `IsSquare` | `Algebra/Group/Even` | Definition + lemmas |
| `Asymptotics.IsTheta` (=Θ) | `Analysis/Asymptotics/Defs` | Full asymptotic notation |
| `Asymptotics.IsBigO`, `IsLittleO` | `Analysis/Asymptotics/*` | Full API |
| `Nat.sqrt` | `Data/Nat/Sqrt` | Integer sqrt |
| `Real.log` | `Analysis/SpecialFunctions/Pow` | Real log |
| `Real.sqrt` | `Analysis/Real/Sqrt` | Real sqrt |
| Finset API | `Data/Finset/*` | Full |
| `SimpleGraph` | `Combinatorics/SimpleGraph/*` | Graph theory framework |
| `Nat.findGreatest` | `Data/Nat/Basic` | Used in Formal Conjectures target |

## Partially Available / Needs Verification

| Concept | Status | Notes |
|---------|--------|-------|
| Prime-counting function π(x) | Unclear search | Search returned no `pi`-named theorem; may exist under `Nat.primes` |
| Chebyshev estimates | Only Chebyshev *polynomials* found | No `∏_{p≤x} p ≤ exp(Cx)` found in search |
| Mertens theorems | Not found in search | May exist under different name |
| Smooth numbers / ψ(x,y) | Not found | Likely absent |
| Colored KST / C4-free bounds | Not found | Must formalize |
| Landau semiprime asymptotic | Not found | Likely absent |
| Prime zeta sums Σ p^{-α} | Not found | Likely absent |

## Gap Analysis Summary

1. **Graph theory gap**: Mathlib has `SimpleGraph` framework but no C4-counting, KST, or bipartite extremal bounds. Phase 6 (ColoredKST) will be our largest reusable contribution to Lean graph theory.

2. **Analytic number theory gap**: Mertens estimates, prime sums, smooth-number estimates all appear absent or under-diff erent names. Existing campaign `erdos-647` built Mertens infrastructure; inspect for reusability. Landau's theorem is fully absent.

3. **Asymptotic notation available**: `IsTheta`, `IsBigO`, `IsLittleO` are well-developed. Final target uses `=Θ[atTop]`.

4. **Squarefree and factorization ready**: Full API available, including `Nat.squarefree_mul_iff` and `Nat.factorization`.
