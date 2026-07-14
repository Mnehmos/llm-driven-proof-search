# Attack Plan — Erdős 888 (living)

> Last updated 2026-07-14. This is the working plan of record.

## Dominant structure

The proof proceeds in ten layers:

1. **Foundations** — definitions, F(n), G(n), fibers, basic lemmas
2. **Lower bound construction** — primes ∪ semiprimes is rigid
3. **Squarefree reduction** — F(n) ≤ Σ G(⌊n/k²⌋)
4. **Two-largest-prime encoding** — a = c·p·q for squarefree a
5. **Colored rectangle obstruction** — no 2×2 rectangle in two colors
6. **Colored KST supersaturation** — total edge bound
7. **Dyadic summation** — analytic bound on sums
8. **Number-theoretic estimates** — π(x), Mertens, Landau
9. **Dyadic block sums** — S1, S2, S3
10. **Final assembly** — Θ theorem

## Current phase

Phase 0 (source audit) complete. Phase 1 (foundations) in progress.

## First Proof Search obligations

1. `squarefree_kernel_unique` — every integer has a unique squarefree-square decomposition
2. `fiber_admissible` — each A_k fiber inherits admissibility
3. `semiprime_set_rigid` — the lower bound set is admissible
4. `squarefree_reduction_bound` — F(n) ≤ Σ G(⌊n/k²⌋)
5. `two_largest_prime_factor_unique` — decomposition a = c·p·q

## Next actions

1. Create problem_version for each obligation
2. Submit via episode_step
3. Record in evidence.md
4. Update checkpoint.md after each 3 submissions