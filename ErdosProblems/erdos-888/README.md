# Erdős Problem 888 — Square-Product Rigidity

## Status

| Item | Status |
|------|--------|
| Problem | Solved (GPT-5.5 Pro / Ulam AI) |
| Formalization target | Formal Conjectures `Erdos888.erdos_888` (statement only, proof `sorry`) |
| This campaign | Independent Lean 4 formalization and audit |
| Budget | $25 total model inference |
| Phase | 0 — Source audit and setup |

## The Problem

Let F(n) be the maximum cardinality of A ⊆ {1,...,n} such that, whenever
a ≤ b ≤ c ≤ d, a,b,c,d ∈ A, and abcd is a square, we have ad = bc.

**Asymptotic**: F(n) ≍ n log log n / log n

## Key References

- Main solution: [Ulam AI note (PDF)](erdos888.pdf)
- Erdős Problems page: [https://www.erdosproblems.com/888](https://www.erdosproblems.com/888)
- Discussion: [https://www.erdosproblems.com/forum/thread/888](https://www.erdosproblems.com/forum/thread/888)
- Formal Conjectures: [888.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/888.lean)
- Ulam/Aristotle Lean draft: [https://www.ulam.ai/research/erdos888.lean](https://www.ulam.ai/research/erdos888.lean)

## Campaign Structure

```
proof/
    Foundations.lean              — Definitions, F(n), G(n), A_k fibers
    LowerBoundRigidity.lean       — Rigidity of primes ∪ squarefree semiprimes
    SquarefreeReduction.lean      — F(n) ≤ Σ G(⌊n/k²⌋)
    LargestPrimeEncoding.lean     — a = cpq decomposition
    ColoredRectangle.lean         — No 2×2 rectangle in 2 colors
    ColoredKST.lean               — Colored Kővári–Sós–Turán
    DyadicSums.lean               — Lemma 2.2 and dyadic estimates
    NumberTheoryEstimates.lean    — π(x), Mertens, Landau
    SquarefreeUpperBound.lean     — G(n) ≪ n log log n / log n
    Main.lean                     — Final assembly
dossiers/
    prior-art.md
    source-map.md
    theorem-dag.md
    mathlib-gap-map.md
    formalization-walls.md
```

## Authors

- Paul Erdős, András Sárközy, Vera T. Sós (problem)
- Stijn Cambie, Desmond Weisenberg (lower bound observation)
- GPT-5.5 Pro, prompted by Przemek Chojecki (matching upper bound)
- Google DeepMind Formal Conjectures (formal statement)
- This campaign: independent kernel-checked formalization
