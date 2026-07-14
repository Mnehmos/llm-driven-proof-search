# Prior Art — Erdős 888

## Mathematical History

- **Problem**: Paul Erdős, András Sárközy, Vera T. Sós (1980s/1990s)
- **Sárközy's bound**: |A| = o(n) (Erdős claims; proof by Terence Tao in forum using Turán–Kubilius + multiplication table)
- **Lower bound observation**: Primes only → |A| ≫ n/log n. Stijn Cambie and Desmond Weisenberg noted squarefree semiprimes also admissible, giving (1+o(1))·n·log log n / log n
- **Matching upper bound**: GPT-5.5 Pro (prompted by Przemek Chojecki), published at Ulam AI. Proof verified by Nat Sothanaphan via standard check. Thomas Bloom provides structural commentary connecting to Erdős [Er68] multiplicative Sidon technique.

## Prior Formalization Attempts

### Google DeepMind Formal Conjectures
- File: `FormalConjectures/ErdosProblems/888.lean`
- Status: Statement definitions only, all theorems `sorry`
- Target: `erdos_888 : (fun n ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop] (fun n ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n)`
- This is the public formalization target our campaign must match

### Ulam / Aristotle Formalization
- File: `erdos888.lean` (available at ulam.ai)
- Author: Przemek Chojecki (GPT-5.5 Pro with Aristotle)
- Status: Incomplete — analytic/Mertens-type estimates unfinished
- Strengths:
  - Core definitions (`SquareProductRigid`, `sqProdRigidMax`, `lowerBoundSet`)
  - Rigidity of lowerBoundSet proved (exhaustive case analysis via factorization)
  - `squarefree_two_factor_rigid` theorem proved
  - `squarefree_reduction` lemma partially written
  - Uses `Nat.factorization` for ad=bc equality
- Weaknesses:
  - Heavy use of `grind`/`aesop`/`omega` — possibly fragile
  - No formalization of colored KST supersaturation
  - No analytic estimates (Mertens, Landau, dyadic sums)
  - File truncated in our fetch — `squarefree_reduction` incomplete

## Known Invalid Approaches

1. **Global kernel reduction** (Masty13's attempt): Replacing A by squarefree kernels globally fails because removing square parts changes ordering and admissibility does not transfer. Detected and reported by Nat Sothanaphan via ChatGPT verification.

2. **Exact finite maximum claimed** (arturgoulao/GPT attempt): Claiming max = π(n) + #{pq ≤ n} + 1_{n≤14} is false — products of 7+ disjoint primes can be added for large n (Stijn Cambie's observation).

## Infrastructure from Prior Campaign (erdos-647)

The erdos-647 campaign built significant Lean infrastructure:
- Quantitative Mertens assembly (kernel-verified)
- Chebyshev estimates (theta_ge bridging)
- Selberg weight optimization
- Moebius swap-and-reindex
These may be partially reusable for Phase 8 number-theoretic estimates.
