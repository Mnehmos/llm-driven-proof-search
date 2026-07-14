# Source Map — Erdős 888

## Source Documents

| Source | URL | Format | Status |
|--------|-----|--------|--------|
| Ulam proof note (paper) | `erdos888.pdf` | PDF | Local copy exists |
| Erdős Problems page | https://www.erdosproblems.com/888 | HTML | Fetched |
| Forum discussion | https://www.erdosproblems.com/forum/thread/888 | HTML | Fetched |
| Formal Conjectures | https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/888.lean | Lean | Statement only, proof `sorry` |
| Ulam/Aristotle draft | https://www.ulam.ai/research/erdos888.lean | Lean | Fetched, incomplete (analytic estimates unfinished) |

## Key Observations from Source Review

### From the Ulam paper (erdos888.pdf):
The proof architecture is:
1. Arbitrary admissible sets → decompose by fixed square part (k²)
2. Squarefree admissible sets → encode each element by its two largest prime factors
3. Colored bipartite graphs → Kővári–Sós–Turán supersaturation
4. Dyadic summation → final asymptotic

### From the Forum Discussion:
- **Sárközy's o(n) result**: Proof supplied by Terence Tao using Turán–Kubilius + multiplication table
- **Lower bound**: Stijn Cambie / Desmond Weisenberg observed semiprime construction gives n·log log n / log n
- **Matching upper bound**: GPT-5.5 Pro, prompted by Przemek Chojecki
- **Tao's comment** on [Er68] technique: C4-free bipartite graph bound via Cauchy-Schwarz is a natural ancestor
- **Warning**: Early AI attempts using global kernel reduction are invalid (Nat Sothanaphan's verification)
- **Formalization status**: Ulam's Aristotle formalization incomplete — Mertens-type and other analytic estimates unresolved

### From the Formal Conjectures file:
- Target: `erdos_888 : (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n)`
- Two variants: `sarkozy` (o(n)) and `primes` (≫ n/log n), `semiprimes` (≫ n·log log n / log n)
- All are `sorry`

### From the Ulam/Aristotle Lean Draft:
- Very extensive file (~12000+ bytes truncated)
- Defines `SquareProductRigid`, `sqProdRigidMax`, `lowerBoundSet`
- Proves `lowerBoundSet_rigid` via exhaustive case analysis (4 primes, 2+2, 4 semiprimes)
- Contains the core `squarefree_two_factor_rigid` theorem
- Uses `Nat.factorization` for ad=bc equality via factorization matching
- `squarefree_reduction` lemma is partially written (truncated in fetch)
- Relies on machinery like `no_extremes_share_prime`, `no_middles_share_prime`
- Many lemmas use `grind`, `aesop`, `omega` heavily — likely fragile
