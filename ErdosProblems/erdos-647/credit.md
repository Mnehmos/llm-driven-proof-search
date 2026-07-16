# Credit & disclosure — Erdős #647

> Last updated 2026-07-16. The global seventh-power density theorem is
> kernel-verified; the original existence problem remains open.

## Mathematics

- **Problem:** Erdős #647 (Erdős–Selfridge, ~1979), catalogued by Thomas Bloom
  at [erdosproblems.com/647](https://www.erdosproblems.com/647).
- **Scott Hughes**
  ([erdos647-proof-chain](https://github.com/scottdhughes/erdos647-proof-chain)):
  Stage-1 modular reduction, the 41-residue frontier, the finite exclusion to
  6.16×10¹⁷, the direct-full-value and single-overlap techniques, Theorem 2's
  statement and sketch, the all-avoid obstruction, and—with Kitamura—the
  seventh-power density program.
- **Kenta Kitamura:** necessary prime-shift conditions and co-development of
  the prime-seven-tuple/Brun-sieve direction.
- **Patrik Idén:** independent computation to 10¹², depth records, and
  gap-growth analysis.
- **Mathlib contributors:** the abstract `BoundingSieve`/`SelbergSieve`
  framework and supporting number-theory/analysis library used here.

## This folder's contributions

- Independent rederivation and kernel verification of the modular reduction,
  using a tighter 48-survivor base sieve and a proof-producing bridge from
  every shift classification to its sieve row.
- Fresh Lean proofs of four residue closures, reaching the 41-class frontier,
  plus 48 previously unrecorded sub-AP closures.
- What we believe is the first machine-checked proof of Hughes's Theorem 2;
  corrections or earlier references are welcome.
- Extension of the all-avoid negative argument to Theorem-2 chain forms
  (currently prose rather than a terminal Lean theorem).
- A concrete seven-dimensional Selberg upper-bound sieve for
  `{210N−1,315N−1,420N−1,630N−1,840N−1,1260N−1,2520N−1}`.
- Discovery and repair of an integration gap: Mathlib's
  `SelbergSieve.level` does not itself truncate `lambdaSquared`. The
  campaign constructs an explicit level-truncated optimal weight, proves
  support above `R²` vanishes, and obtains `errSum≤(R²+1)^8`.
- An exact Mertens-style identity and effective Chebyshev bounds. These are
  valid infrastructure, but their `log 2` coefficient is explicitly not used
  to claim seventh-power growth.
- An elementary factorial/Euler-product denominator proof yielding
  `(16/77)^7(log z)^7≤L`, explicit dyadic parameter certification, and
  finite-range closure.
- The global theorem `|C(X)|≤K·X/(log X)^7` for every natural `X`, with
  explicit effective `K`.
- Exact post-density interfaces: full maximum iff all shift budgets, certified
  closure of `25≤n≤84`, the `n>84`/`2520∣n`/prime-family reduction, and a
  short-window iff fixed-depth-shift adapter.
- Exact shift-9/shift-10 residue and parity sharpening, together with
  kernel-verified seven-prime consistency witnesses surviving through shifts
  10 and 12. These witnesses identify the next fixed-depth obstruction; they
  are not candidates for the original problem.
- A first shift-13 refinement: at most three distinct prime factors, exclusion
  of the primes dividing `2520`, and an exact first 13-adic split that reduces
  the nonexceptional cofactor to at most seven divisors and two prime factors.
- A reusable seven-theorem shift-factor/adic induction framework: generic
  coprime and prime-power budget peeling, cofactor prime-factor control, and
  exact conversion of the next `p`-adic layer to a modular exceptional class.
  Shifts 14–16 are recorded as 7-adic, 5-adic, and family-sensitive 2-adic
  stress tests of that framework—not as a claim that isolated shift
  accumulation will solve the problem.
- Exact interfaces for the variants: the limit statement is equivalent to an
  eventual arbitrarily large shift excess, while prime powers prove only
  sparse unboundedness; window size three is exactly the Sophie Germain prime
  infinitude problem.
- A generic rough `r`-power divisor theorem and four local-factor product
  theorems, including an exact integral numerator/denominator formulation.
- Generic power-prefix and excess-shift bridges, including a corollary stated
  with the exact Formal Conjectures candidate expression.
- Exact `gcd(k,2520)` transport and class-sensitive cube constants at
  `2,3,5,7`, replacing a uniform worst-case prefix coefficient.
- An exact arbitrary-block equivalence reindexing every positive shift into a
  unique block/rung cell.
- An executable, kernel-sound prime-power factorization batch format and an
  end-to-end theorem converting complete prefix coverage into the candidate
  predicate.
- Conditional pairwise-coprime novelty and shared-host accumulation theorems,
  isolating the hypotheses still needed by the growing-gauntlet lane.
- A smooth-number large-factor alternative and exact shift-difference
  non-reuse theorem. Together they turn a sufficiently large block of
  budgeted shifts into an injective family of primes larger than the block
  width, including a scalar endpoint interface and the quantitative
  `(W+1)^W` shared-host bound.
- The first concrete cross-rung factor non-reuse theorem: the exact relation
  `5(504N-1)-7(360N-1)=2` and parity imply that the rung-5 and rung-7 values
  are coprime for every positive `N`.
- The complete four-rung extension: the reduced cofactors at shifts
  `5,7,9,10` are pairwise coprime by six explicit positive Bézout identities,
  so every positive parameter supplies four pairwise distinct shifted-value
  prime factors; the associated rung-5 and rung-10 5-adic depths cannot both
  be positive.
- General `t`-subset product selection and an exact CRT re-entry certificate:
  whenever a selected prime product lies below `n`, its residue supplies a
  new shift with the kernel-checked sandwich
  `2^|I| ≤ τ(n-h) ≤ h+2`. The complementary product-large branch is retained
  explicitly rather than assumed away.
- A conditional second-layer cofactor catalog. After at most one square-scale
  exception and one nonsmooth-cofactor exception, at least `W-2` coordinates
  have positive proper coprime cofactors with `q²<n`, all prime factors at
  most `W`, and `q≤W^((1+i)/2)`. Large primes selected from those cofactors
  obey the same shift-gap injectivity law. These are structural reductions,
  not a contradiction.
- The explicit global bound `τ(n)^4≤19680n` and its fourth-root candidate
  prefix.
- A complete public export archive for all 321 related episodes: 314
  kernel-verified successes and seven retained non-success histories.
- The final checkpoint contains 172 Lean files with 456 actual theorem
  declarations and five lemma declarations (461 theorem/lemma declarations
  total).

## Tools and authorship

- Proofs and assembly were authored through LLM agents (Claude/Anthropic and
  Codex/OpenAI) in the verifier-gated proof-search environment built by
  **Mnehmos**; Mnehmos supplied direction, review, and publication decisions.
- Formal claims are checked by the Lean 4 kernel against pinned Mathlib. Model
  prose, human confidence, numerical experiments, and literature summaries do
  not substitute for kernel evidence.
- Computational searches were used to locate fixed-depth witnesses. The
  published Lean witnesses recheck explicit factorizations, divisor counts,
  and primality claims in the kernel; larger scan-range observations remain
  search guidance and are not promoted to theorems.
- Mid-campaign errors and corrections—including the inert-level diagnosis and
  the insufficient Mertens coefficient—are retained in the record rather than
  silently rewritten away.

## Honest limits

- **Erdős #647 remains open.** The density theorem neither constructs a larger
  candidate nor proves the candidate set empty.
- The three research statements in the Formal Conjectures module remain
  explicit `sorry`s. The new fixed-depth witnesses and variant equivalences
  sharpen what those obligations require; none is presented as a replacement
  for an open theorem.
- The power-prefix theorems reduce verification for each fixed `n` to a
  finite growing prefix; they do not give a uniform proof for all `n`.
- Coordinate injectivity alone is not prime-factor novelty. The newer
  large-factor theorem does prove prime novelty once every selected factor is
  larger than the block width, but its power-escape or second-layer catalog
  hypotheses have not been derived uniformly from every hypothetical
  candidate. CRT re-entry likewise requires a nontrivial selected product
  below `n`; only singleton availability is automatic.
- The factorization checker is a proof-producing verifier for supplied data,
  not evidence that a suitable candidate exists.
- Formal Conjectures closure status remains **0 of 3**: none of the original
  research `sorry` declarations is replaced by this batch.
- Hughes's 6.16×10¹⁷ exclusion is Hughes's computation, not ours.
- Theorem 2's mathematics and the density target are Hughes–Kitamura
  mathematics. Our contribution is the independent Lean reconstruction,
  truncation-gap diagnosis and repair, explicit constants, and final assembly.
- The 321 proof-search episodes have `fidelity_status = attested`: Lean checks
  project-authored formal statements, but this is not neutral-corpus
  certification. Kernel verification applies to 312 of those episodes; the
  other seven are retained as explicit negative or unfinished trajectories.
- The terminal density theorem is supported by a clean transitive source
  replay. It is not misrepresented as an additional standalone tracked
  episode.
- Full proof dossiers and structured trajectories are published deliberately.
  Attribution and fidelity metadata should remain attached to downstream use.
