# Credit & disclosure — Erdős #647

> Last updated 2026-07-15. The global seventh-power density theorem is
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
- A complete public export archive for all 227 related episodes: 220
  kernel-verified successes and seven retained non-success histories.

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
- Hughes's 6.16×10¹⁷ exclusion is Hughes's computation, not ours.
- Theorem 2's mathematics and the density target are Hughes–Kitamura
  mathematics. Our contribution is the independent Lean reconstruction,
  truncation-gap diagnosis and repair, explicit constants, and final assembly.
- The 227 proof-search episodes have `fidelity_status = attested`: Lean checks
  project-authored formal statements, but this is not neutral-corpus
  certification. Kernel verification applies to 220 of those episodes; the
  other seven are retained as explicit negative or unfinished trajectories.
- The terminal density theorem is supported by a clean transitive source
  replay. It is not misrepresented as an additional standalone tracked
  episode.
- Full proof dossiers and structured trajectories are published deliberately.
  Attribution and fidelity metadata should remain attached to downstream use.
