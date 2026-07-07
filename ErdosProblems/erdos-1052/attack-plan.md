# Erdős #1052, the OPEN problem — attack plan

**The question (open since 1966):** are there only finitely many unitary
perfect numbers? Corpus statement:
`answer(sorry) ↔ {n | IsUnitaryPerfect n}.Finite`. Known unitary perfects —
exactly five discovered: 6, 60, 90, 87360, and Wall's
146361946186458562560000 (= 2¹⁸·3·5⁴·7·11·13·19·37·79·109·157·313).
Prize: $10. Open because it is hard, not because it is cheap.

## Honest position

Nobody — us included — should expect to resolve finiteness. The rational
"real shot" is the one research actually takes: **push the kernel-verified
boundary of what is PROVEN about unitary perfect numbers as far as our
machinery allows, and map the wall precisely.** Every milestone below is a
theorem, not a heuristic; each lands in this folder with a tracked episode.

## Milestones

**M1 — evenness (DONE).** `even_of_isUnitaryPerfect`, kernel_verified
pass@1 (this folder). The machinery built for it — one-prime peel-off +
p-free-part identification — is the recursion step for everything below.

**M2 — σ*-multiplicativity (DONE).** `sigmaStar_mul_of_coprime` — for
coprime `m, n`, `σ*(mn) = σ*(m)·σ*(n)` — proved directly via an explicit
divisor-splitting bijection (`gcd(d,m)·gcd(d,n) = d` for `d ∣ mn`, `m,n`
coprime), plus `sigmaStar_prime_pow` (`σ*(p^e) = p^e+1`). Built from scratch
— Mathlib has no unitary-divisor-sum machinery at all. Unlocks:
- **M2a (DONE)** — `isUnitaryPerfect_87360_fast`: `σ*(87360) = 2·87360`,
  proved in a handful of `rw` steps via `87360 = 2^6·3·5·7·13`. The corpus's
  own test (`isUnitaryPerfect_87360`) is disabled with `stop` as "too slow"
  via naive divisor enumeration — this replaces that with an
  exponentially-cheaper multiplicative computation, then reconnects to the
  corpus's exact `properUnitaryDivisors`-based statement shape
  (`isUnitaryPerfect_87360`, via the new `isUnitaryPerfect_of_sigmaStar`
  bridge lemma).
- **M2b (DONE)** — `isUnitaryPerfect_wall_fast`: same for Wall's 24-digit
  fifth unitary perfect number (`2^18·3·5^4·7·11·13·19·37·79·109·157·313`),
  which the corpus ships as a bare `sorry` with only an external,
  non-replaying `formal_proof` link. Now independently verified, matching
  the corpus's exact statement shape (`isUnitaryPerfect_wall`).

**M3 — structure theorems toward finiteness.**
- **M3a (DONE)** — `omega_odd_le_two_adic_add_one`: for a unitary perfect
  `n = 2^a·m` (`m` odd, `a ≥ 1`), the number of distinct odd prime factors
  of `m` is at most `a + 1`. Proved via 2-adic valuation comparison on both
  sides of `σ*(n) = 2n`, using a genuine new lemma
  (`two_pow_card_primeFactors_dvd_sigmaStar`: for any odd `m`,
  `2^(ω(m)) ∣ σ*(m)`, proved by strong induction peeling off one prime
  power at a time). **Honest caveat on what this bound is worth:** combined
  with Wall's real 1988 theorem (any sixth unitary perfect number needs
  ≥9 distinct odd prime factors — Wall, *"New unitary perfect numbers have
  at least nine odd components,"* Fibonacci Quarterly 26(4), 1988, MR
  0967649 — confirmed real via Mathematical Reviews/Zentralblatt, though we
  could not access the full 1988 proof text to reproduce his technique),
  this forces `a ≥ 8` for any sixth unitary perfect number: it must be
  divisible by `2^8 = 256`. That is real, if modest, new information — it
  narrows the search space — but nowhere close to finiteness.
- **M3b** — small non-divisibility facts from the literature (e.g. behavior
  mod 3) as far as they formalize cleanly. Not yet attempted.

**A dead end, disclosed.** While researching M3a's literature context, a
2026 arXiv preprint (*"Bounded-box reductions in the Subbarao–Warren
problem,"* claiming a much deeper partial result) was found, read in full,
and identified as very likely AI-fabricated — invented terminology
("3-Higgs primes" beyond the real, narrower "Higgs prime" concept),
zero independent footprint for its named author, and suspiciously precise
unverifiable computational claims, dressed in real citations (Zsigmodny,
Ford, Wall, Graham) as camouflage. It was discarded and not used for
anything in this attack plan. Recorded here so this mistake-avoided is
part of the audit trail, not silently dropped.

**M4 — the wall, mapped.** Finiteness itself requires mathematics that does
not exist yet (this is why it is open). The deliverable at the frontier is
an honest statement in the whitepaper of exactly which quantitative step
fails, with the formalized fences from M3 as the boundary markers.

## Ground rules

- Every claim kernel-verified (M2/M2a/M2b/M3a currently verified directly
  via `lake env lean`, not yet re-submitted through the tracked MCP
  episode pipeline — that re-submission is the next concrete step, so the
  hash-pinned audit trail catches up to what's already proven); partial
  results labeled partial (North-Star reporting discipline, issue #124).
- No upstream PRs until the maintainer says go.
- If at any point a genuinely novel bound emerges, it goes to independent
  review before any public claim.
