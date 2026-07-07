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

**M2 — σ*-multiplicativity, the keystone.** Prove
`σ*(n) = ∏_{p ∈ n.primeFactors} (1 + p^{ν_p(n)})` by strong induction on
`n`, iterating the already-proven peel-off (`sum_uDiv_factor` +
`filter_not_dvd_eq_uDiv_ordCompl` recursing on `ordCompl`, which strictly
decreases). Unlocks:
- **M2a** — verify `IsUnitaryPerfect 87360` *fast* (the corpus's own test is
  disabled with "too slow"; the product formula makes it `norm_num`-sized).
- **M2b** — verify Wall's 25-digit fifth unitary perfect, which the corpus
  ships as a bare `sorry`. Enumeration is hopeless; the product formula
  reduces it to checking one factorization and a product identity. A real,
  visible contribution nobody has in Lean.

**M3 — structure theorems toward finiteness.** With M2, in a unitary
perfect `n = 2^a·m` (`m` odd, `a ≥ 1` by M1): `σ*(n) = (1+2^a)·∏(1+pᵢ^{aᵢ})
= 2^{a+1}·m'`. Since `1+2^a` is odd and each odd factor `1+pᵢ^{aᵢ}` is even:
- **M3a** — `ω_odd(n) ≤ a + 1`: the number of distinct odd primes is at most
  the 2-adic budget. Clean, provable with M2 + 2-adic valuation counting.
- **M3b** — small non-divisibility facts from the literature (e.g. behavior
  mod 3) as far as they formalize cleanly.
These are the actual known fences around the problem; having them
kernel-verified is the state of the art in formalized territory.

**M4 — the wall, mapped.** Finiteness itself requires mathematics that does
not exist yet (this is why it is open). The deliverable at the frontier is
an honest statement in the whitepaper of exactly which quantitative step
fails, with the formalized fences from M3 as the boundary markers.

## Ground rules

- Every claim kernel-verified through the tracked pipeline; partial results
  labeled partial (North-Star reporting discipline, issue #124).
- No upstream PRs until the maintainer says go.
- If at any point a genuinely novel bound emerges, it goes to independent
  review before any public claim.
