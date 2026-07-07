# Erdős bounty board — open, formalized, with prize money

Hunt list generated 2026-07-07 from `teorth/erdosproblems` `data/problems.yaml`
(status = open ∧ formalized = yes ∧ prize > 0), cross-checked against the
local `formal-conjectures/` clone (fork: origin `Mnehmos/formal-conjectures`,
upstream `google-deepmind/formal-conjectures`; gitignored in this repo).

**Toolchain note:** formal-conjectures pins lean4 **v4.27.0**; our lab runs
**v4.32.0-rc1 + mathlib@360da6fa**. Statements must be re-elaborated in our
toolchain per problem (the stage-1 calibration on erdos_1 confirmed this
works; expect occasional rename drift).

## The 30 targets

| # | Prize | Tags | Open stmts | File |
|---|------:|------|-----------:|------|
| 142 | $10,000 | additive combinatorics, APs | 4 | 70 ln |
| 3 | $5,000 | number theory, APs | 1 | 39 ln |
| 592 | $1,000 | set theory, ramsey | 1 | 42 ln |
| 30 | $1,000 | sidon sets | 1 | 44 ln |
| 20 | $1,000 | combinatorics | 1 | 66 ln |
| 1135 | $500 | number theory | 1 | 45 ln |
| 593 | $500 | hypergraph chromatic | 3 | 236 ln |
| 564 | $500 | hypergraph ramsey | 1 | 41 ln |
| 143 | $500 | primitive sets | 2 | 73 ln |
| 138 | $500 | additive combinatorics | 3 | 127 ln |
| 89 | $500 | geometry, distances | 1 | 91 ln |
| 74 | $500 | chromatic number, cycles | 2 | 139 ln |
| 66 | $500 | additive basis | 1 | 43 ln |
| 41 | $500 | sidon sets | 1 | 59 ln |
| 40 | $500 | additive basis | 1 | 96 ln |
| 39 | $500 | sidon sets | 1 | 42 ln |
| 28 | $500 | additive basis | 1 | 42 ln |
| 1 | $500 | additive combinatorics | 2 | 172 ln |
| 595 | $250 | graph + set theory | 1 | 246 ln |
| 126 | $250 | number theory | 2 | 71 ln |
| 123 | $250 | number theory | 2 | 115 ln |
| 52 | $250 | additive combinatorics | 1 | 40 ln |
| 50 | $250 | number theory | 1 | 79 ln |
| 241 | $100 | sidon sets | 2 | 105 ln |
| 120 | $100 | combinatorics | 1 | 55 ln |
| 119 | $100 | analysis, polynomials | 1 | 83 ln |
| 101 | $100 | geometry | 1 | 56 ln |
| 99 | $100 | geometry, distances | 1 | 51 ln |
| 1052 | $10 | number theory | 1 | 78 ln |
| 470 | $10 | number theory, divisors | 2 | 123 ln |

## Honest triage

These carry money because they are **hard research problems** — a cheap
bounty is not an easy problem (#470's $10 question, "are there odd weird
numbers?", has been open since 1974). Nobody should expect a direct kill.
The systems-rational lanes, in order:

**Lane 1 — solved-with-`sorry` statements inside bounty files (immediate wins).**
The corpus marks some variants `research solved` but ships no proof. Found in
this sweep:
- `#470 erdos_470.variants.weird_pos_density` — weird numbers have positive
  density (Benkoski–Erdős 1974); `sorry` in the corpus.
- ✅ **DONE** `#1052 even_of_isUnitaryPerfect` — unitary perfect numbers are
  even (Subbarao–Warren): **independent proof kernel-verified pass@1**
  through the tracked loop (2026-07-07; episode `2cc1e02a`, result
  `27534f5e`), hosted at `lean-checker/LeanChecker/Erdos/Erdos1052.lean`.
  Cross-check: the corpus's linked AlphaProof reference does NOT replay
  standalone (depends on formal-conjectures' custom `valid` tactic + older
  toolchain); ours is the reproducible artifact. Upstream `formal_proof`
  link PR: prepared on the fork.
Each is a genuine upstream contribution via the `@[formal_proof]` host
mechanism, and builds the exact machinery the parent bounty problem needs.

**Lane 2 — missing known-bounds variants (statement contributions).**
`#20` and `#30` carry literal `TODO: add the various known bounds as
variants` comments — upstreamable statement work that seeds later proofs.

**Lane 3 — finite/certificate sub-cases of the combinatorial targets.**
`#564` (hypergraph Ramsey lower bounds via explicit colourings — witness
constructions are certificate-shaped, our rung-1/2/4 ladder applies at small
scale), `#592`, `#241`/`#39`/`#41` (Sidon sets: finite instances are
`decide`/`bv_decide`-shaped). Named finite results here are publishable
variants even when the asymptotic question stays open.

**Flagships (context, not targets):** #142 ($10k, asymptotics of r_k(N)) and
#3 ($5k) sit on top of Kelley–Meka-scale mathematics. Track, don't attack.

## Standing rules

- Any claim follows the North-Star reporting discipline (#124): partial
  results labeled as exactly that; anything novel goes to independent review
  before any public claim.
- Upstream PRs disclose AI assistance; kernel verification is the
  "independently verified" evidence. CLA: signed (2026-07-07).
- Proofs > 25–50 lines stay in THIS repo (the proof host); upstream gets the
  statement + `@[formal_proof using lean4 at "<permalink>"]`.
