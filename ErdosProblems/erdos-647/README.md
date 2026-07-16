# Erdős #647 — global density theorem verified; existence problem open

**Problem ([erdosproblems.com/647](https://www.erdosproblems.com/647),
Erdős–Selfridge, OPEN):** is there any `n > 24` with
`max_{m<n}(m + τ(m)) ≤ n + 2`?

This folder contains a complete Lean proof of the effective global density
estimate

```text
|C(X)| ≤ K · X / (log X)^7
```

for the bounded set of Erdős #647 candidates, with an explicit constant `K`.
It also contains an independent machine-checked rederivation of the modular
frontier, what we believe is the first machine-checked proof of Hughes's
Theorem 2, the repaired level-truncated Selberg machinery, and the complete
candidate-to-sieve assembly.

**The original problem remains open.** Density zero does not imply emptiness.
The active continuation now targets individual candidates: a kernel-verified
[shift-depth interface](proof/Erdos647_ShiftDepthInterface.lean) reduces
nonexistence to finding one failed budget `σ₀(n-k)>k+2` for each `n>24`.

## Start here

| file | what it is |
|---|---|
| [whitepaper.md](whitepaper.md) | full problem narrative and completed density proof architecture |
| [THEOREM-CATALOG.md](THEOREM-CATALOG.md) | theorem inventory and final assembly map |
| [attack-plan.md](attack-plan.md) | completed density program and remaining existence directions |
| [evidence.md](evidence.md) | tracked episode evidence plus the clean repository replay |
| [dossiers/](dossiers/README.md) | complete 211-episode export archive and indexes |
| [credit.md](credit.md) | attribution, AI disclosure, and honest limits |
| [proof/](proof/) | 102 Lean files containing 223 top-level theorem declarations |

## Headline results — 2026-07-15

1. **Global seventh-power density theorem.**
   [`boundedCandidates_density_global`](proof/Erdos647_ConcreteAsymptoticDensity.lean)
   proves the displayed bound for every natural `X`. The proof includes the
   bounded candidate `Finset`, exact `n=2520N` reindexing, concrete
   seven-form sieve, truncated optimal weights, polynomial error control,
   denominator growth, dyadic parameters, and finite-range closure.

2. **The analytic obstruction was repaired explicitly.** Hard support
   `d≤R` gives `lambdaSquared(w)(d)=0` above `R²`; the coefficient and
   remainder bounds give `errSum≤(R²+1)^8`. The final seventh-power
   denominator uses an elementary factorial/Euler-product comparison. The
   earlier valid Chebyshev/Mertens theorem has leading coefficient `log 2`
   and is not used to overclaim the exponent.

3. **Hughes's Theorem 2 formalized.** Every candidate lies in one of two exact
   four-prime constellations. The three stages are
   [Stage 1/2](proof/Erdos647_Thm2_Stage12.lean),
   [Stage 4](proof/Erdos647_Thm2_Stage4.lean), and
   [Stage 8](proof/Erdos647_Thm2_Stage8.lean).

4. **Independent frontier replication.** The 41 open residue classes modulo
   46189 were reproduced from scratch using a tighter 48-survivor base sieve,
   with every sieve row derived from a classification theorem.

5. **Forty-eight new sub-AP closures.** This line was deliberately frozen once
   the all-avoid obstruction showed that bounded congruence trees cannot close
   the frontier.

6. **Complete machine export archive.** All 211 related episodes
   are exported in redacted JSON, full Markdown dossier, and structured
   training JSON forms under
   [dossiers/exports/](dossiers/exports/README.md). Of these, 204 report
   `KERNEL_VERIFIED`; the archive deliberately retains three unfinished,
   three gave-up, and one budget-exhausted trajectory for audit completeness.
   The terminal composition is separately identified as a clean source replay
   rather than invented as an additional tracked episode.

7. **Existence campaign restarted.** `SurvivesThrough n D` packages the
   first `D` shift budgets. The global candidate condition implies survival
   through every depth, while any one failed budget rules it out. This is the
   formal handoff to a growing-depth obstruction or direct prime-chain
   contradiction; it is not itself a solution of the open problem.

8. **Formal Conjectures predicate compatibility checked.**
   [`Erdos647_FormalConjecturesCompatibility.lean`](proof/Erdos647_FormalConjecturesCompatibility.lean)
   mirrors the exact open-file expression, proves the candidate predicates
   definitionally equivalent, proves the bounded Finsets extensionally equal,
   and restates the density theorem over that exact set. The Formal Conjectures
   module independently compiles the matching API in its own pinned toolchain.
   This compatibility result fills none of its three research-open `sorry`s.

## Verification snapshot

- Pinned environment:
  `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- Complete density dependency replay: 42 modules plus
  `proof/campaign/family2-classifications.lean`, exit code 0
- No `sorry`, `admit`, or added axiom in the final assembly
- Generated `.olean` files are not committed

No new witness and no disproof are claimed. What changed is substantial but
logically different: the full `X/(log X)^7` density theorem is now
machine-checked.
