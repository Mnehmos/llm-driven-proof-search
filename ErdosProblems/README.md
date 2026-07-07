# ErdosProblems — one folder per problem

Organized **by problem**: each Erdős problem this project has touched gets
its own self-contained folder with proof, evidence, credit, and a
problem-specific whitepaper. Start with the **[project index](whitepaper.md)**.

## Layout

```
ErdosProblems/
├── whitepaper.md          project-level index + system-wide trust design
├── README.md               this file
├── erdos-1/                Erdős Problem #1 (calibration case study)
│   ├── whitepaper.md       problem statement, proof idea, verification record
│   ├── credit.md           attribution: math, catalog, corpus, this proof
│   ├── evidence.md         machine records (result row, episode summary)
│   ├── proof/              snapshot .lean, byte-stamped by module_source_hash
│   └── trace/              hash-chained episode ledger
├── erdos-1052/             Erdős Problem #1052 (unitary perfect numbers)
│   ├── whitepaper.md
│   ├── credit.md
│   ├── evidence.md
│   ├── proof-narrative.md  how the proof was found, incl. round-1 failures
│   ├── attack-plan.md      staged milestones toward the OPEN question
│   ├── proof/
│   └── trace/
├── erdos-349/              Erdős Problem #349 (binary expansion lemma)
│   ├── whitepaper.md
│   ├── credit.md
│   ├── evidence.md         includes the local-corpus-scan discovery method
│   ├── proof/
│   └── trace/
└── shared/                 cross-problem infrastructure notes
    ├── corpus-validation.md
    ├── bounty-board.md
    ├── run-575f57b1-summary.md
    └── disclosure-note.md
```

Adding a new problem: copy the `erdos-1052/` shape (whitepaper, credit,
evidence, proof/, trace/; add `proof-narrative.md`/`attack-plan.md` only if
relevant) into a new `erdos-<N>/` folder and link it from the project index.

## Headline results

1. **Calibration MATCH** ([erdos-1/](erdos-1/whitepaper.md)) — an
   independently written proof agrees with the corpus's proof on file, on
   the byte-identical statement, under one verifier.
2. **Unitary perfect numbers are even** ([erdos-1052/](erdos-1052/whitepaper.md),
   Subbarao–Warren 1966): first standalone-reproducible Lean proof — the
   statement ships as `sorry` in google-deepmind/formal-conjectures, and
   the only prior linked proof does not replay outside its home
   infrastructure.

## Verify it yourself

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean
```

Exit 0 = Lean's kernel accepts every step. No trust in the authors required.

## Status of open problems

Neither #1 nor #1052 is resolved by this repository. #1052's staged attack
(σ*-multiplicativity, the corpus's missing 25-digit verification, a
`ω_odd ≤ ν₂+1` structure bound, then an honest map of the wall) is in
[erdos-1052/attack-plan.md](erdos-1052/attack-plan.md) and is actively
worked.

## Upstream

An upstream contribution branch (`erdos-1052-formal-proof-link` on the
Mnehmos fork of formal-conjectures, adding a `@[formal_proof]` link) is
**staged but deliberately not opened** — maintainer's call, on hold while we
take a real shot at the problem itself.
