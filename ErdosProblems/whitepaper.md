# Verifier-Gated LLM Proof Search on the Erdős Problem Corpus

**Project index — 2026-07-07**
Repository: [Mnehmos/llm-driven-proof-search](https://github.com/Mnehmos/llm-driven-proof-search)

## Abstract

We describe a proof-search environment in which a large language model
proposes Lean 4 proofs but **never holds proof authority**: every claim is
settled by Lean's kernel, every statement is hash-pinned to its source, and
every attempt is recorded in a tamper-evident event ledger. This repository
is organized **one folder per Erdős problem**; each folder is a
self-contained deliverable — problem statement, proof (or attack plan if
open), machine evidence, hash-chained trace, and credit/disclosure. This
page is the index and the system-level report; problem-specific narrative
lives in each problem's own `whitepaper.md`.

## The trust design (applies to every problem folder)

- **Statement fidelity by hash.** A problem enters as an exact string; the
  server computes its hash; a proof is only accepted against that hash. The
  model cannot silently prove an easier statement.
- **Tracked episodes.** Attempts run in a claim/step loop with a
  hash-chained event ledger (`GENESIS → episode_created →
  action_committed → episode_terminated`); results cross-check the
  episode's actual recorded outcome.
- **Trust taxonomy.** Fidelity bases (canonical hash match vs. independent
  review vs. dev attestation) and a five-rung certificate ladder (kernel
  `decide` → verified-LRAT SAT → kernel-checked solver models → bounded
  UNSAT via verified LRAT → *bare solver output, never proof authority*)
  keep every claim labeled by what actually backs it.
- **Capability substrate.** Nine reusable Lean "kits" (geometry, affine
  areas, power series, convexity, arithmetic, certificates, extremal
  combinatorics, recurrences, inequalities), importable through hashed
  manifests.

## Problems in this repository

| Folder | Problem | Status | Result |
|---|---|---|---|
| [erdos-1/](erdos-1/whitepaper.md) | [#1](https://www.erdosproblems.com/1) — distinct subset sums | Open (calibration case study) | Weaker known bound independently proven; audit **MATCH** vs. proof on file |
| [erdos-1052/](erdos-1052/whitepaper.md) | [#1052](https://www.erdosproblems.com/1052) — unitary perfect numbers | Open (finiteness); companion theorem proven | First standalone-reproducible proof that unitary perfect numbers are even; staged attack plan for the open question |

## Cross-problem method: calibrate, then produce, then attack

1. **Calibrate** ([erdos-1/](erdos-1/whitepaper.md)) — verify the pipeline's
   "done" signal against an external artifact before trusting it on new
   material.
2. **Produce** ([erdos-1052/](erdos-1052/whitepaper.md)) — target the
   corpus's solved-but-unproven-in-Lean statements; ship the first
   standalone-reproducible proof.
3. **Attack** (in progress, see [erdos-1052/attack-plan.md](erdos-1052/attack-plan.md)) —
   push kernel-verified milestones toward a genuinely open question, with
   every partial result honestly labeled as partial.

## Honest limits (repository-wide)

- Proved theorems to date are **known mathematics**; the contribution is
  the formalization artifact and the audited pipeline, not new mathematics
  — until/unless a genuinely novel result emerges from the attack-plan work,
  which would go to independent review before any public claim.
- pass@1 = 1.0 across current results reflects heavy *local pre-validation*
  before tracked attempts (every proof compiled locally first); the tracked
  pipeline measures end-to-end integrity, not zero-shot model skill.
- Cross-problem infrastructure notes: [shared/](shared/) (corpus survey,
  bounty-board triage, run-level machine evidence, the disclosure rationale
  for publishing full proof bodies).

## Reproduce anything in this repository

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean          # erdos-1052's proof
lake env lean LeanChecker/Erdos/CorpusValidation.lean    # EGZ/EKR/perfect validations
lake env lean LeanChecker/Erdos/OpenStatements.lean      # open statements (sorry warnings expected)
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`. Per-problem
`proof/` snapshots are byte-stamped by hashes in each problem's `trace/`;
the living, CI-built copies are under `lean-checker/LeanChecker/Erdos/`.
