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

**None of these Erdős problems have been solved by us.** Every one is still
listed OPEN on erdosproblems.com, unchanged. Each folder proves a
*different, already-known* companion fact that happens to live in the same
corpus file — a supporting lemma some human mathematician already solved
(sometimes decades ago), which had no Lean proof yet. That distinction is
the whole point of the two right-hand columns below: they never describe
the same thing.

| Folder | Erdős problem (upstream status) | What we actually proved |
|---|---|---|
| [erdos-1/](erdos-1/whitepaper.md) | [#1](https://www.erdosproblems.com/1) — distinct subset sums. **Open.** | Not #1 itself. A weaker, already-known bound from the same file, independently reproven; used as a calibration audit (**MATCH** vs. the proof already on file) — this folder is about testing our pipeline, not the problem. |
| [erdos-1052/](erdos-1052/whitepaper.md) | [#1052](https://www.erdosproblems.com/1052) — are there finitely many unitary perfect numbers? **Open.** | Not #1052 itself. A companion theorem (Subbarao–Warren 1966: unitary perfect numbers are even) — known math since 1966, first standalone-reproducible *Lean* proof of it. A staged attack plan targets further companion facts, not the open question itself. |
| [erdos-349/](erdos-349/whitepaper.md) | [#349](https://www.erdosproblems.com/349) — for which `(t,α)` is `⌊tαⁿ⌋` additively complete? **Open.** | Not #349 itself. The binary-expansion theorem (elementary, classical) — a supporting fact in the same file, explaining why `(1,2)` is a "good pair," closed with a one-line Mathlib corollary. |

**In short: three infra/companion-lemma wins, zero Erdős problems closed.**
If that ever changes for a genuinely open question, it will say so
explicitly, in a table row of its own, not folded into this one.

## Cross-problem method: calibrate, then produce, then attack

1. **Calibrate** ([erdos-1/](erdos-1/whitepaper.md)) — verify the pipeline's
   "done" signal against an external artifact before trusting it on new
   material.
2. **Produce** ([erdos-1052/](erdos-1052/whitepaper.md),
   [erdos-349/](erdos-349/whitepaper.md)) — target the corpus's
   solved-but-unproven-in-Lean statements. #1052 came from an
   externally-suggested target; #349 came from a **local corpus scan**
   (grep every `research solved` + `sorry` theorem in the formal-conjectures
   clone, score by elementary-proof signals in the docstring — zero
   external-fetch risk, ~691 candidates found). Both ship the first
   standalone-reproducible proof of their statement.
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
