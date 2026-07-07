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
| [erdos-1052/](erdos-1052/whitepaper.md) | [#1052](https://www.erdosproblems.com/1052) — are there finitely many unitary perfect numbers? **Open.** | Not #1052 itself. A companion theorem (Subbarao–Warren 1966: unitary perfect numbers are even), plus new work: `σ*` multiplicativity (not previously in Mathlib), fast verification of two corpus test numbers the corpus leaves disabled/unproven, and a structural bound that — combined with a real 1988 theorem of Wall's — forces any undiscovered 6th unitary perfect number to be divisible by 256. Real but modest; not a resolution. |
| [erdos-349/](erdos-349/whitepaper.md) | [#349](https://www.erdosproblems.com/349) — for which `(t,α)` is `⌊tαⁿ⌋` additively complete? **Open.** | Not #349 itself. Seven already-known theorems from the same file: four named component lemmas plus the corpus's own `integer_isGoodPair_iff` itself — the complete, already-solved characterization of the *integer* sub-case — fully assembled and kernel-verified. |
| [erdos-291/](erdos-291/whitepaper.md) | [#291](https://www.erdosproblems.com/291) — is `gcd(aₙ,Lₙ)=1` (harmonic-number denominators) infinitely often? **Open.** | Not #291 itself (part i, the `=1` question, is open). The **easy solved companion** (part ii): `gcd(aₙ,Lₙ) > 1` infinitely often (Steinerberger), via the explicit family `n=2·3ᵏ`. Corpus ships it `sorry`; kernel-verified here. |

**In short: four infra/companion-lemma wins (#1, #1052, #349, #291), zero Erdős
problems closed, one genuine sub-characterization fully assembled (#349's
integer case: `integer_isGoodPair_iff`, all four pieces plus the final iff,
kernel-verified end to end).** If that ever changes for a genuinely open
question, it will say so explicitly, in a table row of its own, not folded
into this one.

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
   external-fetch risk, ~691 candidates found). Both ship standalone,
   reproducible Lean proofs of their recorded statements.
3. **Attack** (in progress for #1052, see
   [erdos-1052/attack-plan.md](erdos-1052/attack-plan.md); complete for #349,
   see [erdos-349/attack-plan.md](erdos-349/attack-plan.md)) — push
   kernel-verified milestones toward a genuinely open question (#1052) or a
   well-scoped already-solved sub-characterization within one (#349), with
   every partial result honestly labeled as partial. #349's sub-target,
   `integer_isGoodPair_iff`, reached full assembly this session.

## Honest limits (repository-wide)

- Proved theorems to date are **known mathematics**; the contribution is
  the formalization artifact and the audited pipeline, not new mathematics
  — until/unless a genuinely novel result emerges from the attack-plan work,
  which would go to independent review before any public claim.
- Most current results were pass@1 after local pre-validation; the newest
  #349 growth-gap theorem was pass@3 because two tracked namespace
  qualification repairs were preserved in the ledger. The tracked pipeline
  measures end-to-end integrity, not zero-shot model skill.
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
