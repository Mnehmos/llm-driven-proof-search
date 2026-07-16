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
| [erdos-399/](erdos-399/whitepaper.md) | [#399](https://www.erdosproblems.com/399) — `n! = xᵏ ± yᵏ` solvable? **Resolved (Barfield, not by us).** | Not the headline. Cambie's **already-known companion**: `n! ≠ x⁴ + y⁴` for coprime `x,y` with `xy>1`, via a mod-8 fourth-power argument. Corpus ships it `sorry`; kernel-verified here. |
| [erdos-1113/](erdos-1113/whitepaper.md) | [#1113](https://www.erdosproblems.com/1113) — Sierpiński numbers with no finite covering set? **Open.** | Not the open question. The classical **solved companion** (Sierpiński 1960): there are **infinitely many Sierpiński numbers**, via Selfridge's `{3,5,7,13,19,37,73}` covering generalized across `k ≡ 78557 (mod M)`. Corpus ships it `sorry`; kernel-verified here with **pure `decide`** (no `native_decide` — stronger than the corpus's own `selfridge_78557`). |
| [erdos-494/](erdos-494/whitepaper.md) | [#494](https://www.erdosproblems.com/494) — is a set determined by its `k`-subset sums? | The **product** analogue is **false** (Steinerberger): distinct `A, B ⊆ ℂ`, same card, same multiset of 3-subset products — witness `A = {1,ω,ω²,2}`, `B = ω·A`, `ω³=1`. Corpus ships it `sorry`; kernel-verified here. |
| [erdos-647/](erdos-647/README.md) | [#647](https://www.erdosproblems.com/647) — is there `n>24` with `max_{m<n}(m+τ(m)) ≤ n+2`? **Open.** | The existence question remains open, but the effective global density theorem `|C(X)|≤KX/(log X)^7` is kernel-verified. The finite band `25≤n≤84` is now closed, and every remaining hypothetical candidate is formally above `84`, divisible by `2520`, and in one of the two four-prime families. The folder contains 106 Lean files with 239 theorem declarations and complete exports for 214 related episodes (207 kernel-verified; seven retained non-success histories). |

**In short: seven infra/companion-lemma wins (#1, #1052, #349, #291, #399,
#1113, #494), zero Erdős problems closed, one genuine sub-characterization
fully assembled (#349's integer case), and one open-problem campaign (#647)
that now includes both the replicated frontier/first formalization of its
Theorem 2 and a complete kernel-verified seventh-power density theorem. The
#647 existence question itself remains open.** If an open question is ever
actually closed here, it
will say so explicitly, in a table row of its own, not folded into this one.

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
