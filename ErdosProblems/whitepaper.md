# Verifier-Gated LLM Proof Search on the Erdős Problem Corpus

**A systems report — 2026-07-07**
Repository: [Mnehmos/llm-driven-proof-search](https://github.com/Mnehmos/llm-driven-proof-search)

## Abstract

We describe a proof-search environment in which a large language model
proposes Lean 4 proofs but **never holds proof authority**: every claim is
settled by Lean's kernel, every statement is hash-pinned to its source, and
every attempt is recorded in a tamper-evident event ledger. Against the
Erdős problem corpus (erdosproblems.com; Lean statements in
google-deepmind/formal-conjectures) the system passed a calibration audit —
an independently written proof agreeing with a reference proof on file, on
the byte-identical statement — and then produced the first
standalone-reproducible formal proof of the Subbarao–Warren theorem
(*unitary perfect numbers are even*), a `research solved` corpus statement
previously carrying only a `sorry` and a non-portable machine-generated
external link. Both results verified on the first tracked attempt
(pass@1 = 1.0 for the run).

## 1. The trust problem

LLMs produce plausible-looking proofs; plausibility is not correctness. Our
design premise: the model's output is *untrusted input* to a pipeline whose
only arbiter is the Lean kernel (the same small checker that validates all
of Mathlib). Concretely:

- **Statement fidelity by hash.** A problem enters as an exact string;
  the server computes its hash; a proof is only accepted against that hash
  (`formal_benchmark_hash_alignment` against a registered corpus target).
  The model cannot silently prove an easier statement.
- **Tracked episodes.** Attempts run in a claim/step loop with a hash-chained
  event ledger (`GENESIS → episode_created → action_committed →
  episode_terminated`); results cross-check the episode's actual recorded
  outcome — a result cannot claim what the ledger doesn't back.
- **Trust taxonomy.** Fidelity bases (canonical hash match vs. independent
  review vs. dev attestation) and a five-rung certificate ladder (kernel
  `decide` → verified-LRAT SAT → kernel-checked solver models → bounded
  UNSAT via verified LRAT → *bare solver output, never proof authority*)
  keep every claim labeled by what actually backs it.
- **Capability substrate.** Nine reusable Lean "kits" (geometry, affine
  areas, power series, convexity, arithmetic, certificates, extremal
  combinatorics, recurrences, inequalities), importable through hashed
  manifests; demonstrated results include R(3,3) = 6 with the upper bound
  by external SAT + formally verified LRAT replay, and pigeonhole UNSAT at
  2²⁰ with zero kernel enumeration.

## 2. Method: calibrate, then produce

**Stage 1 — calibration.** Before trusting the pipeline on new material,
verify that "our tool says done" matches an external artifact. Target:
`erdos_1.variants.weaker` (Erdős's counting bound for distinct-subset-sum
sets) — one of the few corpus entries with a complete proof on file. The
reference compiled unmodified in our pinned toolchain; our independently
written proof (different constant, different structure) went through the
tracked loop and was kernel-verified on the identical statement hash
(`6d9502df…`). **Verdict: MATCH** — two implementations, one spec, one
checker, both green. (Disclosure: the reference was inspected during target
selection; the audit certifies the pipeline, not proof originality.)

**Stage 2 — production.** Target the corpus's *solved-but-unproven-in-Lean*
statements. First result: `even_of_isUnitaryPerfect` (Erdős #1052's solved
variant). Our proof avoids heavyweight multiplicativity machinery: the
unitary-divisor sum factors at one prime via a toggle bijection,
`σ*(n) = (1 + p^{ν_p(n)}) · σ*(p\text{-free part})`; for odd `n` the second
factor is even by a fixed-point-free involution pairing odd divisor values
(`d ↦ m/d`), so `4 ∣ σ*(n) = 2n` — contradiction. ~250 lines, Mathlib-only,
kernel-verified pass@1 (episode `2cc1e02a`, statement hash `6ea8f9fe…`).

**Cross-check finding.** The corpus's only prior proof artifact for this
statement (AlphaProof-generated, linked from the corpus) fails to replay
outside its home infrastructure: it depends on custom tactics (e.g.
`valid`) and an older toolchain. Our artifact replays against plain
Mathlib. Reproducibility of formal proofs is not automatic — portability
across toolchains is a property that must be engineered, and standalone
Mathlib-only proofs are the robust currency.

## 3. Results

| Result | Statement source | Outcome | Attempt |
|---|---|---|---|
| Calibration: distinct-subset-sums bound | formal-conjectures `1.lean` (proof on file) | kernel_verified, audit MATCH | pass@1 |
| **Unitary perfect ⇒ even** (Subbarao–Warren) | formal-conjectures `1052.lean` (`sorry`) | kernel_verified, first standalone-reproducible Lean proof | pass@1 |
| EGZ n=2, n=3 finite instances; EGZ general; Erdős–Ko–Rado; perfect 6/28 via kit bridges | corpus / Mathlib | kernel_verified (environment + kit validation) | — |
| Erdős–Straus, Erdős #1, Erdős–Turán basis | — | faithful open statements (typecheck, `sorry`) | — |

Run metrics (suite `ErdosProblems-FormalConjectures`, run `575f57b1`):
2/2 solved, pass@1 rate 1.0, verifier wall time 58s total, all results on
`canonical_statement_hash_match` fidelity basis.

## 4. Honest limits

- The proved theorem is **known mathematics** (1966); the contribution is
  the formalization artifact and the audited pipeline, not new mathematics.
- The **open** question of #1052 (finiteness of unitary perfect numbers)
  remains open; our attack plan
  ([reasoning/05](reasoning/05-open-problem-attack-plan.md)) targets
  kernel-verified structure theorems (σ*-multiplicativity; the 25-digit
  fifth unitary perfect, currently a corpus `sorry`; `ω_odd ≤ ν_2 + 1`) and
  will map, not hide, the wall.
- pass@1 = 1.0 reflects heavy *local pre-validation* before tracked
  attempts (every proof compiled locally first); the tracked pipeline
  measures end-to-end integrity, not zero-shot model skill.
- LLM-generated Lean is drift-prone: the biggest practical error source was
  Mathlib name/API churn, mitigated by grepping the pinned snapshot before
  writing (see [reasoning/04](reasoning/04-erdos1052-proof-narrative.md)).

## 5. Reproduction

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean          # the 1052 proof
lake env lean LeanChecker/Erdos/CorpusValidation.lean   # EGZ/EKR/perfect validations
lake env lean LeanChecker/Erdos/OpenStatements.lean     # open statements (3 sorry warnings expected)
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`. The snapshot
copies in [proofs/](proofs/) are byte-stamped by the `module_source_hash`
values in [traces/](traces/); the living, CI-built copies are under
`lean-checker/LeanChecker/Erdos/`.
