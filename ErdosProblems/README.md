# ErdosProblems — proofs, evidence, traces, reasoning

Self-contained deliverable for the Erdős-corpus work. Start with the
**[whitepaper](whitepaper.md)**.

## Layout

| Path | Contents |
|---|---|
| [whitepaper.md](whitepaper.md) | The report: trust design, method, results, honest limits, reproduction |
| [proofs/](proofs/) | Snapshot copies of the kernel-verified proofs (byte-stamped by `module_source_hash` in traces/). Living CI-built copies: `lean-checker/LeanChecker/Erdos/` |
| [evidence/](evidence/) | Machine records: run metrics, public summaries with redaction markers, and the disclosure rationale for publishing full bodies |
| [traces/](traces/) | Hash-chained episode ledgers (GENESIS → committed → terminated) with all integrity hashes and regeneration commands |
| [reasoning/](reasoning/) | The narrative: 01 calibration audit · 02 corpus validation · 03 bounty board · 04 how the 1052 proof was found · 05 the open-problem attack plan |

## Headline results

1. **Calibration MATCH** — an independently written proof of
   `erdos_1.variants.weaker` agrees with the corpus's proof on file, on the
   byte-identical statement, under one verifier. The pipeline's "done"
   signal is corroborated by an external artifact.
2. **Unitary perfect numbers are even** (Subbarao–Warren 1966, Erdős #1052's
   solved variant): first standalone-reproducible Lean proof — the
   statement ships as `sorry` in google-deepmind/formal-conjectures, and the
   only prior linked proof does not replay outside its home infrastructure.
   Kernel-verified pass@1, ~250 lines, Mathlib-only.

## Verify it yourself

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean
```

Exit 0 = Lean's kernel accepts every step. No trust in the authors required.

## Status of the open problem

Erdős #1052 — *are there finitely many unitary perfect numbers?* — is
**open**, and this folder does not claim otherwise. The staged attack
(kernel-verified milestones: σ*-multiplicativity, the corpus's missing
25-digit verification, `ω_odd ≤ ν₂ + 1` structure bound) is in
[reasoning/05-open-problem-attack-plan.md](reasoning/05-open-problem-attack-plan.md).

## Upstream

An upstream contribution branch (`erdos-1052-formal-proof-link` on the
Mnehmos fork of formal-conjectures, adding a `@[formal_proof]` link) is
**staged but deliberately not opened** — maintainer's call, on hold while we
take a real shot at the problem itself.
