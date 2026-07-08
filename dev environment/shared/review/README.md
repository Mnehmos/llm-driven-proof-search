# Shared Review Queue

Cross-domain review queue: packets or proposed shared-infrastructure
promotions awaiting review before merging into `shared/lean_kits` or
`shared/proof_patterns`.

| Date | Item | Proposed by | Domain | Status |
|------|------|--------------|--------|--------|
|      |      |              |        |        |

## Global Operating Rule

Do not let proof work escape the proof environment.

Meaningful proof work includes: formal statements, Lean diagnostics, proof
attempts, generated scripts, generated files, source reviews, failed routes,
route pivots, Mathlib lookup failures, repair notes, final proof exports.

- If it matters to how the proof was found, record it.
- If it proves the theorem, verify it through Lean.
- If it fails, record the failure.
- If it uses another domain, record the dependency.
- If it becomes reusable, promote it to `shared/`.

Private reasoning is not proof authority. Lean decides. The ledger records.
