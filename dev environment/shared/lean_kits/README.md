# Shared Lean Kits

Reusable Lean tactic/import kits promoted from domain packets once a
pattern is used by more than one domain. See
`shared/proof_patterns/README.md` for the promotion workflow; this folder
holds the actual reusable Lean source, not the writeup.

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
