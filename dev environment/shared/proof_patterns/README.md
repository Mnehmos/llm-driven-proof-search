# Shared Proof Patterns

Distilled, reusable proof patterns and their writeups. A domain agent that
finds a lemma or tactic sequence used by more than one domain should record
the dependency in that domain's `CROSS_DOMAIN.md`, then propose promoting
it here rather than duplicating it across domains.

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
