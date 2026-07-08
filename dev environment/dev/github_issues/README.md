# Dev Issue Loop

The dev-agent home. Its job is **not** to create math packets — its job is
to constantly work open GitHub issues, especially MCP workbench issues,
trace-capture issues, validation bugs, export bugs, and workflow friction.
The dev agent keeps the toolchain healthy while the domain agents fill the
corpus.

- Run this loop: see `LOOP.md`
- Triage state: see `TRIAGE.md`
- Bug tracking: see `BUGS.md`
- Feature tracking: see `FEATURES.md`
- Completed work: see `DONE.md`
- Filing a new issue: see `ISSUE_TEMPLATE.md`
- Session handoff: see `HANDOFF.md`

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
