# Induction (Elementary)

Focus on proof patterns that teach induction, strong induction, recursion, finite sums, products, factorials, powers, inequalities by induction, and monotonicity.

This folder is both a packet storage area and a local agent workspace for
the Induction domain at the elementary level.

- Run this domain: see `LOOP.md`
- Track progress: see `DASHBOARD.md`
- Next targets: see `QUEUE.md`
- Stalled work: see `BLOCKERS.md`
- Inter-domain dependencies: see `CROSS_DOMAIN.md`
- Evidence-rail rules: see `TRACE_POLICY.md`
- Packet shape: see `PACKET_TEMPLATE.md`
- Completion checklist: see `VALIDATION.md`

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
