# Agent Loops Index

Index of every domain/frontier/dev `LOOP.md` in this workspace. Each
folder owns its own loop file; this index exists so a coordinating agent
can find them without walking the whole tree.

## Elementary

- `packets/elementary/algebra/LOOP.md`
- `packets/elementary/number_theory/LOOP.md`
- `packets/elementary/combinatorics/LOOP.md`
- `packets/elementary/geometry/LOOP.md`
- `packets/elementary/induction/LOOP.md`
- `packets/elementary/inequalities/LOOP.md`
- `packets/elementary/functions/LOOP.md`

## Intermediate

- `packets/intermediate/algebra/LOOP.md`
- `packets/intermediate/number_theory/LOOP.md`
- `packets/intermediate/combinatorics/LOOP.md`
- `packets/intermediate/geometry/LOOP.md`
- `packets/intermediate/induction/LOOP.md`
- `packets/intermediate/inequalities/LOOP.md`

## Frontier

- `packets/frontier/formal_conjectures/LOOP.md`
- `packets/frontier/erdos/LOOP.md`

## Dev

- `dev/github_issues/LOOP.md`

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
