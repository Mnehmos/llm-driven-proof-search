# Fix Plan — Environmental Scope Collapse (2026-07-03)

## The finding

A transcript working the Bonza-style theorem hit an unknown identifier
(`Nat.factorization`-style API) and reasoned:

> "This declaration is not available in the current proof file"
> → "This Mathlib commit does not contain the API"

Those are not the same claim. The verifier hardcoded exactly two imports
(`Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`). An `unknown identifier` result
under that closure establishes only that the name didn't resolve *there* — never
that it's absent from the pinned `mathlib@<rev>`. The model then used the
unsupported conclusion to declare a witness blocked and ask for a strategic
retreat, converting a local, fixable obstacle (missing import) into a
user-facing capability claim it had no evidence for.

We call this failure class **environmental scope collapse**: a local fact about
one import closure gets inflated into a global claim about what the system can
do. It's the inverse of confident fabrication — not inventing a capability, but
confidently inventing a limitation.

## The invariant

An `unknown_declaration` diagnostic proves exactly one thing: the name didn't
resolve under the exact import manifest used for that attempt. It proves
nothing about the pinned library's actual contents. The only way to test that
second claim is to actually check — under a broader import — which is what
`lean_declaration_lookup` does.

## What shipped (v0.2.3)

**Import manifests are now real data, not hardcoded Rust.**
- `problem_versions` gains `import_manifest_json` / `import_manifest_hash` —
  immutable per problem version. `problem_create(problem_imports=[...])` extends
  the base manifest (`Ring` + `NormNum`); each new module is validated with a
  real compile check (`LeanGateway::validate_import_manifest`) before the
  problem is created, not discovered as a failure at solve time.
- `LeanGateway::verify_exact` takes `import_manifest: &[String]` instead of
  building imports from two hardcoded lines. `RealLeanGateway` assembles the
  import block from the manifest; behavior for problems using the default
  manifest is unchanged.
- `import_manifest_hash` is threaded into every observation (`CompactContext`)
  and is re-fetched (never trusted from a trajectory payload) during
  `episode_replay`, so replay always re-verifies against the exact closure the
  original attempt used — never a environment silently mutated underneath an
  existing trajectory.

**New tool: `lean_declaration_lookup`.** Given a `problem_version_id` and a list
of names, checks each in one compile pass under the problem's own manifest,
then — only for names that failed — a second pass under the full Mathlib
umbrella (`import Mathlib`). Returns one of four honest statuses per name:
`available`, `not_in_current_import_scope`, `unknown_declaration`,
`environment_error` (the lookup itself failed — not evidence either way). A
gateway that can't perform the check (e.g. a test mock) reports
`environment_error` by default rather than guessing.

**Diagnostic quality.** `LeanDiagnosticCategory` gains `UnknownDeclaration`,
split out from the generic `ParseError` it was previously lumped into — a name
resolution failure and a syntax failure are different claims and were
indistinguishable before this. `source_span` is now actually populated from
Lean's `pos`/`endPos` JSON fields (previously always `None`). Every
error-severity diagnostic from a Lean run is now collected independently into
`LeanVerificationResult.all_diagnostics` — previously they were joined into one
semicolon-delimited string, which is what made several of the transcript's
speculative interpretations ("that's a parser artifact", "the type mismatch is
cascading") impossible to actually verify against the verifier's own output.

**Epistemic rule surfaced to the agent.** `environment_describe.epistemic_rules`
states the rule plainly: an unknown-declaration result under the active
manifest doesn't establish library absence; call `lean_declaration_lookup`
first. A second rule: a prior model's proof is a candidate artifact, not
evidence of correctness, until it passes the current pinned verifier.

## Explicitly deferred (not in this release)

The review proposed a fuller architecture — this ships the hotfix tier:

- **Controlled `request_import` typed action with auto-forking** — a typed
  action that validates a new module and forks a new episode/problem revision
  bound to the extended manifest, so a running episode never has its
  environment mutated underneath it. Not built: the practical equivalent today
  is creating a new `problem_create(problem_imports=[...])` — an immutable new
  problem_version, no special forking logic needed, at the cost of needing a
  fresh `problem_submit_fidelity_review` even when only the import scope
  changed (the statement itself is unchanged). A lighter "clone this problem's
  review onto a new problem_version with the same statement hashes" convenience
  is a reasonable follow-up.
- **Multi-branch parallel obligation architecture** ("Branch A: environment
  discovery, Branch B: foundational lemma, ..." in the review) — a genuine
  research direction for the obligation graph, not a bounded fix. The current
  single-prover, single-obligation-at-a-time loop with `decompose` is what
  exists; running several strategies concurrently on independent obligations is
  future work.
- **Full per-diagnostic goal state / local context extraction** — `goal`,
  `local_context`, `unsolved_goals` on `LeanDiagnostic` remain unpopulated;
  Lean's `--json` output used here doesn't carry structured goal state without
  additional elaboration hooks. `source_span` and category are populated now;
  goal-state capture is a separate, larger integration.
- **Verifier-fact vs. model-interpretation storage** — checked, and this one
  turned out to already hold: `step.rs`'s `failure_lesson` is always the
  verifier's own diagnostic message, never model-authored prose (there is no
  tool today that lets a model write arbitrary "lessons" into the DB). No code
  change was needed; noted here so the invariant is documented, not just true
  by accident.

## Regression tests (8 new/updated, 29 total, all green)

- `test_unknown_identifier_is_not_categorized_as_parse_error` /
  `test_diagnostic_categories_stay_distinct` — the categorization logic itself,
  unit-tested directly.
- `test_problem_create_extends_import_manifest` — `problem_imports` extends
  (never replaces) the base manifest; returned hash is usable downstream.
- `test_lean_declaration_lookup_reports_environment_error_honestly` — a gateway
  that can't check reports that honestly rather than fabricating a status.
- Live verification (see conversation) against the real `lean-checker`:
  `lean_declaration_lookup` on a real absent declaration vs. a real
  not-yet-imported one, distinguishing the two through the actual two-pass
  compile check, not a mock.
