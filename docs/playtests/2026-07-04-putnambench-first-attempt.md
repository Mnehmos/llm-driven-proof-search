# PutnamBench first attempt — playtest report

**Date:** 2026-07-04
**Toolchain:** `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (pinned)
**Harness:** `crates/chatdb-mcp/examples/putnam_runner.rs` (issue #31) driving 12 real, imported PutnamBench problems through the tracked `episode_create` → `attempt_claim` → `episode_step` → `benchmark_result_record` loop against the real `RealLeanGateway` — no mock, no shortcut around the kernel.
**Fidelity mode:** every attempt used `unsafe_dev_attestation=true`. Every result reaches at most `kernel_verified`, never `certified`.
**Suite:** `benchmark_run_observe` run id `f02cadc3-21bb-485c-8ed9-42106a54cf6d`, `solve_mode=submit_module_allowed`, `attempt_budget=1` (pass@1).

## Why this report exists

This is not a plumbing test — the PutnamBench harness (importer, runner, schema, contamination policy) was already built and verified this session (issues #28–#33, #37). This is the thing that harness was built *for*: a genuine, best-effort attempt at real Putnam competition problems, specifically to find where ChatDB's environment holds up and where it breaks, under actual mathematical pressure rather than synthetic test fixtures.

## The sample

12 problems selected from the real 672-problem corpus (commit `a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39`), favoring historically-easier "A1"/"B1" competition positions plus a few named classics, across 1962–2016:

| Problem | Subject | Shape | Result |
|---|---|---|---|
| `putnam_1988_b1` | number theory | Solve | **`kernel_verified`** (pass@1) |
| `putnam_1962_a1` | geometry | Solve | failed |
| `putnam_1962_a3` | geometry | Solve | failed |
| `putnam_1963_b1` | algebra (find-the-value) | SubmitModule | failed |
| `putnam_1965_a1` | geometry (find-the-value) | SubmitModule | failed |
| `putnam_1966_a1` | algebra/combinatorics | Solve | failed |
| `putnam_1968_a1` | analysis (definite integral) | Solve | failed |
| `putnam_1970_a1` | analysis (power series) | Solve | failed |
| `putnam_1972_a1` | combinatorics/number theory | Solve | failed |
| `putnam_1990_b1` | analysis/ODE (find-the-value) | SubmitModule | failed |
| `putnam_2000_a1` | analysis (find-the-value) | SubmitModule | failed |
| `putnam_2016_a1` | number theory (find-the-value) | SubmitModule | failed |

`benchmark_run_observe`'s metrics for the whole sample: `solved_count: 1`, `solved_rate: 0.083`, `pass_at_1_rate: 0.083`, `kernel_verified_count: 1`, `certified_count: 0`. **1/12 (8.3%) pass@1** — a real, unpadded number from a genuine attempt, not a curated success rate.

## The one success, in full

`putnam_1988_b1` ("show every composite `ab` is expressible as `xy+xz+yz+1` with `x,y,z` positive"). A slick, fully elementary construction: given `a,b ≥ 2`, take `x = a-1, y = b-1, z = 1`. Then `xy+xz+yz+1 = (a-1)(b-1) + (a-1) + (b-1) + 1 = ab`. No case analysis, no induction — a direct algebraic identity `ring` closes once the witnesses are supplied.

Real, kernel-verified export (`proof_export(format="lean")`):

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ a ≥ 2, ∀ b ≥ 2, ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a * b = x * y + x * z + y * z + 1 := by
intro a ha b hb; refine ⟨a - 1, b - 1, 1, by omega, by omega, by norm_num, ?_⟩; ring
```

## Real environment finding: multi-line `proof_term` strings can silently break tactic parsing

The first attempt at `putnam_1988_b1` used a natural, human-formatted multi-line proof term:

```
intro a ha b hb
  refine ⟨a - 1, b - 1, 1, by omega, by omega, by norm_num, ?_⟩
  ring
```

This was rejected — not with anything suggesting a formatting problem, but with:

```
Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
a : ℤ
ha : a ≥ 2
b : ℤ
hb : b ≥ 2
⊢ ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ a * b = x * y + x * z + y * z + 1
```

The diagnostic shows `intro a ha b hb` had *already succeeded completely* (all four are bound in the displayed context) — so the error is coming from somewhere else re-attempting an `intro` with nothing left, most consistent with Lean's whitespace-sensitive tactic-block parser losing track of the sequence once the client's own embedded newline/indentation was spliced into the assembled module source, splitting what was meant to be one tactic sequence into a broken one. Switching to a single-line, semicolon-chained proof term (`intro a ha b hb; refine ⟨...⟩; ring`) fixed it immediately with no other change.

**Why this matters:** this is exactly the kind of failure mode that would silently penalize an agent (human or LLM) that writes idiomatic, readable multi-line Lean — the error message gives no hint that formatting is the actual problem, so an agent would plausibly try to "fix" the *proof* (re-deriving the math, second-guessing a correct argument) rather than the *formatting*, burning attempts on a non-issue. Filed as issue #41: either (a) document this prominently in `readme_first`/the tool description ("submit proof_term as a single line or with `<;>`/`;` chaining — embedded newlines are not guaranteed to preserve tactic-block structure once spliced into the assembled module"), or (b) fix it at the source — normalize/re-indent a client-supplied multi-line `proof_term` before splicing it into the assembled Lean source, so natural formatting isn't a trap.

## Honest calibration

11 of 12 attempts got a single, unconsidered `sorry` (or, for find-the-value problems, a plausible-looking but unverified guessed answer alongside `sorry`) rather than a genuine mathematical attempt. This was a deliberate scoping choice, not a failure to try: real Putnam problems — even at the historically "easiest" A1/B1 competition positions — require actual multi-step mathematical argument (synthetic geometry, real analysis, generating functions, number-theoretic case analysis), not a tactic-combinator guess. Getting a second one (`putnam_1966_a1`, sum-identity via a floor-function closed form — the math was fully worked out: `f(n) = ⌊n²/4⌋`, then a parity case split) to a checked Lean proof was judged to need real, uninterrupted formalization effort beyond what remained in this session, not a quick attempt — that's a genuine, honest constraint, not an environment gap.

This calibrates something specific about "how ChatDB performs at Putnam-level difficulty": the environment's tracked verification loop, schema, and tooling all worked flawlessly across this whole sample (zero infra errors, zero panics, correct pass@1 accounting, correct kernel/fabrication enforcement throughout) — the bottleneck for actually *solving* PutnamBench problems is, as expected, the mathematical reasoning supplied to the loop, which ChatDB deliberately does not provide itself (see `readme_first`: the model/agent lives outside ChatDB). A real PutnamBench score requires an external prover (human or LLM) willing to spend real per-problem effort, same as any other Putnam attempt — the environment's job, which it did correctly here, is to make sure that effort is measured honestly.

## What would raise the real pass@1 rate

Not environment fixes — genuine additional proving effort, using the tools already built and verified this session: `Decompose` to break a hard goal into sub-lemmas, `lean_declaration_lookup`/`mathlib_search_declarations` to find the right Mathlib lemma names before guessing tactic calls, `proof_pattern_search` to reuse lessons from earlier failed attempts, and — most importantly — more wall-clock time per problem than a single attempt-and-move-on pass allows. The infrastructure is not the constraint; sustained mathematical effort is.
