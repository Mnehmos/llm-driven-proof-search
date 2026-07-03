# Fix Plan — Playtest 2 / Adversarial Review (2026-07-03)

## The finding

Playtest 2 ran an adversarial "weakened root" test: formalize "every even natural
is divisible by two" as `∀ n, Even n → True` (conclusion trivially inhabited) and
prove it. The proof kernel-verified. The environment then presented that result —
via `outcome`, problem state, reward, and the `proof_export` dossier — as if it
had certified the source claim.

The defect was not in Lean. It was the application layer collapsing two
independent claims into one boolean:

- **Proof soundness** — Lean proved this exact formal statement.
- **Statement fidelity** — this formal statement represents the source problem.

`problem_create(approve=true)` fabricated fidelity approval with zero review,
`problem_approve_fidelity` was a flag-setter with no evidence, and root-proof
finalization treated "kernel verified" and "certified" as the same thing. Every
downstream consumer (episode outcome, problem lifecycle, reward, dossier,
dataset export) inherited the conflation.

## The invariant

```
COMPLETE = root kernel-verified AND statement fidelity verified
```

`proof_status`, `fidelity_status`, and `promotion_status` are tracked
independently and must never be collapsed. A valid formal proof must never
imply verified fidelity.

## What shipped (v0.2.2)

**Schema** (`db/schema_v1.rs`):
- `problem_versions.fidelity_status`: `pending/approved/revoked` →
  `unreviewed/attested/verified/rejected/revoked`.
- New `problem_fidelity_reviews` table — an immutable, hash-bound record of who
  decided a formalization is faithful and on what evidence. Fidelity belongs to
  the problem version, not to any one proof episode.
- DB-level backstop (defense in depth, not just application logic):
  `CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified')`. `PROVING` allows
  `verified` OR `attested`; only `verified` reaches `COMPLETE`.
- `episodes.outcome` gains `kernel_verified` — root kernel-verified, fidelity not
  (yet) verified. Never a synonym for `certified`.

**Reward** (`models/reward.rs`): new `RootKernelVerified` component, paid on every
kernel-verified termination regardless of fidelity. `TerminalSuccess` is paid
only on the composite `certified` outcome — a prover that faithfully proves a
bad formalization is never rewarded as if it solved the real problem, but it
also isn't penalized for someone else's bad formalization.

**MCP surface** (`chatdb-mcp/src/lib.rs`):
- `problem_create`'s `approve: bool` bypass is gone. Replaced with
  `unsafe_dev_attestation: bool` — honestly named, sets `fidelity_status='attested'`
  (proving allowed, `certified` never reachable), never silently implies review.
- `problem_approve_fidelity` (flag-setter) replaced with
  `problem_submit_fidelity_review` — takes `decision`, `method`, `approver_id`,
  `rubric_version`, `evidence_json`, and the three hashes it claims to have
  reviewed. The server independently recomputes `source_problem_hash`,
  `root_statement_hash`, and `normalized_rendering_hash` from the *current*
  problem_versions row and rejects the submission on any mismatch — a review can
  only authorize the exact text it reviewed. `problem_create`/`problem_list` now
  return these hashes so a real client can copy them back without reimplementing
  the canonical hashing algorithm.
- Root-proof finalization now branches on `fidelity_status`: `verified` →
  `certified` + problem `COMPLETE`; anything else → `kernel_verified` + problem
  state `FIDELITY_REVIEW` (proof search is done; nothing is certified yet). A
  `problem_submit_fidelity_review(decision=verified)` landing *after* an episode
  already reached `kernel_verified` promotes that episode to `certified`
  retroactively — review need not precede proof.
- `proof_export` renders Proof soundness / Statement fidelity / Canonical
  promotion / Training eligibility as four independent fields, always. The
  headline is only `✅ CERTIFIED` when both are verified; a kernel-verified,
  fidelity-unreviewed episode renders `⚠️ KERNEL-VERIFIED FORMAL STATEMENT —
  FIDELITY NOT YET VERIFIED`, and an explicitly rejected one states plainly that
  the proof does not certify the source claim.

**Dataset export** (`chatdb-core/orchestrator/dataset.rs`): fixed `export_rl`
querying the nonexistent `step_committed` event type instead of the runtime's
actual `action_committed` — RL exports were silently empty for every MCP-driven
episode. (Reward/terminated/truncated fields in that payload remain a
follow-up; the trajectory payload doesn't carry them yet — noted in code, not
fixed here.)

## Regression tests (12 MCP integration tests total, all green)

- `test_weakened_root_reaches_kernel_verified_not_certified` — the exact exploit.
  Asserts `outcome != certified`, `TerminalSuccess` absent, problem state
  `FIDELITY_REVIEW` not `COMPLETE`, dossier never renders `✅ CERTIFIED`.
- `test_fidelity_review_wrong_hashes_rejected` — a mismatched hash submission is
  rejected outright and never mutates `fidelity_status`.
- `test_fidelity_verified_before_proving_reaches_certified_directly` — positive
  control: a real review before proving reaches `certified`/`COMPLETE` in one step.
- `test_fidelity_review_promotes_kernel_verified_episode_retroactively` — a
  review landing `verified` after the fact flips the episode's outcome and the
  problem's state.

## Explicitly deferred (not in this release)

This was scoped as the hotfix (the review's own "Phase 1"). Not attempted here:

- **Schema v2 / canonical promotion pipeline** — `canonical_certificates`
  promotion triggers, certificate scope (`formal_statement_only` vs
  `source_aligned`), `approved_formalizations` semantic-structure columns. The
  `problem_fidelity_reviews` table + DB-level CHECK cover the invariant that
  matters today; the fuller canonical-storage architecture in ADR-0002 is a
  separate, larger piece of work.
- **Semantic extraction / risk lints / blind backtranslation / independent
  reviewer policy / human review UI** (the review's Phase 3) — no automated
  fidelity-detection pipeline exists; `problem_submit_fidelity_review` records
  evidence, it doesn't generate it. This is real, substantial future work.
- **`needs_revision` review decision** — simplified to `verified`/`rejected` for
  this pass; the three-way decision can be added when the review pipeline needs it.
- **Full dataset quarantine metadata** (`proof_status`, `certificate_scope`,
  `canonical_promotion_status`, etc. on every exported record) — the SFT/DPO
  exporters are independently broken (they read `submitted_action_json`, which
  the MCP runtime never populates) and need their own fix before quarantine
  metadata is worth adding to their output.
- **Reward-role separation** (prover vs. formalizer) — no formalizer role exists
  in this single-prover-role environment yet.

## Acceptance

`cargo test --workspace` — 27 tests, 13 suites, all green. Verified live against
the real `lean-checker` (see conversation): the weakened-root exploit reproduced
and fixed through the actual Lean 4 kernel, not just the mock gateway.
