# LLM-Driven Proof Search Environment — a Verifier-Backed RL Environment

[![Rust](https://img.shields.io/badge/Rust-2024_edition-orange)](https://www.rust-lang.org/)
[![MCP](https://img.shields.io/badge/MCP-2025--11--25-blue)](https://modelcontextprotocol.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This is a **synthetic reinforcement learning environment** where an external LLM agent attempts to prove mathematical theorems verified by the [Lean 4](https://lean-lang.org/) kernel. It exposes a [Model Context Protocol (MCP)](https://modelcontextprotocol.io/) server so that any MCP-compatible host — Claude Desktop, Cline, Roo Code, a custom Python script, or a distributed training loop — can drive proof search episodes without this environment ever containing a single line of inference code.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     External Agent Host                         │
│  (Claude Desktop, Cline, Python RL loop, human, ...)            │
│                                                                 │
│  Chooses model · formats prompt · calls LLM · parses response   │
└────────────────────────┬────────────────────────────────────────┘
                         │  MCP (stdio, JSON-RPC 2.0)
                         │  Protocol version 2025-11-25
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     proofsearch-mcp (MCP Server)                     │
│                                                                 │
│  86 tools · typed schemas · JSON Schema 2020-12                 │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     proofsearch-core (Engine)                         │
│                                                                 │
│  Episode lifecycle · obligation scheduler · crash recovery       │
│  Atomic step (CAS) · hash-chained trajectories · replay         │
│  Budget leases · reward calculation · dataset export             │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Lean 4 Kernel (Verifier)                    │
│                                                                 │
│  Sandboxed per-attempt · deterministic · timeout-guarded        │
│  Kernel pass / fail is ground truth                             │
└─────────────────────────────────────────────────────────────────┘
```

**Key invariant:** LLM-Driven Proof Search Environment contains **no provider SDKs, no API keys, no model routing, no inference calls, no streaming logic, and no provider retry code.** The external host owns all of that. LLM-Driven Proof Search Environment is the environment; the host is the policy.

As of v0.3.x, LLM-Driven Proof Search Environment verifies more than single theorem bodies — see
[`Solve` vs. `SubmitModule`](#solve-vs-submitmodule) below and
[`docs/submit_module.md`](docs/submit_module.md) for the small local Lean
development this environment now supports (helper defs/theorems, mutual
recursion, staged all-or-nothing verification). For what this represents in
terms of overall system capability and what's still ahead, see
[`docs/roadmap.md`](docs/roadmap.md).

## MCP Tools

**Call `readme_first` before creating any episode.** It's the dedicated
first-contact tool (issue #35): the required proof-search loop, the trust
boundary (tracked MCP actions and Lean verdicts are evidence — your own
reasoning is not), when to use `Solve` vs `SubmitModule`, why a proof check
outside `episode_step` doesn't count as a valid attempt, and the cost/
benchmark-mode boundary. Any agent host — Claude Code, Codex, Kilo Code,
Antigravity, or a custom script — should call this first.

| Tool | Description |
|---|---|
| `readme_first` | Call this first. The proof-search protocol: the loop, trust boundary, Solve/SubmitModule guidance, untracked-attempt warning, cost and benchmark-mode boundary |
| `environment_describe` | Protocol version, capabilities, tool schemas, Lean gateway readiness |
| `problem_create` | Register a new problem version (source text + root formal statement). `fidelity_status` starts `unreviewed` |
| `problem_submit_fidelity_review` | Record an evidence-backed determination that a problem's formal statement represents its source text. The ONLY path to `fidelity_status='verified'` — required for `outcome='certified'` |
| `problem_record_benchmark_alignment` | Record a `formal_benchmark_hash_alignment` basis (issue #43): the server verifies the problem hash-matches a registered trusted-benchmark target and sets `fidelity_status='benchmark_aligned'`, unlocking proving without `unsafe_dev_attestation`. Hash alignment, **not** NL review — reaches `kernel_verified` but never `certified` |
| `problem_list` | List known problem versions (includes the hashes a reviewer must submit back unchanged) |
| `episode_create` | Start an episode from a problem version with `fidelity_status` `verified` or `attested` |
| `episode_reset` | Nondestructive reset — creates a new episode with `parent_episode_id` |
| `episode_observe` | Get the current observation and pending action request |
| `attempt_claim` | Claim a pending action request to obtain the `action_attempt_id` + `claim_token` required by `episode_step` |
| `episode_step` | Submit a typed action (`Solve` / `SubmitModule` / `Decompose` / `GiveUp`) with CAS revision check |
| `episode_status` | Episode state, revision, budget, step count, outcome |
| `episode_close` | Gracefully terminate an active episode |
| `model_call_reserve` | Reserve a budget lease before calling an external model |
| `model_call_settle` | Settle or void a lease (provider failure, cancellation) |
| `trajectory_export` | Paginated export of hash-chained trajectory events |
| `episode_replay` | Re-execute typed actions (`Solve` or `SubmitModule`) through Lean and verify trajectory integrity |
| `proof_export` | Proof dossier in one of 7 modes: `markdown` (default), `lean`, `public_summary` (redacted, never includes the proof body), `audit_archive`, `training_export` (structured JSON for SFT/RL/DPO), `paper_dossier` (adds a written narrative), `maintainer_submission`. Modes exposing the proof body require `allow_putnambench_proof_export=true` when the episode is linked to a tracked benchmark suite — see [docs/benchmarks/putnambench.md](docs/benchmarks/putnambench.md) |
| `lean_declaration_lookup` | Checks whether names resolve under a problem's import manifest (fast, default). Pass `deep_check=true` to also check under the full Mathlib umbrella and distinguish "not imported here" from "genuinely absent" (slow — loads all of Mathlib). Call this before concluding an API is unavailable |
| `proof_pattern_create` | Register a reusable proof-pattern lesson (failure signature + recommended repair). Advisory only — never marks anything proved |
| `proof_pattern_search` | Free-text search over the proof-pattern library, or list it whole. Call before repeating a failure another attempt already diagnosed |
| `proof_pattern_record_application` | Record that a pattern was relevant to a real episode/attempt (failed example, repair example, or suggested hint). Insert-only metadata — never touches proof/fidelity/certification status |
| `draft_create` | Register an informal Draft artifact — untrusted planning/reasoning content. A draft can never mark anything proved |
| `draft_observe` | Read back a draft's content and any moves recorded against it |
| `draft_extract_moves` | Record structured moves (construction, auxiliary_lemma, case_split, ...) the external agent identified in a draft. Metadata only |
| `formalization_plan` | ONE tool for the whole Level 3 formalization-plan family, dispatching on an internally-tagged `action` (`create` / `observe` / `update` / `add_item` / `attach_lookup` / `promote_item_to_obligation` / `attach_librarian_result`) — exactly like `episode_step`'s typed `action`. Advisory scaffolding, never proof authority: `promote_item_to_obligation` links a plan item to an episode_obligation that **already exists** (created via a normal `Decompose` action) and never creates one; `attach_lookup` / `attach_librarian_result` attach `lean_declaration_lookup` / Mathlib-librarian search results to a plan item as hints, updating its Mathlib coverage status but never proof status |
| `research_dossier` | ONE tool for the whole Level 4 research-dossier family, dispatching on an internally-tagged `action` (`create` / `observe` / `node_add` / `external_reference_add` / `assumption_boundary_add` / `citation_review_add` / `verification_layer_set`) — exactly like `episode_step`'s typed `action`. Explicit trust-boundary metadata, never proof authority: `external_reference_add` records citations as **tracked assumptions**, never proof; `citation_review_add` records human review, which remains distinct from Lean verification; `verification_layer_set` is the **only path** to a `kernel_verified` layer and accepts that status only where kernel evidence already exists (e.g. a node whose `trust_status` is already `proved_in_episode`, backed by a verified lemma from **this dossier's own** episode/problem context) |
| `candidate_construction` | ONE tool for the whole candidate-construction family (issue #8), dispatching on an internally-tagged `action` (`add` / `observe` / `update_status` / `link_node` / `link_verification_layer`) — exactly like `episode_step`'s typed `action`. A candidate construction is a **proposed mathematical object, not a proof certificate**: its `trust_status` never certifies anything, and empirical support, human review, citation, and "a formal statement exists" all remain distinct from kernel verification. `add` proposes a construction (`graph_family`, `counterexample`, `coloring`, etc.) with motivated-discovery metadata — it can exist before a dossier, node, Lean theorem, or episode; `observe` records one empirical check (`supports`/`refutes`/`inconclusive`) against it, and never changes proof status; `update_status` updates status/trust_status/claimed_properties/known_failures/next_check (`kernel_verified_claim_linked` is rejected unless a real kernel-verified layer is already linked); `link_node` attaches it to a research node, adopting the node's dossier if the construction has none yet; `link_verification_layer` attaches it to an existing verification layer, adopting the layer's dossier if the construction has none yet — provenance, never promotion |
| `empirical_search` | ONE tool for the whole empirical math-lab family (issue #26), dispatching on an internally-tagged `action` (`add` / `observe` / `update_status` / `link_candidate` / `link_verification_layer`) — exactly like `episode_step`'s typed `action`. Every result is experimental **evidence, never proof**: no field carries kernel evidence, no status certifies an asymptotic/universal theorem, and even the strongest trust status only links to a formal target. `add` records a small-case/counterexample/construction search, parameter sweep, finite check, candidate ranking, or external-tool run; `observe` appends a finding and optional counterexample witness (`no_counterexample` never certifies a universal claim); `update_status` revises status/trust/results/candidate ids but cannot erase counterexamples, so falsified/failed/timed-out searches and witnesses stay visible; `link_candidate` and `link_verification_layer` attach existing dossier artifacts as provenance only — empirical support never proves a candidate, and a link never makes a layer kernel-verified |
| `challenge_create` | Define a challenge in a dossier (issue #53): a bounded, scored, reviewable competition frame for AI-generated math. Never proof |
| `challenge_observe` | Read a challenge with its tasks → submissions → scores/reviews, plus the export grouping (accepted/rejected/superseded/open separated). Read-only |
| `challenge_update_status` | Update a challenge's status (open/closed/archived/superseded). Never touches proof/fidelity/benchmark state |
| `validation_protocol_create` | Register a validation protocol a task's submissions can be checked against. A protocol describes a check; it is never itself proof |
| `task_create` | Add a bounded task to a challenge (find_candidate_object, improve_bound, find_counterexample, …). `bounds_json` keeps it small and reviewable |
| `task_update_status` | Update a task's status (open/closed/superseded). A superseded task stays visible |
| `task_submission` | ONE tool for the whole challenge-submission family, dispatching on an internally-tagged `action` (`create` / `validate` / `score` / `review` / `link` / `update_status`) — exactly like `episode_step`'s typed `action`. The variants carry **distinct trust profiles** and none is proof: `create` records an **untrusted** `content_json` payload (starts `submitted`); `validate` records an automated declared-check result (`validated`/`validation_failed` — **never** kernel verification; failed stays visible); `score` records a measurement (never proof; a rank is not proof authority; never confers training eligibility); `review` records a role-separated **human** decision (accepted/rejected/needs_changes/superseded — human review ≠ kernel verification, `accepted` means accepted into the dossier as a contribution, never proved); `link` records **provenance** to a candidate_construction / empirical_result / verification_layer in the submission's dossier (even a kernel_verified layer never makes the submission a proof); `update_status` sets the outcome (accepted/rejected/superseded/merged_into_dossier) without a review row. Rejected/superseded stay visible |
| `distilled_strategy_add` | Store a reusable distilled strategy artifact (cheat_sheet, heuristic_rule, counterexample_pattern, construction_recipe, …). A distilled strategy is **not** a proof; trust_status tops out at human_reviewed |
| `paper_ingest` | ONE tool for the whole paper/PDF ingestion family (issue #27), dispatching on an internally-tagged `action` (`create` / `extract_claims` / `observe` / `link_to_dossier` / `mark_review_status` / `link_node`) — exactly like `episode_step`'s typed `action`. Every action handles **untrusted extraction**, never proof: LLM-Driven Proof Search Environment does no OCR/LLM extraction — the host records its own extraction result, untrusted by construction, and **an extracted theorem is not statement-fidelity approval, an extracted citation is not citation validation, an extracted assumption is not an accepted assumption**. `create` ingests a paper/manuscript/proof-sketch/exposition as a reviewable source document, optionally linked to a dossier; `extract_claims` appends extracted nodes (main_theorem, definition, lemma, construction, reference, open_gap, …) — each node **requires** a non-empty `source_span` so it stays traceable to the source, plus confidence/status labels; `observe` reads a document with all extracted nodes and their trust labels (read-only); `link_to_dossier` attaches a document (and its nodes) to a dossier, so it surfaces in `research_dossier` `observe`'s ingestion bucket; `mark_review_status` updates a document's ingest/trust status, or (with `node_id`) a node's review/formalization/citation status (`rejected_extraction` stays visible; no status confers proof/fidelity/validation); `link_node` promotes/attaches an extracted node to a real dossier artifact — `external_reference` / `external_theorem_claim` (sets `citation_status=citation_recorded`), `research_node` / `formalization_plan_item` (sets `formalization_status=formalization_target_linked`) — recording provenance in the matching forward-link column and marking `review_status=linked_to_dossier_artifact`; the linked artifact keeps its own trust and the node **never** gains proof/kernel authority |
| `exposition_add` | Add a human-readable exposition section (problem_summary, construction_intuition, key_lemmas, unverified_bridges, …) linked to a problem/episode/obligation/module/lemma/dossier. `prose_status` (prose/reviewed_prose/formalized) marks epistemic weight — never proof |
| `exposition_observe` | List exposition artifacts for a problem_version, episode, or dossier. Read-only prose, separate from verified proof |
| `semantic_skeleton_add` | Attach a structured reading of a statement/module/solution (quantifiers, hypotheses, conclusion, definitions, construction map, back-translation, fidelity `risk_flags`) scoped by `review_scope`. Metadata only — never sets `fidelity_status` or substitutes for `problem_submit_fidelity_review` |
| `semantic_skeleton_observe` | Append one module-aware fidelity observation (confirms_faithful/raises_concern/reports_mismatch/inconclusive) to a skeleton's review history. `confirms_faithful` is not the root fidelity gate |
| `expert_review_add` | Record one role-separated review-ledger entry (proposer/formalizer/prover/reviewer/domain_expert/refuter/editor/…) against a polymorphic target (source_problem, formal_statement, construction_artifact, module_artifact, external_citation, exposition, full_dossier, …). Pure insert — never marks anything proved; a human decision stays distinct from kernel verification |
| `expert_review_observe` | Read review-ledger entries filtered by dossier, target (kind+id), and/or reviewer role. Read-only |
| `mathlib_search_declarations` | Search the real pinned Mathlib source tree for declaration names containing a substring (beyond exact-name lookup). Advisory only |
| `mathlib_search_local_artifacts` | Search this instance's own previously-verified theorem/def names for a substring match |
| `run_envelope` | ONE tool for the whole run-envelope family (issues #34/#38/#46), dispatching on an internally-tagged `action` (`create` / `update` / `cost_observation_add` / `attach_episode` / `observe`) — exactly like `episode_step`'s typed `action`. Purely descriptive metadata; **no action ever affects proof status**. `create` records host/model/mode (development/evaluation/benchmark/private_audit/public_report) and host-side cost accounting LLM-Driven Proof Search Environment cannot itself observe, plus an origin cost observation; `update` corrects an envelope's host-side cost fields or notes after the fact — append-only (issue #46): a correction appends an auditable observation, so the prior value stays queryable; `cost_observation_add` appends an auditable, append-only host-side cost observation, never overwriting a prior one; `attach_episode` tags an episode with a run envelope (metadata only — never changes the episode's outcome/state) and enforces the mode-enforcement policy: an `attested`/`unsafe_dev_attestation` episode is unconditionally rejected from a benchmark/evaluation/public_report-mode envelope (no override), always allowed for `development`, and requires `allow_dev_attested=true` for `private_audit`; `observe` reads back an envelope, every episode tagged with it, and its full append-only cost-observation history |
| `benchmark_suite_create` | Register a benchmark suite (e.g. PutnamBench) — name, upstream URL/commit, language |
| `benchmark_problem_register` | Register one problem from a suite. `root_statement_hash` is server-computed, never client-supplied |
| `benchmark_run_create` | Create a run against a suite. `lean_version`/`mathlib_commit` are read from the server's OWN detected Lean environment, never accepted from the client |
| `benchmark_result_record` | Record (or upsert, for pass@k) one problem's result within a run. If `episode_id` is given, cross-checked against that episode's ACTUAL recorded outcome AND that it proved the SAME statement as the benchmark problem (issue #36) |
| `benchmark_run_observe` | Read back a run, its results, and aggregate metrics — `solved_rate` (solved at all) vs `pass_at_1_rate` (genuine first-attempt success) are reported separately |
| `proof_session` | ONE tool for the whole interactive (tactic-by-tactic) proof-session family, dispatching on an internally-tagged `action` (`start` / `observe` / `tactic_step` / `branch` / `select_node` / `reconstruct` / `promote_to_attempt` / `close` / `export` / `replay`) — exactly like `episode_step`'s typed `action`. Search evidence only, except the `promote_to_attempt` action (and `replay` mode `final_proof`), which resubmits a reconstructed script through the real `attempt_claim` + `episode_step(Solve)` kernel-verification path. See [Interactive Proof Sessions](#interactive-proof-sessions) |

## Budget Accounting

Episode budgets are enforcement/accounting controls, not proof-soundness
claims. A `NULL` `episodes.cost_budget_micros` is unbounded; bounded budgets
are debited only by conditional reservations that must fit the current
remaining budget.

- `episode_step.cost_micros` is the environment step charge. It must be
  non-negative and is reserved before the step executes; over-budget steps are
  denied before any Lean gateway call.
- `model_call_reserve.reserved_cost_micros` is a host/model-call budget lease.
  It must be non-negative and immediately reserves bounded episode budget. The
  lease row is inserted only if that budget reservation succeeds.
- `model_call_settle(actual_cost_micros, status="settled")` records the
  caller-reported actual model-call cost. Settlement adjusts only the delta
  from the reservation: lower actual cost refunds the difference, higher actual
  cost conditionally debits only the extra amount.
- `model_call_settle(status="voided")` cancels a lease and refunds the full
  reserved amount; no actual model-call cost is reported for a voided lease.
- Reserved-but-unsettled costs remain reservations. Benchmark cost summaries
  continue to include only settled `actual_cost_micros` as attested
  `model_call_reported_cost_micros`, never as exact cost.

## Level 4 Research Substrate

Research dossiers are paper-scale working records for definitions, lemmas,
theorems, remarks, references, and open gaps. A dossier can be linked to a
`problem_version`, linked to an `episode`, linked to both, or created before
either exists.

The Level 4 substrate is explicit about trust boundaries:

- `proved_in_episode` means there is a linked Lean-verified episode lemma.
- `imported_from_mathlib` means the claim is attributed to Mathlib, not locally
  proved by this episode.
- `external_citation_unreviewed` and `external_citation_human_reviewed` are
  citation states, not proof states.
- `unformalized_assumption` and `rejected_unsafe_assumption` remain visible as
  assumptions or rejected assumptions.
- `verification_layers` track independent review/construction/formalization
  layers (arithmetic construction, geometric criterion, packing/size bound,
  asymptotic extraction, formal module, statement fidelity, external review, …)
  and can be `blocked` or `failed` without failing the whole dossier. A layer
  reaches `kernel_verified` only for a `formal_module`/`statement_fidelity`
  layer backed by a real Lean pass — a search/construction/packing layer never
  can. The markdown-family `proof_export` modes render a **Verification layers**
  table for the dossier(s) attached to the episode or its problem, and
  `training_export` carries the same per-layer state as structured,
  redacted metadata (`layer_kind`/`status`/`target_kind`/redacted
  `target_handle`/`summary` plus `kernel_verified_layer_count`/
  `total_layer_count` and the non-gating policy note) alongside its `records`
  array — so every export reports the true per-layer state, not only the
  episode outcome. Layer status is **additive metadata**: a kernel-verified
  root theorem does not imply every layer is verified, and layer completeness
  never gates `certified`.

No cited, reviewed, empirical, or assumed artifact is represented as kernel
verified unless it is linked to an actual Lean-verified artifact. These tables
are research bookkeeping and do not mutate episode outcome, obligation status,
budget state, fidelity status, or benchmark results.

### Candidate construction artifacts

Candidate constructions are proposed mathematical objects — graph families,
point configurations, colorings, field towers, lattices, counterexamples,
asymptotic families, algebraic objects, combinatorial designs, and so on. They
are the first durable object layer for **motivated discovery**: beyond *what*
object is proposed, each records *why* it was proposed and what to do with it,
encoding the loop

```text
observation → motivated move → proposed object → intended role → next check
```

via the fields `motivating_move` (`generalize`, `specialize`, `decompose`,
`search_extremal_example`, `search_counterexample`, `introduce_invariant`,
`reduce_to_known_theorem`, …), `source_observation`, `intended_role`
(`witness`, `counterexample`, `extremal_example`, `lower_bound_construction`,
`formalization_target`, `bridge_to_existing_theorem`, …), `strategy_context`,
`why_this_might_work`, `why_this_might_fail`, `next_check`, and
`future_challenge_relevance`. The object itself lives in `informal_description`,
`parameters_json`, and `construction_json`; `verification_targets_json` records
what a later system should check.

A candidate construction can exist before there is a research dossier written
up, before there is a Lean theorem, before there is an episode, and before
there is empirical search machinery to generate one automatically (that
machinery is issue #26's empirical math lab; this substrate only holds the
objects it will produce and judge). Every link — `dossier_id`,
`related_node_id`, `verification_layer_id`, `problem_version_id`,
`episode_id` — is optional.

Candidate constructions are **not proof certificates**. Their `trust_status`
makes that explicit:

- `informal`, `empirical_evidence`, `cited`, `human_reviewed`, and
  `formalized_statement_exists` are all states short of kernel verification —
  empirical support, human review, a citation, or even an existing formal
  statement are each distinct from, and never imply, being proved.
- `kernel_verified_claim_linked` is the only state that claims kernel
  evidence, and it is rejected unless the construction's
  `verification_layer_id` names a `verification_layers` row whose own status
  is already `kernel_verified` (itself only reachable through real
  Lean-backed evidence — see above). A candidate construction can link to
  real evidence; it can never manufacture it.

A candidate construction can attach to a dossier, a research node, and/or a
verification layer, or exist attached to none of them. `falsified` and
`rejected` constructions stay visible in `research_dossier`'s `observe` action
rather than being deleted, since a documented dead end is itself research
output.

### Exposition artifacts

Serious mathematical output is not only a Lean file — it needs an explanation
layer: what the construction means, why the definitions were chosen, what the
key lemma does, and what remains unformalized. Exposition artifacts capture
that prose **alongside, and explicitly separate from, kernel-verified proof**.
Each carries a `prose_status` making its epistemic weight explicit:

- `prose` — raw author narrative.
- `reviewed_prose` — a human read it.
- `formalized` — the described claim is backed by a linked formal artifact.

**None of these is kernel verification**, and no exposition artifact ever
changes an episode outcome, `fidelity_status`, canonical promotion, training
eligibility, budget, or benchmark state. `proof_export` renders exposition in
its own `## Exposition (prose — not part of the verified proof)` section,
never inside the proof tree or the verified-module source, and every section
is labeled with its `prose_status` so a reader can never mistake reviewed or
unreviewed narrative for a checked proof. An artifact can attach to a
problem, an episode, a specific obligation, a verified module, a verified
helper lemma, and/or a research dossier — every link is optional.

### Semantic skeletons (module-aware fidelity)

Statement fidelity can't stay a single flat approval over one root
proposition: a module can prove a correct formal theorem while the real source
claim still rests on prose-only bridges (integer encoding, a bijection, a
final-answer extraction, a domain restriction). A **semantic skeleton** is a
structured reading of what a statement, verified module, or source-aligned
solution actually says — `quantifiers`, `hypotheses`, `conclusion`,
`definitions`, `construction_map`, a natural-language `backtranslation`, and
fidelity `risk_flags` — scoped by `review_scope` (`root_statement_only`,
`module_artifact`, `source_aligned_solution`, `computational_check_only`,
`structural_proof`). Its `semantic_fingerprint_hash` is server-computed over
the normalized content, never client-supplied.

A skeleton is **descriptive metadata, never the fidelity gate**: it has no
column that can hold kernel evidence, never sets `fidelity_status`, and never
substitutes for `problem_submit_fidelity_review`. `semantic_skeleton_observe`
appends module-aware review notes (`confirms_faithful`, `raises_concern`,
`reports_mismatch`, `inconclusive`) — a `confirms_faithful` note is
note-taking, not a proof.

### Expert reviews (role-separated ledger)

Serious mathematics gets its credibility from more than one prover: a claim is
proposed, formalized, proved, refereed, and checked by domain experts.
**Expert reviews** are a role-separated ledger of who reviewed what and what
they decided — `reviewer_role` (proposer, construction_searcher, formalizer,
prover, reviewer, domain_expert, refuter, editor, librarian) against a
polymorphic `review_target_kind` (source_problem, formal_statement,
construction_artifact, module_artifact, external_citation,
asymptotic_extraction, exposition, full_dossier), with a `decision`,
`confidence`, `expertise_tags`, `requested_changes`, and `risk_flags`.

`expert_review_add` is a **pure insert**: unlike `research_dossier`'s
`citation_review_add` action (which updates a citation's `claim_status`), an
expert review mutates no other table.
`reviewer_id` is free text, not an authenticated principal, and a
`domain_expert` "approved" decision is human-attested — it never marks
anything kernel-verified, never changes an episode outcome, `fidelity_status`,
canonical promotion, budget, or benchmark state. A `rejected` review records
an opinion without deleting or downgrading the reviewed artifact.

### Empirical math lab (issue #26)

The empirical math lab records **experimental mathematical evidence** —
small-case searches, counterexample searches, construction searches, finite
model checks, parameter sweeps, and candidate rankings. It is the object layer
candidate constructions are generated, tested, ranked, and falsified against.
It helps discover patterns, candidates, counterexamples, and next proof
targets. **It does not prove theorems. It does not certify asymptotic claims.
It does not replace Lean/kernel verification.**

That boundary is structural, not a convention:

```text
empirical evidence          ≠ proof
small-case check            ≠ asymptotic theorem
no counterexample found     ≠ universal theorem certified
successful construction     ≠ its claimed properties proved
candidate ranking           ≠ verified claim
human-readable result       ≠ kernel verification
```

An `empirical_searches` row has no column that can hold kernel evidence;
`has_kernel_evidence` and `is_proof` are always false. `trust_status` tops out
at `linked_to_formal_target` ("this evidence points at a formalization
target") — still not a proof. Every link (`dossier`, `research_node`,
`candidate_construction`, `verification_layer`, `problem_version`, `episode`)
is optional, so a search can exist before any dossier, candidate, episode, or
Lean proof. `counterexamples`, `failed`, and `timed_out` searches stay visible
(a documented dead end is research output). `cost_summary`/`runtime_metadata`
describe the *external* search run and are isolated from LLM-Driven Proof Search Environment's own cost
surfaces. `research_dossier`'s `observe` action surfaces empirical searches in
their own bucket, separate from proofs, citations, assumptions, candidate
constructions, expert reviews, semantic skeletons, exposition, and verification
layers.

### Paper/PDF ingestion (issue #27)

The empirical math lab and research substrate become useful *before* a Lean
formalization exists when LLM-Driven Proof Search Environment can turn a paper, manuscript, model-written
proof sketch, or human exposition into a structured research workspace. Paper
ingestion records an `ingested_documents` source plus its extracted
`ingested_document_nodes` (abstract, main_theorem, definition, proposition,
lemma, proof_step, construction, remark, appendix_fact, reference, open_gap),
each with a **required** non-empty `source_span` back to the paper text (so no
node is untraceable), a `confidence`, and `formalization_status` /
`citation_status` / `review_status` labels.

**LLM-Driven Proof Search Environment does no OCR/LLM extraction itself** — no inference code lives here. The
host performs extraction and records the structured result, which is **untrusted
by construction**. Ingestion is not verification, and the boundary is
structural:

```text
PDF ingestion            ≠ proof
OCR/LLM extraction        = untrusted
extracted theorem text   ≠ statement-fidelity approval
extracted citation       ≠ citation validation
extracted assumption     ≠ accepted assumption
```

Neither table has a column that can hold kernel evidence; `is_proof` /
`has_kernel_evidence` / `is_statement_fidelity_approved` are always false, and
`formalization_status` is CHECK-constrained to `prose_only` /
`formalization_pending` / `formalization_target_linked` — it can never reach a
proved/verified value. `extraction_trust_status` (unreviewed → machine_extracted
→ human_reviewed_extraction / rejected_extraction / linked_to_dossier_artifact)
tops out at human review, never Lean verification. A `rejected_extraction` stays
visible (never deleted). Extracted nodes are *candidates* that must go through
the normal Lean / fidelity-review / citation / external-theorem paths to gain
any authority. `paper_ingest`'s `link_node` action records that promotion explicitly:
it attaches a node to an `external_reference`, `external_theorem_claim`,
`research_node`, or `formalization_plan_item` that **already exists** (and, for
dossier-scoped kinds, belongs to the document's dossier), setting the node's
derived `citation_status` / `formalization_status` and stamping the matching
forward-link column — but the linked artifact keeps its own independent trust
and the node still gains no proof/kernel authority.
`research_dossier`'s `observe` action shows ingested documents and their nodes
in their own bucket, separate from every proof-bearing bucket.

**Benchmark contamination policy:** upstream benchmarks like PutnamBench ask
that completed formal proofs not be published without first coordinating with
their maintainers. See [docs/benchmarks/putnambench.md](docs/benchmarks/putnambench.md)
for how `proof_export`'s modes and `allow_putnambench_proof_export` flag
enforce this.

### Challenge / task / scoring substrate (issue #53)

AI can generate far more mathematical material than humans can review as full
proofs. Instead of giant opaque proof dumps, LLM-Driven Proof Search Environment channels contributions into
small, bounded, typed, scored, reviewable units:

```text
research_dossier → challenge → task → submission → validation → score → review → distilled artifact
```

A dossier defines a `research_challenge`; a challenge defines bounded
`research_tasks` (`find_candidate_object`, `improve_bound`, `find_counterexample`,
`classify_small_cases`, `produce_witness`, `minimize_example`,
`maximize_parameter`, `verify_property`, `compress_strategy`, `distill_method`,
`formalize_claim`), each with a `bounds_json` that keeps it small; a task accepts
`research_task_submissions` (untrusted `content_json`); a submission is
`validated` against a `validation_protocol`, `scored` (`scoring_results`), and
`reviewed` (`review_results`); accepted work links back to a
`candidate_construction` / `empirical_result` / `verification_layer` as
provenance; and reusable method knowledge is compressed into
`distilled_strategy_artifacts` (`strategy_cheat_sheet`, `heuristic_rule`,
`counterexample_pattern`, `construction_recipe`, `formalization_hint`, …).

**Trust boundary (structural).** Every table here is research bookkeeping — no
column can hold kernel evidence:

```text
challenge/task/score       ≠ proof
accepted submission        ≠ proof
scored submission          ≠ proof
validated empirical result ≠ kernel verification
leaderboard rank           ≠ proof authority
distilled strategy         ≠ proof
```

`is_proof` / `has_kernel_evidence` are always false on every challenge, task,
submission, score, and review; a challenge **score alone never confers training
eligibility**; submission status can never reach a proof value; a link to a
kernel-verified `verification_layer` records provenance only and never makes the
submission a proof. A rejected or superseded submission stays visible (never
deleted), and `challenge_observe` exports the work grouped by outcome
(accepted / rejected / superseded / open shown separately). Only Lean / kernel
verification creates proof authority; challenge state never gates `certified`.

## `Solve` vs. `SubmitModule`

As of v0.3.x, `episode_step` accepts more than a single theorem body:

- **`Solve { proof_term, proof_format? }`** — one theorem: `theorem O_<id> : <statement> := by <proof_term>`. Good for a self-contained tactic proof. `proof_format` (issue #51) is an optional whitespace-transport hint: `flat_tactic_sequence` (default) flattens accidental nesting; `raw_lean_block` preserves the proof's relative indentation for intentional focus-bullet/nested-block structure. It only affects leading whitespace — the Lean kernel remains the sole authority. `SubmitModule`'s `root_theorem` accepts the same field.
- **`SubmitModule { module_items, root_theorem }`** — a small local Lean *development*: helper `def`s, helper `theorem`s, and a root theorem, assembled by the server into one namespaced module and verified as a unit. `module_items` is a list of:
  - `LeanModuleItem::Def { name, type_signature, body }` — `def <name> : <type_signature> := <body>`
  - `LeanModuleItem::Theorem { name, statement, proof_term }` — `theorem <name> : <statement> := by <proof_term>`
  - `LeanModuleItem::MutualGroup { members }` — 2+ `Def`/`Theorem` members that must forward-reference each other (e.g. mutually recursive functions), rendered together inside one server-owned `mutual ... end` block.

The trust boundary is the same one the single-theorem path already has, one
level up: **the model proposes, the server assembles, Lean verifies, the
ledger records.** A client never writes raw Lean — no `import`/`namespace`/
`end`/`set_option` lines, no `axiom`/`opaque`/`unsafe`/`instance`
declarations, never `mutual`/`end` directly (the server owns those tokens
even for a `MutualGroup`). Every name is sanitized to a single namespace-local
identifier, and `root_theorem.statement` must canonical-hash to the problem's
registered root formal statement — a module can never silently prove a
different goal. Verification is **staged and all-or-nothing**: either the
whole module passes the kernel and is recorded, or nothing enters the trusted
namespace.

```jsonc
{
  "type": "submit_module",
  "module_items": [
    { "item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n" }
  ],
  "root_theorem": { "name": "root", "statement": "double 2 = 4", "proof_term": "rfl" }
}
```

Proof soundness vs. statement fidelity (below) is unchanged for module
proofs — a `SubmitModule` root proof reaches the same `kernel_verified`/
`certified` outcomes a `Solve` proof does. A verified module is also a
first-class replayable artifact: `proof_export(format="lean")` can emit the
exact verified module source, and `episode_replay` re-assembles it from the
recorded structured items and re-verifies against the kernel. Full detail,
including the mutual-recursion trust boundary and injection hardening: see
[`docs/submit_module.md`](docs/submit_module.md). For what level of capability
this represents and what's still missing, see [`docs/roadmap.md`](docs/roadmap.md).

## Interactive Proof Sessions

Alongside the whole-proof-attempt actions above (`Solve`, `SubmitModule`,
`Decompose` — all submitted through `episode_step`), the single
`proof_session` tool (issue #161's family, consolidated into one
internally-tagged-action tool by issue #183; part of the
interactive-proof-session epic #158) lets a client work **one** obligation's
goal state tactic-by-tactic — Pantograph-style live proof-state interaction —
instead of only submitting a complete proof and finding out afterward whether
it checked. Every call has the shape
`proof_session {"action": {"type": "<variant>", ...}}`, exactly like
`episode_step`'s typed `action`.

### How this differs from `Solve` / `SubmitModule` / `Decompose`

- **`Solve`** and **`SubmitModule`** are whole-proof-attempt submissions: you
  hand the server a complete tactic script (or module) and the real Lean
  kernel checks it in one pass, via `episode_step`. This remains the only
  family of actions that can mark an obligation `kernel_verified`/`certified`.
- **`Decompose`** splits the current obligation into child sub-lemma
  obligations — still a real, budget-accounted `episode_step` action with no
  session state involved.
- **`proof_session`** sits *beside* `episode_step`, not on top of it: its
  actions let you explore a goal state one tactic at a time, branch to try
  alternatives from an earlier point, and see whether a path closes
  (`is_solved: true`) before committing to a `Solve`/`SubmitModule`
  submission. Nothing in this family changes how `Solve` / `SubmitModule` /
  `Decompose` / `GiveUp` behave, and — with one deliberate exception below —
  no `proof_session` action can change an obligation's status.

### What each action does

| Action (`{"action": {"type": ...}}`) | What it does | Category |
|---|---|---|
| `start` | Starts a new session against one existing episode obligation, backed by an `InteractiveProofGateway` backend (`mock` or `pantograph`). Returns a `session_id` and the root proof-state node. | Starts a session, records initial evidence |
| `observe` | Reads back the session's currently selected node — goals, local context, proof-state hashes, branch summary. | Read-only, records nothing new |
| `tactic_step` | Applies one tactic to a node. Success records a new child node as evidence and moves the session's selected node forward; failure records a structured diagnostic — also evidence, never discarded, a first-class negative example. | Records evidence, advances working state |
| `branch` | Same mechanics as `tactic_step`, framed explicitly as starting a *named* branch from any existing node. Prior branches from the same parent are never deleted or overwritten. | Records evidence, advances working state |
| `select_node` | Moves the session's "selected node" convenience pointer to any existing node in its tree (e.g. to switch which branch you're working). Applies no tactic and records no new evidence. | Working state only |
| `reconstruct` | Builds a Lean tactic script from the root-to-selected-node path and returns it verbatim (raw tactic text for a successful step is *not* durably stored server-side otherwise). `reports_complete` reflects the session's *own* `is_solved` claim — still not a verified proof. | Reconstructs a proof, still search evidence |
| `promote_to_attempt` | **The only action in this family that can change an obligation's status.** Takes a reconstructed script and resubmits it through the exact same `attempt_claim` + `episode_step(Solve)` path a normal whole-proof submission uses — a real, from-scratch Lean kernel check. | Final verification |
| `close` | Marks a session `closed` / `abandoned` / `superseded`. The session's full trace (every node/step, including failed tactics) stays visible and queryable afterward — closing never deletes anything. | Session lifecycle only |
| `replay` | Replays a session from *persisted DB state* in one of three modes: `trace_only` (pure DB-consistency check, no kernel call), `backend` (re-runs the tactic path against a fresh backend session and compares outcomes/hashes), `final_proof` (resubmits through the real verification path). | `trace_only`/`backend`: evidence check only. `final_proof`: final verification |
| `export` | Exports one session's trace as `public_summary` (aggregate counts only, no tactic/goal text), `audit_archive` (full trace, hashes, reconstructed-script linkage), or `training_export` (per-step records including negative-space failed routes). | Read-only export of already-recorded evidence |

### The loop

```text
proof_session {"action": {"type": "start", ...}}
    │  (root node)
    ▼
proof_session {"action": {"type": "tactic_step" / "branch" / "select_node", ...}}   ← repeat, explore, branch
    │  (some node reports is_solved: true)
    ▼
proof_session {"action": {"type": "reconstruct", ...}}          ← builds a tactic script from root → selected node
    │
    ▼
proof_session {"action": {"type": "promote_to_attempt", ...}}   ← the ONLY step that can change obligation status:
                                                                     attempt_claim + episode_step(Solve) through the
                                                                     real Lean kernel, exactly like a direct Solve call
```

The `replay` action with `mode="final_proof"` is an alternate route to the
same trust gate for a closed or historical session — it reconstructs and
resubmits through the same internal `attempt_claim` + `episode_step(Solve)`
logic, not a second, parallel verification path.

### The trust boundary

**Every `proof_session` result — a session's state, a tactic-application
outcome, a reconstructed script, a replay result — is search evidence, never
proof authority.** A node reporting `is_solved: true` is only the session's
own internal claim; the deterministic `mock` backend (the only backend that
actually steps tactics today) closes the first open goal on every
syntactically nonempty tactic string, without ever asking a real elaborator
whether that tactic discharges the goal. The only way an interactive session
can change an obligation's status is the `reconstruct` action followed by
`promote_to_attempt` (or `replay` with `mode="final_proof"`) — both route
through the exact same `attempt_claim` + `episode_step(Solve)` internal path,
the real Lean kernel, that every direct `Solve` submission already uses. If a
future backend's own elaborator ever disagrees with the kernel, the kernel
wins, always.

Do not report a goal as proved, or an obligation as closer to done, based on
`tactic_step` / `observe` / `branch` / `select_node` / `reconstruct` output
alone — only a `promote_to_attempt` (or `replay` `mode="final_proof"`) result
backed by a real kernel verdict counts.

### Backend choices

- **`mock`** (default) — a deterministic, in-memory test double: no Lean
  process, no Pantograph, no I/O. Always available; useful for exercising the
  full start → step → branch → reconstruct → promote loop mechanically, but
  its tactic outcomes carry no real elaboration evidence — it closes the
  first open goal on any nonempty tactic string, correct or not.
- **`pantograph`** — a *recognized* backend value, not yet a *usable* one.
  `PantographInteractiveGateway` (issue #166) runs a real filesystem/PATH
  probe for a compatible Pantograph installation (binary on `PATH`,
  `lake-manifest.json` dependency, a fetched checkout, a matching
  `lean-toolchain`) and reports specifically which of those conditions is
  missing — but this prototype has no process-spawning/IPC implementation
  behind it, so every operation fails closed regardless of what the probe
  finds, including the most favorable case (a fetched Pantograph checkout
  whose toolchain matches this project's own exactly). Check
  `environment_describe`'s `pantograph_available` / `pantograph_reason`
  fields before assuming Pantograph is usable in a given environment —
  `pantograph_available` is `false` in every configuration this prototype can
  currently detect.

Results from either backend remain subject to the trust boundary above
regardless of how "confident" the backend's own internal state looks.

See [`docs/roadmap.md`](docs/roadmap.md)'s Level 2.5 section for where this
capability sits relative to whole-module verification (Level 2) and
formalization planning (Level 3), and how its failed-tactic records feed
negative-space training/export value.

## Drafts and formalization planning (Level 3)

Before a `Solve`/`SubmitModule` attempt, a client can preserve informal
reasoning as a **Draft** (`draft_create`) and record the moves it identifies
within it (`draft_extract_moves` — construction, auxiliary_lemma, case_split,
induction, reduction, bijection, counterexample_search, asymptotic_step,
external_citation, unknown). Selected moves can seed a **formalization
plan** — since issue #184 the whole plan family is the single
`formalization_plan` tool, dispatching on an internally-tagged action
(`formalization_plan {"action": {"type": "create", ...}}`, exactly like
`episode_step`) — which tracks planned concepts, definitions, lemmas, and
modules together with their Mathlib coverage status (the `attach_lookup`
action, using `lean_declaration_lookup` results, or the
`attach_librarian_result` action, using `mathlib_search_declarations` /
`mathlib_search_local_artifacts` results).

Both are strictly advisory, mirroring the trust boundary everywhere else in
this environment: a Draft or a plan item can never mark anything proved.
Real obligations are still created only through `Decompose`, via the normal
budget-accounted `episode_step` flow — the `promote_item_to_obligation`
action only records a metadata *link* to an obligation that already exists
that way; it never creates one itself. See `docs/roadmap.md`'s Level 3
section for the full design.

## Proof soundness vs. statement fidelity

These are independent claims, and the environment never conflates them:

- **Proof soundness** — the Lean kernel verified this exact formal statement. Reaching this alone yields `outcome: "kernel_verified"`.
- **Statement fidelity** — that formal statement actually represents the source problem. Only `problem_submit_fidelity_review(decision="verified")` can establish this, based on evidence the server independently hash-checks against the problem's *current* source/statement/rendering (a stale or mismatched submission is rejected, not silently accepted).

`outcome: "certified"` requires **both** — a kernel-verified root can never present as certifying the source claim on proof soundness alone. This closes a real exploit: a trivially-true weakening of a source problem (e.g. proving `∀ n, Even n → True` for the claim "every even natural is divisible by two") kernel-verifies but must never be reported, rewarded, or exported as if it certified the source claim. See `docs/fix_plan_playtest_02.md`.

Two ways to unlock proving:
- **Real review**: `problem_submit_fidelity_review(decision="verified", ...)` → `fidelity_status="verified"` → root proof reaches `certified` directly (or promotes retroactively if the root was already `kernel_verified`).
- **Dev bypass**: `problem_create(unsafe_dev_attestation=true)` → `fidelity_status="attested"` → proving is allowed, but the episode can only ever reach `kernel_verified`, never `certified` — and problems/episodes under `attested` are excluded from default dataset exports (`training_eligible=false`).

A minimal prover loop is: `problem_create` → `problem_submit_fidelity_review` (or `unsafe_dev_attestation=true` for dev use) → `episode_create` → `episode_observe` → `attempt_claim` → `episode_step` → repeat `episode_observe`/`attempt_claim`/`episode_step` until `outcome` is set.

## Import manifests and "environmental scope collapse"

Every problem version has an immutable import manifest — the exact set of Mathlib modules its proofs are checked against (base: `Mathlib.Tactic.Ring` + `Mathlib.Tactic.NormNum`; extend it via `problem_create(problem_imports=[...])`, each validated with a real compile check before acceptance). Import strings and `lean_declaration_lookup` names are written verbatim into Lean source, so both are restricted to plain identifier syntax (dot-separated `[A-Za-z_][A-Za-z0-9_]*` segments for imports; no whitespace/comment/command syntax for declaration names) and capped at 50 entries per call — anything else is rejected before it ever reaches Lean, never silently compiled. See `docs/fix_plan_playtest_04.md`.

**An `unknown_declaration` diagnostic only ever proves a name didn't resolve under that exact manifest — it never proves the name is absent from the pinned Mathlib.** Before either changing proof strategy or declaring an API unavailable, call `lean_declaration_lookup`.

By default the lookup only checks the problem's own manifest — a few seconds, since it doesn't load all of Mathlib:

- **`available`** — resolves under the current manifest.
- **`not_available_under_current_manifest`** — doesn't resolve under the current manifest. **This alone does not prove absence from the library** — call again with `deep_check=true` to get a conclusive verdict.
- **`environment_error`** — the lookup itself failed; not evidence either way.

Pass `deep_check=true` to additionally check under the full Mathlib umbrella (slow — reliably 15-40+ seconds, since it loads all of Mathlib) and get a conclusive verdict:

- **`not_in_current_import_scope`** — resolves under the full umbrella but not the current manifest → add the module via a new `problem_create(problem_imports=[...])`.
- **`unknown_declaration`** — doesn't resolve even with everything imported → genuinely try a different name.

Conflating "not available under the current manifest" with "the library doesn't have this" — is a real failure mode we call **environmental scope collapse**: a local fact about one import closure gets inflated into a global claim about library capability, which can cascade into a model abandoning a provable branch. `environment_describe` carries this as an explicit epistemic rule for any agent driving the loop. Diagnostics also distinguish `unknown_declaration` (name resolution) from `parse_error` (syntax) and other categories — see `docs/fix_plan_playtest_03.md`. The fast-default/opt-in-deep split exists because the unconditional umbrella check was slow enough to blow past MCP client tool-call timeouts — see `docs/fix_plan_playtest_04.md`.

Import manifests are immutable per problem_version and included in every observation/trajectory event as `import_manifest_hash`, so replay always re-verifies against the exact closure the original attempt used.

## Prerequisites

- **Rust** (2024 edition) — install via [rustup](https://rustup.rs/)
- **Lean 4 toolchain manager (elan)** — install via [elan](https://github.com/leanprover/elan):
  ```powershell
  # On Windows, you can use the included bootstrap script:
  .\elan-init.ps1
  ```
- **The `lean-checker` Lake project** — see [Lean Checker Setup](#lean-checker-setup) below. Without it, `solve` actions fail with an infrastructure error; every other tool (episode lifecycle, decompose, trajectories, dataset export) works without it.

## Lean Checker Setup

`PROOFSEARCH_LEAN_PROJECT_PATH` (default `./lean-checker`) must point at a [Lake](https://github.com/leanprover/lake) project that depends on [Mathlib](https://github.com/leanprover-community/mathlib4). Every problem version has its own immutable **import manifest** — the exact Mathlib modules its proofs (and its `SubmitModule` developments) are checked against, starting from a base of `Mathlib.Tactic.Ring` + `Mathlib.Tactic.NormNum` (`omega` comes with core Lean once any Mathlib module is imported) and extendable per-problem via `problem_create(problem_imports=[...])` — each additional module is validated with a real compile check before the problem is accepted, not merely a name-shape check (`crates/proofsearch-core/src/lean/mod.rs`). This is not a single hardcoded import list baked into the gateway; see [Import manifests and "environmental scope collapse"](#import-manifests-and-environmental-scope-collapse) above. Setting up the Lake project itself is a one-time, multi-gigabyte task — do it once per machine, not per session:

```powershell
# 0. (Optional but recommended on machines with a small C: drive) Keep the multi-GB
#    toolchain store off the system drive. Match this with PROOFSEARCH_ELAN_HOME in the
#    MCP server env so the server's Lean subprocesses resolve the same store.
$env:ELAN_HOME = "F:\lean\elan"

# 1. Scaffold a Lake project pinned to Mathlib's toolchain (skip if lean-checker/ exists).
#    The math template runs `lake update` itself, cloning mathlib + deps.
lake +leanprover-community/mathlib4:lean-toolchain new lean-checker math
cd lean-checker

# 2. Download Mathlib's prebuilt .olean cache (do NOT build from source —
#    that takes hours; the cache download takes minutes)
lake exe cache get

# 3. Verify the toolchain resolves and a trivial proof compiles
@'
import Mathlib.Tactic.NormNum
theorem t : (1:Nat) + 1 = 2 := by norm_num
'@ | Out-File -Encoding utf8 smoke.lean
lake env lean --json smoke.lean
```

If step 3 prints no `"severity":"error"` JSON lines, the gateway is ready. Point `PROOFSEARCH_ELAN_BIN_PATH` at the `.elan/bin` directory containing `lake.exe`/`lean.exe` (default `~/.elan/bin`), and `PROOFSEARCH_LEAN_PROJECT_PATH` at the `lean-checker/` directory itself (the one containing `lakefile.toml`). The server checks both paths at startup and reports readiness via `environment_describe`'s `lean_gateway` field (`"ready"` or `"unavailable"`) — an `"unavailable"` warning is also printed to stderr on stdio startup.

The gateway copies every kernel-passing proof into `lean-checker/LeanChecker/Verified/O_<id>.lean` and `lake build`s it so later obligations can `import` it as an approved dependency — keep that directory out of `.gitignore` exclusions if you want to inspect proved lemmas after a run.

## Build

```bash
# Debug build (fast compile, slower runtime)
cargo build

# Release build (optimized binary)
cargo build --release
```

The MCP server binary will be at:
- Debug: `target/debug/proofsearch-mcp.exe`
- Release: `target/release/proofsearch-mcp.exe`

## Run Tests

```bash
cargo test
```

This runs the full test suite across both crates:

| Test Suite | What It Verifies |
|---|---|
| `p0_migration_baseline` | Schema v0 → v1 migration safety |
| `architecture_test` | No provider SDKs in `proofsearch-core` |
| `phase5_lifecycle_tests` | Episode create / reset / advance lifecycle |
| `phase6_attempts_tests` | Crash-recovery attempt state machine |
| `phase8_step_tests` | Atomic CAS step with budget deduction |
| `phase9_trajectories_tests` | Hash-chained recording and tamper detection |
| `phase11_dataset_tests` | SFT/RL/DPO export and sanitization |
| `phase12_conformance_tests` | Production path matches replay path |
| `proofsearch-mcp` lib tests | Full MCP client↔server play-throughs over duplex transport: tool listing, decompose→give_up, solve→certified (mock Lean gateway), solve→kernel_fail (non-terminal), fabricated-claim/stale-revision rejection, idempotent claim retry |

## Register as MCP Server

### Claude Desktop

Add to `%APPDATA%\Claude\claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "proofsearch": {
      "command": "F:\\Github\\mnehmos.llm-driven-proof-search.environment\\target\\release\\proofsearch-mcp.exe",
      "args": ["proofsearch.db"],
      "env": {
        "PROOFSEARCH_LEAN_PROJECT_PATH": "F:\\Github\\mnehmos.llm-driven-proof-search.environment\\lean-checker",
        "PROOFSEARCH_ELAN_BIN_PATH": "C:\\Users\\mnehm\\.elan\\bin"
      }
    }
  }
}
```

### Cline / Roo Code

Add to your `mcp_settings.json`:

```json
{
  "mcpServers": {
    "proofsearch": {
      "command": "F:\\path\\to\\target\\release\\proofsearch-mcp.exe",
      "args": ["proofsearch.db"],
      "env": {
        "PROOFSEARCH_LEAN_PROJECT_PATH": "F:\\path\\to\\lean-checker",
        "PROOFSEARCH_ELAN_BIN_PATH": "C:\\Users\\you\\.elan\\bin"
      },
      "disabled": false
    }
  }
}
```

### ChatGPT (via OpenAI Tunnel or Direct HTTP)

ChatGPT requires an HTTP endpoint speaking the MCP SSE transport. Start the server in `http` mode:

```bash
proofsearch-mcp.exe --transport http --port 8080 proofsearch.db
```

Then, use a tunneling solution like the [OpenAI Secure MCP Tunnel](https://github.com/openai/tunnel-client) or `ngrok` to expose it, and register the resulting HTTPS URL in your OpenAI platform settings as a Server URL.

```bash
# Example using OpenAI tunnel-client
tunnel-client run --tunnel-id <YOUR_TUNNEL_ID> --mcp-command "proofsearch-mcp.exe --transport http --port 8080 proofsearch.db"
```

> **Known transport property:** some web/hosted MCP surfaces (observed with claude.ai web connectors)
> strip MCP error *bodies* down to a bare failure — the server's diagnostic messages
> (claim expiry timestamps, action-shape hints, etc.) are only visible on transports that
> relay them, such as Claude Desktop stdio or a raw JSON-RPC client. On stripped surfaces,
> diagnose via state probes instead: `episode_status`, `episode_observe`, `problem_list`.

### Programmatic (Python / Any stdio MCP client)

```python
import subprocess, json

proc = subprocess.Popen(
    ["target/release/proofsearch-mcp.exe", "proofsearch.db"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    env={
        "PROOFSEARCH_LEAN_PROJECT_PATH": "./lean-checker",
        "PROOFSEARCH_ELAN_BIN_PATH": "~/.elan/bin",
    }
)
# Send JSON-RPC 2.0 messages over stdin/stdout
```

## Environment Variables

| Variable | Default | Description |
|---|---|---|
| `PROOFSEARCH_DB_PATH` | `proofsearch.db` | SQLite database path (also settable as first CLI arg) |
| `PROOFSEARCH_LEAN_PROJECT_PATH` | `./lean-checker` | Path to the Lean 4 project used for verification |
| `PROOFSEARCH_ELAN_BIN_PATH` | `~/.elan/bin` | Path to the directory containing the `lake`/`lean` elan proxy binaries |
| `PROOFSEARCH_ELAN_HOME` | *(unset)* | If set, exported as `ELAN_HOME` to Lean subprocesses — the elan **root** where `toolchains/` lives. Use this to keep multi-GB toolchains off the system drive (e.g. `F:\lean\elan`). When unset, elan uses the process env / `~/.elan` |

## Episode Lifecycle

```
episode_create(problem_version_id)
    │
    ▼
┌──────────────────────┐
│ awaiting_external_    │◀──────────────────────────────┐
│ action                │                               │
└──────────┬───────────┘                               │
           │  episode_observe()                         │
           │  → observation + action_request            │
           ▼                                            │
    attempt_claim(action_request_id, idempotency_key)    │
           │  → action_attempt_id + claim_token          │
           ▼                                            │
    ┌──────────────┐                                    │
    │ Host calls   │                                    │
    │ external LLM │  (outside LLM-Driven Proof Search Environment)                  │
    └──────┬───────┘                                    │
           │                                            │
           ▼                                            │
    episode_step(action_attempt_id, claim_token, revision, action)
           │                                            │
           ├── Solve → Lean verifies ──┐                │
           │                           ▼                │
           │                    ┌─────────────┐         │
           │                    │ KernelPass  │──▶ root proved ──▶ terminated(certified)
           │                    └─────────────┘         │
           │                                            │
           │                    ┌─────────────┐         │
           │                    │ KernelFail  │──▶ next obligation
           │                    └─────────────┘─────────┘
           │
           ├── SubmitModule → staged, all-or-nothing Lean module verification ──┐
           │        (defs + helper theorems + root theorem, one namespace)      │
           │                                            ▼                      │
           │                    ┌─────────────┐  whole module passes           │
           │                    │ KernelPass  │──▶ root proved ──▶ terminated(certified)
           │                    └─────────────┘                                │
           │                    ┌─────────────┐  policy rejection OR           │
           │                    │ KernelFail  │  any declaration fails ──▶ next obligation
           │                    └─────────────┘  (nothing enters the trusted namespace)
           │
           ├── Decompose → child obligations ──▶ next (child) obligation
           ├── GiveUp ──▶ terminated(gave_up)
           ├── budget_exhausted / max_steps_reached ──▶ truncated(budget_exhausted)
           └── stale revision / invalid claim ──▶ rejected, retry (episode unchanged)
```

## Dataset Export

LLM-Driven Proof Search Environment produces training-grade synthetic data:

- **SFT records** — (prompt, completion) pairs from committed steps
- **RL tuples** — (s, a, r, s', terminated, truncated, info) from trajectory events
- **DPO pairs** — (prompt, chosen, rejected) from accepted vs. rejected attempts
- **Contamination-safe splits** — deterministic train/validation/test by theorem lineage hash
- **Sanitized trajectories** — API keys, credentials, and private endpoints automatically scrubbed
- **Dataset manifests** — checksums, lineage hashes, and sanitization policy metadata

## Project Structure

```
├── Cargo.toml                    # Workspace root
├── crates/
│   ├── proofsearch-core/              # Engine library (zero network dependencies)
│   │   ├── src/
│   │   │   ├── db/               # Schema, migrations, queries
│   │   │   ├── lean/             # Sandboxed Lean 4 gateway
│   │   │   ├── models/           # Typed data contracts
│   │   │   ├── orchestrator/     # Lifecycle, step, trajectories, dataset
│   │   │   ├── hashing.rs        # RFC 8785 JCS canonical hashing
│   │   │   └── schema_export.rs  # JSON Schema 2020-12 generation
│   │   └── tests/                # Integration test suites
│   └── proofsearch-mcp/               # MCP server (thin shell over core)
│       ├── src/lib.rs            # 86 tools, rmcp 1.8.0, 2025-11-25 — ServerHandler + tests
│       └── src/main.rs           # CLI: stdio/http transport wiring only
├── docs/
│   ├── adr/                      # Architecture Decision Records
│   ├── playtests/                # Dated playtest reports (real-toolchain sprints, lessons learned)
│   ├── roadmap.md                # Capability levels (0-6) and what each requires
│   └── submit_module.md          # SubmitModule / mutual recursion trust boundary and mechanics
├── fixtures/                     # Test fixtures
└── PROOFSEARCH_SPEC.md                # Full specification document
```

## Design Decisions

Architectural decisions are recorded in [`docs/adr/`](docs/adr/):

- **ADR-0001** — Lean sandbox platform isolation strategy
- **ADR-0002** — Canonical vs. episode-local storage separation
- **ADR-0003** — Hash-chained trajectory design

## Playtests and roadmap

- [`docs/roadmap.md`](docs/roadmap.md) — capability levels (0 through 6), what
  v0.3.1 actually reaches (Level 2), and what each subsequent level requires.
- [`docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md`](docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md) —
  a real-toolchain playtest sprint covering algebraic inequalities, induction,
  structural/well-founded/mutual recursion, and list predicates, with full
  proof exports and reusable proof-pattern lessons.
- [`docs/librarian.md`](docs/librarian.md) — the Mathlib librarian's
  architecture, trust boundary, confidence vocabulary, and deliberate MVP
  scope cuts (issue #25).

## License

MIT
