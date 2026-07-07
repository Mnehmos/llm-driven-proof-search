# LLM-Driven Proof Search Environment Proof Core Rebuild Specification

**Document:** `PROOFSEARCH_SPEC.md`  
**Status:** Implementation specification, revised for MCP-only external model execution and headless RL environment  
**Scope:** Ground-up rebuild of the LLM-Driven Proof Search Environment proof core  
**Primary input:** `PROOFSEARCH_REVIEW.md`  
**Normative language:** `MUST`, `MUST NOT`, `SHOULD`, `SHOULD NOT`, and `MAY` are requirements terms.

## Design basis

The rebuilt core adopts a strict **Draft -> Sketch -> Certificate** pipeline, derived from the Draft, Sketch, and Prove separation introduced by Jiang et al. and reinforced by later systems that use recursive subgoal decomposition, verified lemma libraries, and compiler-guided repair.

Primary research references:

- Albert Q. Jiang et al., *Draft, Sketch, and Prove: Guiding Formal Theorem Provers with Informal Proofs*, arXiv:2210.12283.
- Azim Ospanov and Roozbeh Yousefzadeh, *APOLLO: Automated LLM and Lean Collaboration for Advanced Formal Reasoning*, arXiv:2505.05758.
- Haiming Wang et al., *LEGO-Prover: Neural Theorem Proving with Growing Libraries*, arXiv:2310.00656.
- DeepSeek-AI, *DeepSeek-Prover-V2: Advancing Formal Mathematical Reasoning via Reinforcement Learning for Subgoal Decomposition*, arXiv:2504.21801.
- Sumanth Varambally et al., *Hilbert: Recursively Building Formal Proofs with Informal Reasoning*, arXiv:2509.22819.

The prior audit is authoritative for the redesign. Audit references in this specification use the form `[Audit T-01]`, `[Audit C-03]`, or `[Audit §10.2]` and refer to `PROOFSEARCH_REVIEW.md`.

---

# 1. Goal and non-goals

## 1.1 Goal

The rebuilt LLM-Driven Proof Search Environment proof core SHALL accept an immutable natural-language problem, bind it to an approved Lean root theorem, discover and discharge a dynamically growing obligation graph, produce a kernel-checked proof of the root theorem, and stop only when a deterministic coverage-convergence policy is satisfied.

The proof core itself SHALL NOT call an LLM provider. All model inference occurs in an external agent host that connects to LLM-Driven Proof Search Environment through MCP. LLM-Driven Proof Search Environment emits bounded role requests and observations; the external host selects and invokes a model; the resulting typed action is submitted back through MCP for deterministic validation and state transition.

The smallest correct proof system has seven required capabilities, and the complete LLM-Driven Proof Search Environment product has two additional execution capabilities:

1. Immutable problem versioning with a mandatory formal root theorem.
2. A Draft artifact for informal planning.
3. A single authoritative Sketch graph of formal obligations and dependency edges.
4. A versioned MCP role-and-action contract through which external models submit Drafts, formalizations, decompositions, proof proposals, repairs, and review proposals.
5. A supervised Lean service that is the sole authority for proof discharge.
6. Reviewer epochs that can add formal coverage obligations but cannot establish truth.
7. A hard budget governor and append-only event history.
8. A versioned headless environment protocol that exposes reproducible proof episodes through reset, observe, step, terminate, truncate, replay, and export operations.
9. An MCP server and external runner contract that allow independently hosted models to operate the environment and generate verifier-backed synthetic training trajectories without placing provider code or credentials inside LLM-Driven Proof Search Environment.

A run is successful only when both conditions hold:

```text
KERNEL_SUCCESS  := the exact root theorem has a passing Lean kernel artifact
COVERAGE_SUCCESS := the deterministic reviewer-convergence policy is satisfied
COMPLETE         := KERNEL_SUCCESS and COVERAGE_SUCCESS and no integrity block
```

Kernel success and coverage success MUST remain separate fields. The interface MUST never imply that reviewer convergence proves the theorem. Lean proves the theorem. Reviewer convergence only establishes that the system has stopped discovering substantive uncovered regions under the configured review policy.

## 1.2 Product behavior

The rebuilt core SHALL:

- Preserve an immutable source problem and formal root theorem per problem version.
- Emit a typed Draft request through MCP when informal planning is required and accept the external agent's Draft as an untrusted proposal artifact.
- Emit typed formalization and decomposition requests through MCP and admit only outputs that pass deterministic schema, graph, fidelity, and Lean checks.
- Treat proof-structuring moves as graph topology, not as theorem facts.
- Discharge every proved obligation with an exact Lean theorem artifact.
- Verify that non-leaf obligations compose verified dependencies.
- Use structured Lean diagnostics to drive externally generated repair proposals.
- Allow the obligation graph to grow during diverse reviewer epochs using reviewer proposals submitted through MCP.
- Enforce internal Lean, tool, action, and wall-time budgets before every LLM-Driven Proof Search Environment-controlled operation.
- Issue model-call budget leases through MCP for trusted external runners without owning provider credentials or invoking provider APIs.
- Expose a stable core API that the existing Tauri UI can consume.
- Persist enough information to reproduce and audit every proof-state transition.
- Expose the same proof-state machine through a headless environment service that does not require Tauri, a browser, or a human operator.
- Allow MCP-capable agent hosts to discover the environment, create isolated episodes, observe bounded proof state, submit typed actions, and receive structured Lean diagnostics.
- Produce append-only, replayable trajectories suitable for evaluation, supervised fine-tuning, preference construction, and reinforcement learning.
- Keep reward calculation, termination, and proof status under deterministic environment and Lean authority rather than model self-report.
- Remain fully functional as a deterministic verifier and state machine when no model host is connected; the run waits in an explicit `awaiting_external_action` state rather than making an internal model call.

## 1.3 Explicit non-goals

The proof core SHALL NOT include the following behaviors or subsystems.

### Removed acceptance mechanisms

- No LLM truth votes.
- No tally-based satisfaction subsystem.
- No solver self-assessment as closure evidence.
- No reviewer, adversary, critic, or council verdict that can mark an obligation proved.
- No SymPy, Pint, numeric sampler, or heuristic that can mark an obligation proved.
- No automatic conclusion object.
- No conclusion reviewer.
- No fail-open path on missing responses, parser failures, timeouts, or exceptions.
- No inherited trust in any existing `verified` database value.

These are direct cuts required by `[Audit T-01]`, `[Audit T-02]`, `[Audit T-03]`, `[Audit T-04]`, `[Audit S-01]`, and `[Audit S-02]`.

### Removed graph and state duplication

- No parallel `steps`, `proof_nodes`, JSON dependency arrays, and generalized DAG representations.
- No duplicate parent ID fields that compete with the dependency-edge table.
- No proof state reconstructed from natural-language step chains.
- No second closure state machine beside the obligation state.

These are direct cuts required by `[Audit §2.2]` and `[Audit §8.1]`.

### No internal model execution

- No provider SDK in the LLM-Driven Proof Search Environment proof-core process.
- No OpenAI, Anthropic, Google, local-model, or other LLM API credentials stored by LLM-Driven Proof Search Environment.
- No internal `LlmClient`, `ModelGateway`, proposer client, reviewer client, or provider retry loop.
- No background model invocation by the orchestrator.
- No direct model call from Tauri, Rust core, Lean service, database layer, or export subsystem.
- No hidden fallback model when an external agent is unavailable.
- No proof-state transition caused by the absence, timeout, or failure of an external model host.

Models are external policy actors. They interact with LLM-Driven Proof Search Environment only through the versioned MCP observation and action contract.

### Removed hot-path agent roles

- No satisfaction reviewer.
- No satisfaction adversary.
- No conclusion reviewer.
- No hot-path critic with no state effect.
- No post-success pattern extraction inside the proof transaction.
- No separate re-decomposition subsystem.
- No LLM-based retry/done classifier.

A reviewer MAY propose a new formal obligation. It MUST NOT accept, reject, close, or certify an existing theorem.

### Moved outside the core

The following MAY exist as optional adapters or offline jobs, but the proof transaction MUST NOT depend on them:

- Research search.
- Theorem retrieval.
- Pattern mining.
- Training-pair extraction inside the trusted proof transaction. Synthetic-data derivation belongs to the headless environment and offline export subsystem defined in Section 13.
- Corpus embeddings.
- After-action reports.
- Analytics dashboards.
- External evidence extraction.
- Multi-proposer portfolio search.

### Not a natural-language proof verifier

The system SHALL NOT attempt to verify the Draft line by line. Informal moves such as “without loss of generality,” “consider,” “suppose,” “split into cases,” or repeated explanatory statements are not proof obligations by themselves. The Draft is planning material. The Sketch is the formal proof surface.

## 1.4 KISS component test

A component belongs in the core only if removing it would violate a hard invariant.

| Component | Invariant served | Core status |
|---|---|---|
| Problem version and fidelity approval | Invariant 6 | Required |
| Draft artifact | Draft-Sketch separation and capability-gated planning | Required |
| Obligation and edge tables | Invariants 5 and 10 | Required |
| Scheduler | Deterministic progress and cost control | Required |
| MCP role-and-action contract | External candidate generation without internal model calls | Required product boundary |
| Lean service | Invariants 1 through 5 | Required |
| Reviewer epochs | Coverage discovery and convergence | Required |
| Budget governor | Invariant 9 | Required |
| Event log | Reproducibility and audit | Required |
| Headless environment service | Reproducible model interaction, evaluation, and trajectory generation | Required product layer |
| MCP adapter | Model-callable execution surface over the headless environment | Required product adapter |
| External MCP runner contract and trajectory exporter | Synthetic RL data generation without provider code in LLM-Driven Proof Search Environment | Required product boundary |
| SymPy/Pint preflight | Faster rejection only | Optional |
| Search/retrieval | Bounded hint source | Optional |
| Pattern library | Future optimization | Offline or optional |
| Council/critic/satisfaction roles | No invariant | Removed |

---

# 2. The three artifacts

## 2.1 Artifact A: Draft

### Purpose

The Draft is an external policy model’s informal mathematical reasoning and plan, submitted through MCP. It exists to capture the high-capability reasoning that is difficult to replace with a cheaper prover model, especially for olympiad-level or research-style problems.

The Draft MAY contain:

- Intuition.
- Candidate constructions.
- Case splits.
- WLOG moves.
- Contradiction plans.
- Intermediate claims.
- Redundant explanations.
- Alternative approaches.
- Open uncertainties.

The Draft is not a proof certificate and has no verified status.

### Draft data model

```text
Draft
- id: UUID
- problem_version_id: UUID
- source_problem_hash: Hash
- external_agent_config_hash: Hash
- declared_model_config_hash: Optional<Hash>
- prompt_template_hash: Hash
- content_artifact_hash: Hash
- natural_plan: Text
- extracted_moves: DraftMove[]
- created_at: Timestamp
```

```text
DraftMove
- ordinal: Integer
- kind: case_split | wlog | construction | contradiction | induction |
        rewrite | reduction | auxiliary_lemma | heuristic | unknown
- label: String
- source_span: Optional<TextSpan>
- natural_description: Text
```

`extracted_moves` are metadata for the Sketch compiler. They are not propositions and MUST NOT appear in the obligation table.

### Allowed Draft inputs

- Immutable natural-language problem text.
- Approved background domain metadata.
- Allowed theorem-library summary.
- Bounded retrieved hints, when enabled.
- Prior Draft only when explicitly creating a new Draft revision.

### Forbidden Draft outputs

The Draft MUST NOT directly:

- Create a proved obligation.
- Create a certificate.
- Change the root theorem.
- Mark anything verified.
- Send a natural-language chain to Lean.
- Become automatic context for a prover attempt.

### Boundary rule

The raw Draft MAY cross only into the Sketch compiler and the human fidelity review interface. It MUST NOT cross into the Lean verifier or the normal obligation-discharge prompt.

## 2.2 Artifact B: Sketch

### Purpose

The Sketch is the single authoritative formal proof graph. Every active node is a proposition. Every proof dependency is an edge. Proof-structuring moves from the Draft become topology.

Examples:

- A Draft case split becomes multiple child obligations plus a parent composition obligation.
- A Draft “WLOG” move becomes a symmetry lemma and a composition dependency, not a node called “WLOG.”
- A Draft construction becomes an existence or witness obligation.
- Two Draft sentences that assert the same proposition become one normalized obligation.

### Sketch data model

The Sketch is represented by exactly two authoritative structures:

```text
Obligation
- id: UUID
- problem_version_id: UUID
- kind: root | proof | coverage | counterexample
- theorem_name: LeanIdentifier
- lean_statement: Text
- statement_hash: Hash
- natural_description: Text
- status: open | in_progress | proved | refuted | superseded |
          abandoned | blocked_needs_human
- depth_from_root: Integer
- created_by: initial_sketch | decomposition | reviewer | human
- created_by_epoch_id: Optional<UUID>
- superseded_by_id: Optional<UUID>
- proved_lemma_id: Optional<UUID>
- refutation_lemma_id: Optional<UUID>
- failure_lesson: Optional<Text>
- attempt_count: Integer
- created_at: Timestamp
- closed_at: Optional<Timestamp>
```

```text
ObligationEdge
- parent_obligation_id: UUID
- dependency_obligation_id: UUID
- edge_kind: lemma | case_branch | witness | reduction
- case_group: Optional<String>
- created_at: Timestamp
```

Edge orientation is:

```text
parent_obligation_id DEPENDS ON dependency_obligation_id
```

All active edges are required. There is no optional proof dependency. If a lemma is not required by the active composition plan, it MUST NOT have an active edge.

### Node classes

A leaf obligation has no outgoing dependency edges.

A composition obligation has one or more outgoing dependency edges. Its Lean proof MUST reference every required direct dependency theorem. This includes the root obligation when the active Sketch decomposes the root.

The root obligation’s `lean_statement` MUST be exactly the approved root theorem statement under Lean definitional equality.

### Sketch immutability rules

- `lean_statement` and `statement_hash` are immutable after admission.
- Changing a statement creates a new obligation and marks the old obligation `superseded`.
- Changing the root theorem creates a new `problem_version` and invalidates all old proof artifacts for the new run.
- Edges are append-only in the event history. Active edge deletion is represented by superseding the affected composition obligation, not by silently rewriting history.
- The graph MUST remain acyclic.

### Sketch admission checks

Before an obligation becomes active, code MUST verify:

1. The statement parses and elaborates in the pinned Lean environment.
2. The theorem name is unique within the problem namespace.
3. The statement hash is not an exact duplicate of an active obligation.
4. The new edges do not create a cycle.
5. Every referenced dependency belongs to the same problem version.
6. The statement does not introduce unauthorized imports, axioms, or namespaces.
7. The child count and decomposition depth obey Section 7.
8. Any case group has at least two distinct branches.

A reviewer or model confidence value MAY be stored as event metadata, but MUST NOT affect proof status.

### Allowed Sketch inputs

- Approved root theorem.
- Draft and extracted Draft moves.
- Existing theorem signatures.
- Structured Lean diagnostics.
- Reviewer-proposed formal obligations.
- Human-authored obligations.

### Forbidden Sketch inputs

- Existing legacy `verified` values.
- Satisfaction tallies.
- Sample-based “proof” outcomes.
- Natural-language-only closure claims.
- Reviewer truth verdicts.

## 2.3 Artifact C: Certificate

### Purpose

The Certificate is the immutable, reproducible output of the formal proof transaction. It proves that the exact root theorem was accepted by the pinned Lean kernel in an approved environment and records the verified lemma dependency closure.

### Certificate data model

```text
Certificate
- id: UUID
- problem_version_id: UUID
- root_obligation_id: UUID
- root_verified_lemma_id: UUID
- root_statement_hash: Hash
- root_proof_artifact_hash: Hash
- proof_dependency_manifest_hash: Hash
- active_sketch_snapshot_hash: Hash
- lean_version: String
- mathlib_revision: String
- toolchain_manifest_hash: Hash
- import_allowlist_hash: Hash
- kernel_result_hash: Hash
- kernel_verified_at: Timestamp
- coverage_state: pending | converged | unconverged | integrity_blocked
- convergence_record_hash: Optional<Hash>
- completed_at: Optional<Timestamp>
```

The certificate manifest SHALL list, in topological order:

```text
- obligation ID
- theorem name
- exact theorem statement
- statement hash
- proof source hash
- compiled artifact hash
- actual Lean constant dependencies
- environment hash
- kernel result hash
```

### Certificate rules

- A certificate MAY be created only after the root obligation is `proved` by Lean.
- A certificate’s kernel fields are immutable.
- `coverage_state=converged` MAY be written only by the deterministic convergence monitor.
- `completed_at` MAY be written only when all COMPLETE conditions hold.
- A certificate with `coverage_state=unconverged` is a valid root proof artifact but not a completed LLM-Driven Proof Search Environment run.
- Raw Draft text and raw failed attempts are not part of the certificate.

## 2.4 Boundary matrix

| From | To | Allowed | Forbidden |
|---|---|---|---|
| Natural problem | Draft | Full source text, approved metadata | Legacy proof status |
| Natural problem | Root formalization | Full source text, explicit assumptions | Silent fallback to a conclusion or last relation |
| Draft | Sketch | Moves, propositions, constructions, case structure | Treating prose sentences as verified steps |
| Sketch | Prover | Root signature, selected theorem, direct dependency signatures, latest diagnostic, one lesson | Raw Draft, full proof history, raw failed chains |
| Prover | Lean | One exact theorem declaration with approved imports and dependencies | Natural-language proof, multiple unrelated declarations, new axioms |
| Lean | Sketch state | Structured kernel pass or fail | Advisory success, missing result treated as pass |
| Sketch | Certificate | Kernel-verified root and verified dependency manifest | Independent true statements without root composition |
| Reviewer | Sketch | Candidate formal obligations | Closure votes, truth verdicts, completion decisions |

---

# 3. Invariants

## 3.1 Invariant 1: Lean is the sole authority for discharge

**Contract**

An obligation may transition to `proved` only in the same database transaction that inserts a passing `verified_lemma` produced by the Lean service for that exact obligation statement.

```text
status = proved  <=>  proved_lemma_id references a positive-polarity,
                      kernel-passed verified lemma whose statement hash
                      equals the obligation statement hash
```

SymPy and Pint APIs MUST return only:

```text
preflight_reject | falsified | unknown | infrastructure_error
```

They MUST NOT return an acceptance state consumed as proof.

**Structural enforcement**

- The core repository SHALL expose no generic `set_obligation_proved` function.
- Only `commit_kernel_pass(attempt_id, kernel_result)` may write `status=proved`.
- The database transition SHALL be guarded by a transaction and a status constraint.
- The sidecar SHALL not expose `all_passed` as a proof authority field.
- UI clients SHALL not send proof-status mutations.

**Audit closure:** `[Audit T-01]`.

## 3.2 Invariant 2: No fail-open acceptance

**Contract**

Absence of a result is never a successful result.

All call outcomes use this closed enum:

```text
kernel_pass
kernel_fail
preflight_reject
model_invalid_output
infrastructure_error
budget_denied
timeout
cancelled
```

Only `kernel_pass` can produce a proved obligation.

**Structural enforcement**

- Every call wrapper MUST return one explicit outcome.
- Exceptions MUST be converted to `infrastructure_error` and persisted.
- Null, empty, malformed, or unparseable responses MUST become `model_invalid_output`.
- A reviewer failure makes the review epoch ineligible for convergence.
- A Lean service timeout leaves the obligation open.

**Audit closure:** `[Audit T-02]`, `[Audit S-02]`.

## 3.3 Invariant 3: No auto-conclusion

**Contract**

There is no conclusion entity and no conclusion transition. The root theorem is an obligation from the beginning of the problem version.

**Structural enforcement**

- The schema contains no conclusion table or `verified_conclusion` flag.
- Completion checks only the root obligation’s Lean artifact and convergence record.
- The root theorem statement is mandatory before proof search starts.
- A natural-language final answer may be generated only after completion and is presentation-only.

**Audit closure:** `[Audit T-03]`.

## 3.4 Invariant 4: No sampling as proof

**Contract**

Finite evaluation, random testing, numerical sampling, CAS simplification, and counterexample search can reject or falsify a candidate but cannot discharge a universal proposition.

**Structural enforcement**

- Preflight tools do not have write access to obligation status.
- Their result type has no `proved` variant.
- Every universal claim, including inequalities, divisibility, GCD, congruence, and abstract-function claims, requires a Lean kernel artifact.
- A successful sample run is recorded as `unknown`, not as evidence of proof.

**Audit closure:** `[Audit T-04]`.

## 3.5 Invariant 5: Composition is verified, not assumed

**Contract**

The root certificate must contain a Lean proof of the exact root theorem. Every non-leaf obligation must be verified in an environment containing its required dependency lemmas, and the elaborated proof term must reference every required direct dependency.

**Structural enforcement**

- Dependency modules are generated only from previously kernel-verified lemmas.
- Candidate imports are generated by code, not chosen by the model.
- After elaboration, the Lean service extracts theorem-constant dependencies from the target proof term.
- Actual generated-lemma dependencies MUST be a subset of the declared transitive dependency closure.
- Every direct active edge MUST appear in the target proof term’s generated-lemma dependency set.
- The root theorem is checked by the same mechanism.

A collection of independently verified lemmas without a root proof is never a certificate.

**Audit closure:** `[Audit T-05]`.

## 3.6 Invariant 6: Verified fidelity boundary

**Contract**

Proof search cannot begin until the exact natural-language problem version is bound to a mandatory Lean root theorem through an approved fidelity process.

**Structural enforcement**

- `problem_versions.root_formal_statement` is `NOT NULL`.
- `problem_versions.fidelity_status` must be `approved` before entering `PROVING`.
- Independent formalization candidates are Lean-parsed and, when more than one is used, must have a Lean-checked equivalence result or be explicitly resolved by a human.
- A human approval or signed trusted-corpus manifest binds the natural problem hash, root theorem hash, import policy hash, and normalized rendering.
- Changing any bound hash creates a new problem version.

Lean equivalence between candidate formalizations is a consistency check. It does not by itself prove faithfulness to natural language. Human or trusted-manifest approval is the final seam.

**Audit closure:** `[Audit F-01]`.

## 3.7 Invariant 7: Done is deterministic state evaluation

**Contract**

No model returns `done`, `complete`, `satisfied`, or an equivalent authoritative field.

The deterministic completion predicate is:

```text
complete(problem_version) :=
    fidelity_status == approved
    AND root_obligation.status == proved
    AND certificate.kernel_result == pass
    AND every active required proof obligation is proved
    AND every admitted coverage obligation is resolved
    AND convergence_monitor.is_converged == true
    AND no open integrity or fidelity issue exists
```

**Structural enforcement**

- Models cannot call a completion mutation API.
- Reviewer outputs contain candidate obligations only.
- Completion is recomputed from database state after every state-changing event.
- Missing reviews or ineligible reviewer diversity prevent convergence.

**Audit closure:** `[Audit S-01]`, `[Audit S-02]`.

## 3.8 Invariant 8: Context is evacuated

**Contract**

Verified work collapses to theorem citations. Failed work collapses to one structured diagnostic and one distilled lesson.

Normal prover context MUST contain only:

```text
- pinned environment identifier
- exact root theorem signature
- selected obligation theorem signature
- one-line signatures of direct verified dependencies
- latest structured Lean diagnostic
- one distilled failure lesson, maximum 256 tokens
- one optional bounded retrieved hint
```

The context MUST NOT contain:

- Raw Draft text.
- Full verified proof bodies.
- Full prior assistant messages.
- Raw failed proof chains.
- All sibling obligations.
- Full reviewer prose.
- Accumulated research transcripts.

**Structural enforcement**

- One context-builder module owns all prover prompts.
- It accepts typed IDs and fetches only approved fields.
- Mandatory theorem text is never truncated.
- If mandatory content exceeds the context cap, the obligation is marked `needs_decomposition`; the system does not silently replay more history.

**Audit closure:** `[Audit C-03]`, `[Audit §3.3]`.

## 3.9 Invariant 9: Hard cost governor

**Contract**

Every LLM-Driven Proof Search Environment-controlled Lean, tool, action, retrieval, and sandbox operation must acquire a budget reservation before execution. External model inference must obtain a model-call lease through MCP when the runner participates in LLM-Driven Proof Search Environment cost accounting.

**Structural enforcement**

- LLM-Driven Proof Search Environment contains no provider client and cannot directly make an LLM call.
- Internal tool and Lean operations are reachable only through budgeted gateways.
- Before a trusted external runner invokes a model, it requests a lease containing the role, model declaration, maximum input tokens, maximum output tokens, and worst-case cost.
- If the lease would exceed a hard budget, LLM-Driven Proof Search Environment denies it and no compliant runner makes the external call.
- The runner settles the lease with actual usage when it submits the action. If usage is unavailable, the reserved worst-case amount is charged.
- An expired or missing lease may cause the submitted action to be rejected or marked unaccounted according to run policy, but it can never create proof authority.
- LLM-Driven Proof Search Environment cannot prevent an untrusted external process from making out-of-band provider calls or lying about usage. Strict monetary enforcement therefore requires a trusted MCP runner, provider proxy, or attested usage source.
- Budget exhaustion produces an explicit terminal or paused state, never a proof result.

Proof correctness never depends on cost telemetry. Cost accounting and kernel truth remain separate.

**Audit closure:** `[Audit §3.4]`.

## 3.10 Invariant 10: One authoritative graph

**Contract**

The active proof graph is exactly the `obligations` table plus the `obligation_edges` table.

**Structural enforcement**

- Attempts reference an obligation ID.
- Verified lemmas reference an obligation ID.
- Review proposals reference a proposed or admitted obligation ID.
- Certificates reference the root obligation and a graph snapshot hash.
- No other table stores authoritative parent/child relationships.
- JSON dependency lists in model output are proposals only and are normalized into `obligation_edges` before becoming state.

**Audit closure:** `[Audit §2.2]`.

## 3.11 Invariant 11: Models are external MCP actors

**Contract**

The LLM-Driven Proof Search Environment proof core SHALL NOT invoke an LLM. Every model-produced artifact enters through a versioned MCP action submitted by an external agent host.

**Structural enforcement**

- No provider SDK or provider credential is linked into the trusted proof-core runtime.
- The orchestrator emits typed `ActionRequest` records and waits in `awaiting_external_action`.
- The external MCP client chooses the model, performs inference, and submits a typed action with an action-request ID.
- All model roles use the same boundary: Draft, formalization, decomposition, proving, repair, review, and optional hint generation.
- Disconnect, provider failure, or missing external agents leaves proof state unchanged except for explicit lease expiry or truncation events.
- Replay never invokes a model. It replays recorded typed actions.

**Audit closure:** product architecture invariant added by the MCP-only execution revision.

## 3.12 Required invariant tests

The implementation MUST include integration tests that prove the following operations are impossible:

1. Mark an obligation proved with a SymPy success and no Lean artifact.
2. Mark an obligation proved after a Lean timeout.
3. Mark the root complete with no root theorem source.
4. Mark the root complete with proved lemmas but no root composition proof.
5. Mark a universal claim proved from finite samples.
6. Start proof search with `fidelity_status != approved`.
7. Complete after one reviewer submission is missing or ineligible.
8. Build a prover observation containing raw failed proof text.
9. Execute a LLM-Driven Proof Search Environment-controlled Lean or tool call after its hard budget is exhausted.
10. Create a second parent/dependency authority outside `obligation_edges`.
11. Instantiate a provider client, read a provider API key, or initiate model inference inside the LLM-Driven Proof Search Environment process.
12. Advance a proof state merely because an external model host disconnected or failed.
13. Replay an episode by invoking an LLM rather than replaying recorded actions.

---

# 4. The core loop

## 4.1 Problem state machine

```text
CREATED
  -> FORMALIZING
  -> FIDELITY_REVIEW
  -> DRAFTING
  -> SKETCHING
  -> PROVING
  -> ROOT_PROVED_COVERAGE_PENDING
  -> COMPLETE
```

Terminal or paused states:

```text
STALLED_NEEDS_HUMAN
BUDGET_EXHAUSTED
CANCELLED
INTEGRITY_BLOCKED
ROOT_PROVED_COVERAGE_UNCONVERGED
AWAITING_EXTERNAL_ACTION
```

Transitions are deterministic. A model cannot directly request any transition.

## 4.2 Reactive orchestrator pseudocode

LLM-Driven Proof Search Environment does not run a push loop that calls a proposer. It advances deterministically until either an internal transition is complete or an external model action is required.

```text
function advance(problem_version_id):
    problem = load_problem_version(problem_version_id)

    require problem.fidelity_status == APPROVED
    require problem.root_formal_statement is not null
    require environment_hash_matches(problem)

    loop:
        if cancelled(problem):
            transition(CANCELLED)
            return terminal_status()

        if integrity_issue_open(problem):
            transition(INTEGRITY_BLOCKED)
            return terminal_status()

        if internal_budget.hard_limit_reached(problem):
            transition(budget_terminal_state(problem))
            return terminal_status()

        admit_deterministically_valid_submitted_review_proposals(problem)

        if root_kernel_verified(problem):
            ensure_certificate_exists(problem)

            if review_epoch_due(problem):
                request = create_external_action_request(
                    role=COVERAGE_REVIEW,
                    observation=review_context(problem),
                    required_count=review_policy.required_reviewers
                )
                transition(AWAITING_EXTERNAL_ACTION)
                return request

            convergence = convergence_monitor.evaluate(problem)
            persist_convergence_snapshot(convergence)

            if convergence.complete:
                finalize_certificate(problem, convergence)
                transition(COMPLETE)
                return terminal_status()

        if initial_draft_missing(problem):
            return create_external_action_request(
                role=DRAFT,
                observation=draft_context(problem)
            )

        if initial_sketch_missing(problem):
            return create_external_action_request(
                role=SKETCH_FORMALIZATION,
                observation=sketch_context(problem)
            )

        obligation = scheduler.next_ready(problem)

        if obligation is none:
            if unresolved_in_progress_lock_exists(problem):
                recover_stale_lock_deterministically(problem)
                continue

            if review_epoch_due_or_no_frontier(problem):
                return create_external_action_request(
                    role=COVERAGE_REVIEW,
                    observation=review_context(problem)
                )

            if open_obligations_exist_but_none_ready(problem):
                transition(INTEGRITY_BLOCKED)
            elif root_kernel_verified(problem):
                transition(ROOT_PROVED_COVERAGE_UNCONVERGED)
            else:
                transition(STALLED_NEEDS_HUMAN)
            return terminal_status()

        if decomposition_policy.must_decompose(obligation):
            return create_external_action_request(
                role=DECOMPOSITION,
                observation=compact_decomposition_context(obligation)
            )

        context = compact_context_builder.build(obligation)
        if context.mandatory_tokens > policy.max_context_tokens:
            mark_needs_decomposition(obligation, reason=CONTEXT_TOO_LARGE)
            continue

        role = REPAIR if obligation.has_retry_diagnostic else PROVE
        request = create_external_action_request(
            role=role,
            obligation_id=obligation.id,
            observation=context,
            allowed_actions=typed_actions_for(role)
        )
        transition(AWAITING_EXTERNAL_ACTION)
        return request
```

The external agent host performs inference outside LLM-Driven Proof Search Environment:

```text
request = mcp.episode_observe(episode_id)
lease = mcp.model_call_reserve(request.id, declared_model, token_limits)
model_output = external_provider_or_local_model.generate(request.observation)
result = mcp.episode_step(
    episode_id,
    expected_revision,
    idempotency_key,
    action_request_id=request.id,
    model_call_lease_id=lease.id,
    typed_action=parse_external_output(model_output),
    declared_usage=provider_usage
)
```

`episode_step` validates the action, runs preflight and Lean when required, commits or rejects the transition, settles the lease, calculates reward, records the trajectory event, and calls `advance` until the next external action or terminal state.

No branch in this loop invokes an LLM internally.

## 4.3 External action lease and concurrency policy

The core MAY have multiple outstanding external action requests only when concurrency is enabled explicitly.

Default values:

```text
max_concurrent_obligations = 2
max_outstanding_action_requests_per_obligation = 1
portfolio_mode = false
```

Optional portfolio mode MAY issue multiple action requests for the same obligation only when:

- `portfolio_mode=true` in run configuration.
- Each request has a distinct action-request ID and model-call lease.
- The number of requests is capped.
- The first committed kernel pass invalidates remaining outstanding requests for that obligation.
- Late submissions are rejected deterministically as superseded.
- Portfolio mode does not change any acceptance rule.

LLM-Driven Proof Search Environment coordinates leases and commits. The external runner owns provider concurrency and cancellation.

## 4.4 Transaction boundaries

The following operations MUST be atomic:

- Insert verified lemma plus transition obligation to `proved`.
- Insert negative verified lemma plus transition obligation to `refuted`.
- Admit a decomposition plus all child obligations and edges.
- Create a certificate from a proved root.
- Finalize a certificate plus transition problem to `COMPLETE`.
- Reserve budget before a LLM-Driven Proof Search Environment-controlled call or issue a model-call lease before a compliant external inference.
- Commit, release, expire, or settle the reservation or lease after the corresponding operation.

A crash between proof verification and database commit MUST leave the obligation open. The same proof artifact can be reattached later by hash after rechecking its environment and kernel result.

---

# 5. Verification and composition

## 5.1 Trusted theorem environment

Each problem version SHALL bind to a `ToolchainManifest`:

```text
ToolchainManifest
- lean_version
- lake_version
- mathlib_revision
- approved_imports[]
- prohibited_declarations[]
- kernel_flags
- build_flags
- executable_hash
- manifest_hash
```

The manifest MUST be content-addressed and recorded in every verified lemma and certificate.

Default import policy:

- Imports are generated by code.
- The model cannot add imports.
- Only imports on the allowlist are available.
- Generated lemma modules may import only the base environment and direct verified dependency modules.
- A problem version cannot mix artifacts from different environment hashes.

## 5.2 Generated namespace

Every problem version receives a deterministic namespace:

```text
ProofSearch.P_<first_16_chars_of_problem_version_hash>
```

Every obligation receives a deterministic theorem name:

```text
O_<first_16_chars_of_obligation_id_without_hyphens>
```

Models do not choose theorem names.

## 5.3 Candidate source contract

A normal prover candidate MUST contain exactly one target theorem declaration in a generated wrapper. Local `have`, `let`, `suffices`, and tactic blocks are allowed inside the theorem proof.

Top-level candidate declarations are forbidden except for the exact target theorem. Specifically forbidden:

- `axiom`
- `constant`
- `opaque`
- `unsafe`
- `sorry`
- `admit`
- theorem shadowing
- namespace escape
- unapproved `set_option`
- unapproved imports
- foreign file access
- process execution

The wrapper generated by code is conceptually:

```text
import <approved base imports>
import <verified direct dependency modules>

namespace <problem namespace>

theorem <obligation theorem name> : <exact stored statement> := by
  <candidate proof body>

end <problem namespace>
```

The model SHALL normally return only the proof body. If it returns a full theorem, the parser MUST extract the body and reject any additional top-level declaration.

## 5.4 Exact theorem matching

After elaboration, the Lean service MUST:

1. Locate the generated target declaration by exact name.
2. Read its elaborated type.
3. Compare the elaborated type to the stored obligation statement using Lean definitional equality in the same environment.
4. Reject if type matching fails.
5. Reject if the declaration has any untrusted axiom dependency.
6. Reject if the source contains prohibited syntax.
7. Extract the proof term’s constant dependencies.
8. Apply the dependency checks in Section 5.5.
9. Serialize structured diagnostics or a passing kernel result.

String equality alone is insufficient. Exact matching uses the elaborated Lean expression.

## 5.5 Dependency composition

For obligation `P` with direct dependencies `D1...Dn`:

- Each `Di` MUST already have a passing positive verified lemma.
- The Lean wrapper imports the module for each `Di`.
- No unproved obligation is exposed as a hypothesis or axiom.
- The proof term for `P` MUST reference every direct dependency theorem constant.
- The proof term MAY reference approved mathlib declarations.
- The proof term MUST NOT reference generated lemmas outside the declared transitive dependency closure.

The Lean service returns:

```text
DependencyUseReport
- declared_direct_dependency_ids[]
- actual_generated_dependency_ids[]
- missing_required_dependency_ids[]
- undeclared_generated_dependency_ids[]
```

A kernel-valid theorem with a non-empty `missing_required_dependency_ids` or `undeclared_generated_dependency_ids` list is rejected as a Sketch mismatch. It can be reproposed with corrected edges or a new active composition obligation.

This requirement makes graph composition observable and prevents the system from treating independently true lemmas as a composed proof. `[Audit T-05]`.

## 5.6 Leaf discharge

A leaf obligation has no generated dependency imports. It may use only the approved base theorem environment.

A deterministic tactic portfolio MAY run before LLM-Driven Proof Search Environment emits an external prove action request:

```text
rfl
simp
norm_num
ring
linarith
nlinarith
omega
aesop with a strict time cap
```

The exact tactic allowlist is configuration. A tactic success is still a Lean kernel success, so it may discharge an obligation.

## 5.7 Structured Lean result

```text
LeanVerificationResult
- outcome: kernel_pass | kernel_fail | timeout | infrastructure_error
- attempt_id
- obligation_id
- theorem_name
- expected_statement_hash
- elaborated_statement_hash: Optional<Hash>
- environment_hash
- proof_source_hash
- compiled_artifact_hash: Optional<Hash>
- proof_term_hash: Optional<Hash>
- diagnostic: Optional<LeanDiagnostic>
- dependency_use_report: Optional<DependencyUseReport>
- wall_time_ms
- lean_cpu_time_ms
```

## 5.8 Structured diagnostic

```text
LeanDiagnostic
- category: parse_error | elaboration_error | type_mismatch |
            unsolved_goals | tactic_failure | timeout |
            prohibited_construct | dependency_mismatch | internal_error
- primary_message
- source_span
- goal
- local_context[]
- unsolved_goals[]
- used_dependencies[]
- error_code
- canonical_goal_hash
```

The diagnostic MUST be stored as structured data, not only as one concatenated string.

## 5.9 Positive and negative discharge

An obligation can resolve in two formal ways:

```text
proved  := Lean proves the exact obligation statement
refuted := Lean proves the exact negation of the obligation statement
```

A reviewer cannot mark an obligation refuted. A failed proof attempt is not a refutation.

For a counterexample obligation, the formal statement SHOULD be constructed so that a positive proof expresses the counterexample directly, avoiding reliance on a separate refutation state when possible.

## 5.10 Root verification

The root obligation uses the same exact verification path as every other obligation.

The root is not special-cased into acceptance. It is special only because:

- Its statement hash equals the approved root theorem hash.
- Its passing verified lemma creates a kernel-valid certificate.
- Its status participates in the completion predicate.

## 5.11 CAS and numeric preflight

Optional SymPy/Pint preflight MAY:

- Reject malformed symbolic syntax.
- Detect simple contradictions.
- Find a numeric counterexample.
- Check dimensional consistency.
- Normalize expressions under an allowlist.

It MUST NOT:

- Mark a theorem proved.
- Create a verified lemma.
- Close an obligation.
- Generate a certificate.
- Convert “no counterexample found” into evidence of truth.

The existing SymPy parser allowlist and targeted-operation strategy SHOULD be reused, including the protection against unbounded `simplify()` behavior noted in `[Audit §7]`.

---

# 6. Fidelity

## 6.1 Fidelity objective

The formal theorem proved by Lean must correspond to the intended natural-language problem. Kernel verification cannot establish this correspondence by itself. The system therefore has an explicit, blocking fidelity process before proof search.

## 6.2 Problem version data

```text
ProblemVersion
- id
- source_problem_text
- source_problem_hash
- source_metadata_json
- root_formal_statement
- root_statement_hash
- normalized_root_rendering
- environment_hash
- fidelity_status: pending | candidates_ready | equivalent |
                   disputed | approved | revoked
- fidelity_method: human_authored | dual_formalization_human |
                   trusted_manifest
- fidelity_approval_id
- root_obligation_id
- state
- created_at
```

`root_formal_statement` is mandatory. A placeholder or optional null is forbidden.

## 6.3 Formalization candidate submission

Default policy requires two independent formalization candidates before human approval.

LLM-Driven Proof Search Environment does not generate candidates internally. It emits independent formalization action requests through MCP. External agents submit candidate statements under distinct action-request IDs.

Independence means:

- Different externally declared model configurations, or
- Different provider or model families with trusted runner attestation, or
- A human-authored theorem plus one externally generated candidate.

The second formalizer MUST NOT receive the first candidate through the LLM-Driven Proof Search Environment observation. The external runner is responsible for honoring the independence policy and declaring the model identity used. Unattested identity may be accepted as a proposal but cannot satisfy a strict diversity policy.

Each candidate contains:

```text
FormalizationCandidate
- id
- problem_version_id
- lean_statement
- statement_hash
- normalized_rendering
- explicit_quantifiers[]
- explicit_hypotheses[]
- domain_restrictions[]
- external_agent_config_hash or human_actor_id
- declared_model_config_hash: Optional<Hash>
- action_request_id
- created_at
```

## 6.4 Lean equivalence check

When two candidate statements elaborate to propositions in the same environment, the system creates an equivalence obligation:

```text
CandidateA <-> CandidateB
```

For parameterized theorems, the equivalence proposition includes the complete binders and hypotheses required to compare the propositions in the same scope.

Possible results:

```text
equivalent      := Lean kernel proves the biconditional
not_equivalent  := Lean kernel proves negation or a concrete separating case
unknown         := no proof either way within budget
invalid         := one candidate does not elaborate
```

Only `equivalent` advances automatically to the human audit screen. `unknown`, `not_equivalent`, or `invalid` requires human resolution.

The equivalence proof is stored as a normal verified artifact, but it does not replace human fidelity approval.

## 6.5 Human audit point

The fidelity audit interface MUST display side by side:

- Immutable natural-language problem text.
- Candidate formal statements.
- Normalized English rendering of each candidate.
- Explicit quantifiers.
- Hypotheses and domain restrictions.
- Candidate differences.
- Lean equivalence status.
- Imported theorem environment.

The approver explicitly confirms:

```text
“I approve this exact Lean proposition as the formal target for this exact
natural-language problem under the listed assumptions and imports.”
```

Approval binds:

```text
source_problem_hash
root_statement_hash
environment_hash
normalized_rendering_hash
approver identity or trusted manifest signature
timestamp
```

Proof search MUST remain blocked until this approval exists.

## 6.6 Trusted corpus mode

A benchmark or curated corpus MAY replace per-run human approval with a signed manifest when:

- The manifest binds source text, root statement, environment, and rendering hashes.
- The manifest is produced outside the proof run.
- Manifest verification passes.
- The source is marked `trusted_manifest`.

Trusted corpus ingestion SHOULD still undergo a deterministic audit sample of at least 5 percent plus every equivalence-disputed item. A failed sample revokes the corpus manifest version and blocks new runs from it.

## 6.7 Fidelity challenges during review

A reviewer may propose a formal coverage or counterexample obligation that suggests the root formalization is too weak, too strong, or missing a case.

Such a proposal cannot mutate the root theorem. It creates a `fidelity_issue` event and blocks `COMPLETE` until one of these occurs:

1. Lean resolves the challenge and the human auditor confirms no root change is required.
2. The root formalization is revised, creating a new problem version.
3. A human rejects the challenge as out of scope with a recorded reason.

A root theorem change invalidates all prior obligations and certificates for the new problem version. Old artifacts remain immutable and auditable.

---

# 7. Scheduling, decomposition, and retry

## 7.1 Ready-obligation definition

An obligation is ready when:

```text
status == open
AND every direct dependency status == proved
AND no active lock exists
AND fidelity_status == approved
AND no integrity block exists
AND obligation budget remains
```

Refuted, superseded, abandoned, or blocked obligations are not ready.

## 7.2 Deterministic scheduling score

The scheduler selects the highest-scoring ready obligation. All terms are normalized to `[0,1]`.

```text
score(o) =
    (0.30 * C(o)
   + 0.20 * D(o)
   + 0.30 * I(o)
   + 0.20 * (1 - H(o)))
    / (1 + K(o))
```

Where:

### Graph centrality `C(o)`

```text
paths_to_root(o) = number of distinct active dependency paths from o to root
C(o) = log(1 + paths_to_root(o)) / log(1 + max_paths_to_root)
```

Path counts are computed by deterministic dynamic programming and capped before overflow. This rewards obligations shared by multiple rootward proof paths.

### Dependency depth `D(o)`

```text
D(o) = 1 - min_distance_to_root(o) / max_active_depth
```

Obligations closer to the root receive a higher score, all else equal.

### Expected closure impact `I(o)`

```text
immediate = number of open obligations that become ready if o is proved
open_desc = number of active open descendants of o
I(o) = min(1,
           (immediate + 0.25 * open_desc)
           / max(1, total_open_obligations))
```

### Estimated difficulty `H(o)`

Difficulty is deterministic and uses no LLM confidence field.

```text
H(o) = clamp01(
    0.25 * min(1, lean_ast_nodes / 200)
  + 0.20 * min(1, binder_depth / 8)
  + 0.15 * min(1, logical_branch_count / 8)
  + 0.15 * min(1, typeclass_or_synthesis_failures / 4)
  + 0.25 * min(1, semantic_failure_count / max_attempts)
)
```

### Retry cost `K(o)`

```text
expected_next_cost = median actual cost of recent same-role attempts,
                     else worst-case reservation estimate
K(o) = min(1, expected_next_cost / remaining_obligation_budget)
```

### Tie-breaking

Ties are resolved in this order:

1. Lower attempt count.
2. Older `created_at`.
3. Lexicographically smaller obligation UUID.

The complete score breakdown MUST be emitted in a scheduler event for inspection. This replaces the current `priority * confidence * decay` heuristic. `[Audit §4.1]`.

## 7.3 Decomposition objective

Decompose until each active leaf is plausibly dischargeable as a standalone Lean theorem under the per-obligation budget.

The policy must avoid:

- Under-decomposition, where a leaf repeatedly produces broad unsolved proof states.
- Over-decomposition, where trivial obligations explode graph and model cost.

## 7.4 Initial decomposition

The Sketch compiler receives the Draft and proposes:

- The root obligation.
- Zero or more supporting obligations.
- Required dependency edges.
- Natural descriptions.
- A reason for each decomposition boundary.

The compiler cannot prove or close any obligation.

## 7.5 Leaf probe

Every new leaf receives a bounded discharge probe before further decomposition:

```text
1. Run deterministic tactic portfolio with max 5 seconds.
2. If not proved, run at most one prover attempt under normal context limits.
3. Classify the structured Lean diagnostic.
```

The leaf remains a standalone target when:

- The deterministic tactic portfolio proves it, or
- The prover proves it, or
- The failed probe has one or two focused goals and no repeated semantic failure.

The leaf becomes eligible for decomposition when any condition holds:

- More than two independent unsolved goals remain.
- The same canonical goal hash survives two semantic attempts.
- Two semantic failures indicate a missing intermediate theorem.
- The mandatory context exceeds the hard context cap.
- The proof attempt repeatedly times out after one repair attempt.
- The theorem exceeds the configured structural-complexity threshold and has an evident top-level case, induction, witness, or reduction structure.

Syntax and elaboration errors trigger compiler-feedback repair before decomposition. They do not by themselves justify changing the mathematics.

## 7.6 Decomposition limits

Default hard limits:

```text
max_decomposition_depth = 6
min_children_per_decomposition = 2
max_children_per_decomposition = 6
max_active_obligations_per_problem = 500
```

A valid decomposition must satisfy all of the following:

1. Every child statement elaborates.
2. No child statement hash equals the parent or a sibling.
3. The new graph is acyclic.
4. Child count is within limits.
5. At least one child reduces a structural complexity metric by 20 percent, or each child isolates a distinct case, witness, or named lemma.
6. The parent remains active as a composition obligation.
7. The parent proof will be required to reference every child theorem.
8. No child is admitted as proved from the decomposition model’s assertion.

If no valid decomposition is produced within the decomposition budget, the obligation becomes `blocked_needs_human`.

There is one decomposition operation. There is no separate “re-decomposer” subsystem.

## 7.7 External MCP role contracts

LLM-Driven Proof Search Environment defines roles as typed action contracts, not as internal model clients.

### Draft role

Requested for:

- Initial informal Draft on hard problems.
- Replanning after a mathematically substantive stall.
- Decomposition planning for hard obligations after repeated semantic failure.

The observation includes only the approved Draft inputs. The external agent host chooses a model with the required informal-mathematics capability.

### Sketch formalization role

Requested for:

- Converting Draft propositions into Lean theorem statements.
- Creating an initial obligation DAG proposal.
- Formalizing reviewer-proposed obligations.

The external output is always a proposal and is parsed, audited, and admitted deterministically.

### Prove role

Requested for:

- Producing a proof body for one exact obligation.

### Repair role

Requested for:

- Repairing a failed proof using the exact theorem signature and structured Lean diagnostics.

### Review roles

Requested only to propose new coverage, counterexample, or fidelity obligations. Reviewer submissions never establish truth or completion.

### External role binding

```text
ExternalRoleBinding
- role: DRAFT | SKETCH_FORMALIZATION | PROVE | REPAIR |
        DECOMPOSITION | COVERAGE_REVIEW | FIDELITY_REVIEW
- required_capabilities: CapabilityTag[]
- maximum_input_tokens
- maximum_output_tokens
- allowed_action_kinds: ActionKind[]
- diversity_lens: Optional<String>
- model_identity_requirement: none | declared | attested
- prompt_template_hash
```

The LLM-Driven Proof Search Environment repository stores role requirements and action schemas. The external MCP host stores provider routing, API credentials, sampling settings, reasoning settings, retries, and model-specific transport code.

Model names are external-runner configuration, not proof-core logic.

## 7.8 Compiler-feedback retry

The next attempt is seeded from the obligation signature plus the latest Lean diagnostic, not from the failed prose or proof chain.

### Persisted retry state

```text
AttemptDiagnostic
- attempt_id
- obligation_id
- theorem_signature
- goal
- local_context[]
- unsolved_goals[]
- error_span
- error_category
- error_code
- used_dependencies[]
- canonical_goal_hash
- created_at
```

### Distilled lesson

Each obligation stores at most one failure lesson:

```text
maximum length = 256 tokens
```

The lesson is produced in this order:

1. Deterministic diagnostic template, preferred.
2. Optional cheap-model distillation when the diagnostic is too domain-specific.

The lesson is advisory and cannot change proof status.

Examples:

```text
- “The current proof leaves the induction step goal unchanged; introduce a
  stronger induction hypothesis or decompose the step lemma.”
- “The candidate used lemma X, but X is not a declared dependency.”
- “The theorem statement elaborates, but the proof has two independent case
  goals. Decomposition is now required.”
```

### Retry prompt contents

```text
- exact root signature
- exact obligation signature
- direct verified dependency signatures
- latest structured diagnostic
- one distilled lesson
- optional bounded hint
```

Raw failed source remains in the artifact store for audit but is not injected automatically.

### Retry policy

Default limits:

```text
max_attempts_per_obligation = 6
max_syntax_or_elaboration_repairs = 2
max_semantic_attempts_before_decomposition = 2
max_repeated_canonical_goal_count = 2
```

Decision table:

| Failure category | Next action |
|---|---|
| Parse or syntax error | Compiler-feedback repair, maximum 2 |
| Type mismatch with target theorem | Reject candidate, repair exact signature |
| Prohibited construct | Reject candidate, fresh repair prompt |
| Missing or undeclared dependency | Correct edge or proof use, no closure |
| One focused unsolved goal | Fresh prover attempt |
| Multiple independent goals | Decompose |
| Same canonical goal twice | Decompose |
| Timeout once | One bounded repair |
| Timeout twice | Decompose or block |
| Infrastructure error | Retry transport under global call policy, no mathematical penalty |
| Budget denied | Halt or pause run |

This is the APOLLO-style compiler-feedback path required by the prompt and closes the raw-chain replay problem in `[Audit C-01]` and `[Audit C-03]`.

---

# 8. Convergence and coverage

## 8.1 Reviewer purpose

Reviewers inspect the formal Sketch and propose new formal obligations for uncovered regions. They do not determine truth, obligation closure, or run completion.

Examples of valid reviewer output:

- “The zero case is not represented.”
- “The current root statement omits the positivity assumption used in the Draft.”
- “A symmetry reduction requires a separate lemma.”
- “This claimed case split is not exhaustive.”
- “Prove or refute this candidate counterexample proposition.”

Each output must include a proposed Lean statement.

## 8.2 Review epoch triggers

A review epoch is due:

1. After the initial Sketch is admitted.
2. After every five newly proved obligations.
3. After any decomposition that adds three or more obligations.
4. Immediately after the root theorem is proved.
5. Repeatedly after root proof until convergence or budget exhaustion.

The trigger counters are deterministic and configurable.

## 8.3 Diversity requirement

An eligible review epoch requires at least three reviewer submissions received through distinct MCP action requests with:

- At least two distinct model families or providers, declared by the external runner and attested when strict completion assurance is required.
- Three distinct fixed lenses.
- No duplicate `(provider, model, prompt_template_hash, lens)` tuple.

Required lenses:

```text
1. proof_coverage
   Search for missing cases, missing intermediate propositions, and invalid
   composition structure.

2. adversarial_counterexample
   Search for boundary cases, hidden domain assumptions, and candidate
   counterexamples.

3. formalization_fidelity
   Compare the natural problem, approved rendering, and root theorem for
   omissions or strengthening/weakening.
```

At least one reviewer SHOULD be a frontier reasoning model. At least one SHOULD be a Lean-capable model. The third MAY be a cheaper model with a distinct prompt and family.

If diversity requirements are not met or required identity attestation is absent, the epoch is `ineligible`. An ineligible epoch cannot advance convergence. A human reviewer may satisfy a missing lens with a recorded formal proposal set.

## 8.4 Reviewer input

Reviewers receive a compact graph view:

```text
- natural problem and approved normalized root rendering
- root Lean statement
- active obligation theorem signatures
- status of each obligation
- dependency edges
- verified lemma citations
- unresolved coverage obligations
- previous epoch proposal hashes, not full prose
```

Reviewers do not receive raw failed proof chains or satisfaction votes.

## 8.5 Reviewer output schema

```text
ReviewerProposal
- epoch_id
- reviewer_config_hash
- lens
- natural_description
- proposed_lean_statement
- proposed_dependencies[]
- proposal_kind: proof | coverage | counterexample | fidelity_challenge
- rationale
```

No `is_true`, `satisfied`, `done`, `verified`, or `confidence_to_close` field exists.

A confidence field MAY be logged for analytics but MUST NOT affect admission, proof, or convergence.

## 8.6 Deterministic admission

For each proposal, code performs:

1. Lean parse and elaboration.
2. Import and namespace policy validation.
3. Exact hash deduplication.
4. Normalized theorem-type deduplication.
5. Optional Lean biconditional equivalence check against near-duplicate active obligations.
6. Dependency existence and acyclicity checks.
7. Contamination checks against protected regression answers and typed theorem facts.
8. Child-count and depth policy checks.

Admission outcomes:

```text
admitted
duplicate
superseded_by_existing
invalid_statement
invalid_dependency
policy_rejected
needs_human_fidelity_review
```

Only admitted proposals become obligations.

## 8.7 Surviving obligation rate

Raw reviewer proposal count is noisy. Convergence uses surviving admitted obligations.

For epoch `e`:

```text
R_e = number of valid diverse reviewer results
A_e = number of newly admitted reviewer obligations
S_e = number of obligations from A_e that, by the end of the next eligible
      epoch, are not duplicate, not policy-rejected, and not immediately
      superseded as redundant
r_e = S_e / R_e
```

An obligation counts as surviving whether it remains open, is proved, or is Lean-refuted. This means a reviewer who discovers a real issue still contributes to the measured discovery rate even if the issue is resolved quickly.

## 8.8 Noise-resistant convergence metric

The monitor keeps an exponential moving average:

```text
EMA_e = 0.5 * r_e + 0.5 * EMA_(e-1)
```

The run is coverage-converged only when all conditions hold:

```text
1. The root obligation is kernel-proved.
2. Every active required proof obligation is proved.
3. Every admitted coverage or counterexample obligation is resolved by Lean,
   superseded by a formally equivalent obligation, or explicitly rejected by
   a human fidelity auditor as out of scope.
4. The last two eligible epochs each have S_e = 0.
5. The three-epoch EMA is below 0.15.
6. The last three epochs each satisfy the diversity requirement.
7. No fidelity challenge or integrity issue is open.
```

The first zero-survivor epoch does not establish convergence. Two consecutive zero-survivor epochs plus the EMA threshold distinguish sustained decay from a single quiet or noisy epoch.

## 8.9 Reviewer disagreement

Reviewer disagreement is not resolved by majority vote.

- Distinct formal proposals are independently admitted or rejected by code.
- Equivalent proposals are deduplicated.
- Conflicting propositions become separate formal obligations or a formal counterexample pair.
- Lean resolves mathematical conflict.
- Human review resolves scope or natural-language fidelity conflict.

## 8.10 Convergence terminal states

```text
COMPLETE
- root kernel proof exists
- deterministic convergence satisfied

ROOT_PROVED_COVERAGE_UNCONVERGED
- root kernel proof exists
- convergence not satisfied before budget or epoch limit

STALLED_NEEDS_HUMAN
- no ready obligation
- no valid new reviewer obligation
- root not proved or an unresolved human decision blocks progress
```

There is no reviewer-controlled done label. `[Audit §4.3]`.

---

# 9. Data model and schema

## 9.1 Storage principles

- SQLite is the core transactional store.
- Large text and binary artifacts are content-addressed files outside normal rows.
- Every artifact reference includes a hash.
- Events are append-only.
- No legacy proof fact is trusted during migration.
- The database schema encodes proof-state invariants where possible.

## 9.2 Core tables

### `problem_versions`

```text
id TEXT PRIMARY KEY
source_problem_text TEXT NOT NULL
source_problem_hash TEXT NOT NULL
source_metadata_json TEXT NOT NULL
root_formal_statement TEXT NOT NULL
root_statement_hash TEXT NOT NULL
normalized_root_rendering TEXT NOT NULL
environment_hash TEXT NOT NULL
fidelity_status TEXT NOT NULL
fidelity_method TEXT NOT NULL
fidelity_approval_id TEXT
root_obligation_id TEXT
state TEXT NOT NULL
created_at TEXT NOT NULL
```

Constraints:

- `root_formal_statement` is never null.
- `state IN ('PROVING', ...)` requires `fidelity_status='approved'`.
- Root statement and environment are immutable.

### `formalization_candidates`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
lean_statement TEXT NOT NULL
statement_hash TEXT NOT NULL
normalized_rendering TEXT NOT NULL
quantifiers_json TEXT NOT NULL
hypotheses_json TEXT NOT NULL
domain_restrictions_json TEXT NOT NULL
origin_type TEXT NOT NULL
origin_config_hash TEXT NOT NULL
created_at TEXT NOT NULL
UNIQUE(problem_version_id, statement_hash)
```

### `fidelity_approvals`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
source_problem_hash TEXT NOT NULL
root_statement_hash TEXT NOT NULL
environment_hash TEXT NOT NULL
rendering_hash TEXT NOT NULL
approval_method TEXT NOT NULL
approver_id TEXT NOT NULL
signature TEXT
notes TEXT
created_at TEXT NOT NULL
```

### `drafts`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
model_config_hash TEXT NOT NULL
prompt_template_hash TEXT NOT NULL
content_artifact_hash TEXT NOT NULL
extracted_moves_json TEXT NOT NULL
created_at TEXT NOT NULL
```

### `obligations`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
kind TEXT NOT NULL
theorem_name TEXT NOT NULL
lean_statement TEXT NOT NULL
statement_hash TEXT NOT NULL
natural_description TEXT NOT NULL
status TEXT NOT NULL
depth_from_root INTEGER NOT NULL
created_by TEXT NOT NULL
created_by_epoch_id TEXT
superseded_by_id TEXT REFERENCES obligations(id)
proved_lemma_id TEXT
refutation_lemma_id TEXT
failure_lesson TEXT
attempt_count INTEGER NOT NULL DEFAULT 0
created_at TEXT NOT NULL
closed_at TEXT
UNIQUE(problem_version_id, theorem_name)
```

Required partial index:

```text
UNIQUE(problem_version_id, statement_hash)
WHERE status IN ('open', 'in_progress', 'proved', 'refuted',
                 'blocked_needs_human')
```

Application-level invariant:

```text
status == proved  iff proved_lemma_id is a valid positive kernel artifact
status == refuted iff refutation_lemma_id is a valid negative kernel artifact
```

No `verified BOOLEAN` column exists.

### `obligation_edges`

```text
parent_obligation_id TEXT NOT NULL REFERENCES obligations(id)
dependency_obligation_id TEXT NOT NULL REFERENCES obligations(id)
edge_kind TEXT NOT NULL
case_group TEXT
created_at TEXT NOT NULL
PRIMARY KEY(parent_obligation_id, dependency_obligation_id)
CHECK(parent_obligation_id <> dependency_obligation_id)
```

This is the only authoritative proof graph.

### `proposal_attempts`

```text
id TEXT PRIMARY KEY
obligation_id TEXT NOT NULL REFERENCES obligations(id)
role TEXT NOT NULL
model_config_hash TEXT
prompt_hash TEXT NOT NULL
context_manifest_hash TEXT NOT NULL
candidate_source_artifact_hash TEXT
diagnostic_json TEXT
outcome TEXT NOT NULL
input_tokens INTEGER NOT NULL
output_tokens INTEGER NOT NULL
cost_usd_micros INTEGER NOT NULL
wall_time_ms INTEGER NOT NULL
lean_cpu_time_ms INTEGER NOT NULL
created_at TEXT NOT NULL
```

Raw prompts MAY be stored as encrypted or optional audit artifacts, but normal retry context uses only typed fields.

### `verified_lemmas`

```text
id TEXT PRIMARY KEY
obligation_id TEXT NOT NULL REFERENCES obligations(id)
polarity TEXT NOT NULL  // positive or negative
theorem_name TEXT NOT NULL
statement_hash TEXT NOT NULL
proof_source_artifact_hash TEXT NOT NULL
compiled_artifact_hash TEXT NOT NULL
proof_term_hash TEXT NOT NULL
environment_hash TEXT NOT NULL
actual_dependency_ids_json TEXT NOT NULL
kernel_result_hash TEXT NOT NULL
verified_at TEXT NOT NULL
UNIQUE(obligation_id, polarity)
```

A positive lemma proves the obligation statement. A negative lemma proves its exact negation.

### `review_epochs`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
epoch_number INTEGER NOT NULL
trigger TEXT NOT NULL
eligible BOOLEAN NOT NULL
reviewer_count INTEGER NOT NULL
diverse_family_count INTEGER NOT NULL
lens_count INTEGER NOT NULL
admitted_count INTEGER NOT NULL
surviving_count INTEGER
surviving_rate REAL
ema_rate REAL
created_at TEXT NOT NULL
completed_at TEXT
UNIQUE(problem_version_id, epoch_number)
```

### `review_proposals`

```text
id TEXT PRIMARY KEY
epoch_id TEXT NOT NULL REFERENCES review_epochs(id)
reviewer_config_hash TEXT NOT NULL
lens TEXT NOT NULL
natural_description TEXT NOT NULL
proposed_lean_statement TEXT NOT NULL
proposed_statement_hash TEXT NOT NULL
proposed_dependencies_json TEXT NOT NULL
proposal_kind TEXT NOT NULL
admission_outcome TEXT
admitted_obligation_id TEXT REFERENCES obligations(id)
created_at TEXT NOT NULL
```

The JSON dependency list is not authoritative. It is normalized into `obligation_edges` if admitted.

### `certificates`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
root_obligation_id TEXT NOT NULL REFERENCES obligations(id)
root_verified_lemma_id TEXT NOT NULL REFERENCES verified_lemmas(id)
root_statement_hash TEXT NOT NULL
root_proof_artifact_hash TEXT NOT NULL
proof_dependency_manifest_hash TEXT NOT NULL
active_sketch_snapshot_hash TEXT NOT NULL
toolchain_manifest_hash TEXT NOT NULL
kernel_result_hash TEXT NOT NULL
coverage_state TEXT NOT NULL
convergence_record_hash TEXT
kernel_verified_at TEXT NOT NULL
completed_at TEXT
```

### `budget_ledger`

```text
id TEXT PRIMARY KEY
problem_version_id TEXT NOT NULL REFERENCES problem_versions(id)
obligation_id TEXT REFERENCES obligations(id)
call_kind TEXT NOT NULL
reservation_id TEXT NOT NULL
state TEXT NOT NULL  // reserved, committed, released
reserved_input_tokens INTEGER NOT NULL
reserved_output_tokens INTEGER NOT NULL
actual_input_tokens INTEGER
actual_output_tokens INTEGER
reserved_cost_usd_micros INTEGER NOT NULL
actual_cost_usd_micros INTEGER
reserved_wall_time_ms INTEGER NOT NULL
actual_wall_time_ms INTEGER
created_at TEXT NOT NULL
updated_at TEXT NOT NULL
```

### `events`

```text
id INTEGER PRIMARY KEY AUTOINCREMENT
problem_version_id TEXT NOT NULL
obligation_id TEXT
event_type TEXT NOT NULL
actor_type TEXT NOT NULL
actor_id TEXT NOT NULL
payload_json TEXT NOT NULL
payload_hash TEXT NOT NULL
created_at TEXT NOT NULL
```

Events are append-only. No update or delete API is exposed.

## 9.3 Obligation transition table

| From | To | Required authority |
|---|---|---|
| open | in_progress | Scheduler lock transaction |
| in_progress | open | Attempt failure, timeout, or lock recovery |
| open/in_progress | proved | Positive Lean kernel artifact transaction |
| open/in_progress | refuted | Negative Lean kernel artifact transaction |
| open/in_progress | superseded | New admitted obligation plus recorded reason |
| open/in_progress | abandoned | Deterministic budget/depth policy plus event |
| open/in_progress | blocked_needs_human | Deterministic stall policy plus event |
| proved/refuted | any other proof status | Forbidden; create a new problem version or superseding obligation |

## 9.4 Active graph snapshot

A certificate’s `active_sketch_snapshot_hash` is computed from a canonical serialization of:

```text
- problem version ID
- root obligation ID
- active obligations: ID, kind, theorem name, statement hash, status
- active edges: parent ID, dependency ID, edge kind, case group
- verified lemma hashes
```

Sorting is deterministic by obligation ID and edge key.

## 9.5 Legacy migration

Existing LLM-Driven Proof Search Environment records MAY be imported only as read-only legacy artifacts.

Rules:

- Existing `verified=true` values are not proof facts.
- Existing steps and proof nodes do not become obligations automatically.
- Existing formal statements may become unapproved formalization candidates.
- Existing Lean-passing artifacts may be reverified in the new pinned environment and then attached through the normal exact-statement path.
- Existing reviewer/satisfaction records may be preserved as event history but have no authority.

---

# 10. Cost model

## 10.1 Budget policy

```text
BudgetPolicy
- max_total_cost_usd
- max_total_input_tokens
- max_total_output_tokens
- max_total_wall_time_seconds
- max_total_lean_cpu_seconds
- max_total_model_calls
- max_total_tool_calls
- max_review_epochs
- max_active_obligations
- per_obligation_input_tokens
- per_obligation_output_tokens
- per_obligation_attempts
- per_review_epoch_cost_usd
- per_call_timeout_seconds
```

Default proof-run limits:

```text
max_total_cost_usd = operator supplied, required
max_total_model_calls = 200
max_total_tool_calls = 400
max_review_epochs = 12
per_obligation_input_tokens = 36,000 cumulative
per_obligation_output_tokens = 18,000 cumulative
per_obligation_attempts = 6
max_context_tokens = 6,000
max_attempt_output_tokens = 3,000
per_call_timeout_seconds = 180
```

The operator may choose different values before a run. Limits are immutable during a run except through an explicit signed budget-amendment event.

## 10.2 Reservation and external model-call lease protocol

LLM-Driven Proof Search Environment uses two related mechanisms.

### Internal operation reservation

Every Lean, retrieval, CAS, sandbox, or other LLM-Driven Proof Search Environment-controlled operation follows:

```text
estimate worst_case_cost
reservation = budget_manager.reserve(scope, worst_case_cost)
if reservation denied:
    do not execute
result = internal_operation()
budget_manager.commit_or_release(reservation, actual_usage)
```

### External model-call lease

A trusted external MCP runner follows:

```text
request = observe_next_action()
lease = model_call_reserve(
    action_request_id,
    declared_model_identity,
    maximum_input_tokens,
    maximum_output_tokens,
    worst_case_cost
)
if lease denied:
    do not invoke the model
model_result, usage = external_model_call()
episode_step(action_request_id, lease_id, typed_action, usage)
```

The budget manager SHALL check all applicable scopes:

- Run total.
- Obligation total.
- Review epoch total.
- Call-kind total.
- Episode and dataset-run total where applicable.

There is no provider client, provider credential, or model transport inside LLM-Driven Proof Search Environment.

A lease is accounting authority, not proof authority. An untrusted external runner can spend money outside LLM-Driven Proof Search Environment or misreport usage; strict monetary guarantees require a trusted runner, provider proxy, or attested billing record.

## 10.3 Token context budget

Normal prover context has a hard 6,000-token cap with this allocation:

| Segment | Maximum tokens |
|---|---:|
| System and proof policy | 500 |
| Root theorem signature | 700 |
| Selected obligation signature | 700 |
| Direct verified dependency citations | 2,000 |
| Latest structured Lean diagnostic | 1,200 |
| Distilled failure lesson | 256 |
| Optional retrieved hint | 500 |
| Formatting reserve | 144 |

Mandatory theorem text is not truncated. If root, obligation, and direct dependency signatures cannot fit, the obligation requires decomposition or dependency compression through a new composition lemma.

## 10.4 Context evacuation rules

### Verified obligation representation

```text
<theorem_name> : <exact theorem statement>
```

No proof body is replayed by default.

### Failed attempt representation

```text
Diagnostic category
Current goal
Local context
Unsolved goals
Error span and code
Used dependencies
One distilled lesson
```

No raw failed chain is replayed by default.

### Retrieval exception

A model MAY request a verified proof body by theorem ID through a budgeted retrieval adapter. The retrieved body:

- Is capped at 1,500 tokens.
- Is logged as tool provenance.
- Replaces the optional hint segment.
- Is never automatically appended to future attempts.

## 10.5 External role capability allocation

| Role | Required external capability | Recommended tier | Why |
|---|---|---|---|
| Draft | Strong informal mathematical reasoning | Frontier | Hard reasoning is capability-gated |
| Hard decomposition | Strong informal reasoning plus formal awareness | Frontier | Determines useful subgoal structure |
| Root formalization | Lean autoformalization | Frontier or specialized formalizer | Fidelity-critical, human-approved |
| Sketch formalization | Lean statement generation | Specialized or mid-tier | Output is parsed and audited |
| Standalone proof | Lean proof generation | Specialized prover | Repeated low-context actions |
| Compiler repair | Lean proof repair | Prover or cheaper repair model | Structured diagnostic narrows task |
| Review coverage | Diverse reasoning lenses | Mixed external pool | Diversity matters, no truth authority |
| Failure lesson | Diagnostic summarization | Deterministic first, optional external cheap model | No need for frontier model |
| Pattern mining | None in runtime | Offline | Removed from proof transaction |

These are requirements communicated to the external MCP runner. LLM-Driven Proof Search Environment does not resolve provider names or invoke any of these models.

## 10.6 External call-cost attribution

Every externally submitted model action SHOULD record:

- External runner identity and configuration hash.
- Declared provider and model configuration hash.
- Action-request ID and model-call lease ID.
- Input and output tokens.
- Monetary cost.
- Wall time.
- Provider request identifier when safely available.
- Attestation level: unverified declaration, trusted runner, provider proxy, or billing-attested.
- Lean CPU time and LLM-Driven Proof Search Environment-controlled tool costs.
- Outcome.

The scheduler may consume trusted or policy-approved statistics for retry cost and difficulty updates. Unattested cost data MUST NOT influence proof truth and MAY be excluded from strict cost reports.

## 10.7 Budget terminal behavior

Budget exhaustion never accepts partial work.

Possible outcomes:

```text
BUDGET_EXHAUSTED
- root not proved

ROOT_PROVED_COVERAGE_UNCONVERGED
- root proved
- reviewer convergence unfinished

COMPLETE
- proof and convergence finished before budget limit
```

---

# 11. Reuse map

## 11.1 Reuse after interface cleanup and tests

| Existing capability | Reuse decision | New interface |
|---|---|---|
| Existing provider-specific `LlmClient` adapters | Do not place in proof core | Move to an external MCP runner package or separate repository |
| Existing streaming authentication and provider transport | Do not place in proof core | External runner concern; may be reused there with usage reporting |
| Response repetition detector | Split | External runner guards model streams; LLM-Driven Proof Search Environment independently rejects duplicate canonical submissions |
| Lean executable discovery | Reuse | Part of one supervised Lean service |
| Persistent Lean process supervision | Reuse | Single primary execution path, recovery fallback only |
| Lean JSON diagnostic parsing | Reuse | Populate `LeanDiagnostic` schema |
| No-sorry detection | Reuse and expand | Prohibited construct policy |
| SymPy parser allowlist | Reuse | Preflight/falsification only |
| Targeted SymPy operations | Reuse | No unbounded simplify, no proof authority |
| Contamination/evidence tests | Generalize and reuse | Typed theorem-fact and proposal-admission tests |
| Append-only DAG event concept | Reuse concept | One typed `events` table |
| Token and attempt accounting | Reuse concept | Enforced budget ledger |
| Tauri UI | Reuse as client | New core API and event stream |

## 11.2 Rebuild

| Area | Reason |
|---|---|
| Verification contract | Existing SymPy gate and advisory Lean are unsound `[Audit T-01]` |
| Obligation schema | Existing obligations lack mandatory theorem targets |
| Root formalization boundary | Existing formal statement is optional `[Audit F-01]` |
| Composition environment | Existing Lean checks isolated statements `[Audit T-05]` |
| Scheduler | Existing score ignores leverage and cost `[Audit §4.1]` |
| Retry context | Existing context replays too much history `[Audit C-03]` |
| Completion policy | Existing done decision is an LLM review `[Audit S-02]` |
| Reviewer system | Existing reviewers participate in closure |
| Cost governor | Rebuild for internal reservations plus external MCP model-call leases |
| Persistence | Existing graph and proof representations are duplicated |

## 11.3 Delete or quarantine

The following SHALL NOT be ported into the new proof core:

- Satisfaction tally code.
- Mechanical keyword closure checks.
- Solver closure claims.
- Reviewer/adversary closure votes.
- Auto-conclusion code.
- Conclusion review code.
- Sample-verified typed claim validators.
- SymPy `all_passed` proof gate.
- Dual `steps` and `proof_nodes` representation.
- Parallel parent/dependency encodings.
- Critic hot-path calls.
- Pattern extraction inside proof completion.
- Unused re-decomposition function.
- Unused stale-obligation expiry function.
- Substring known-answer acceptance gate.
- Duplicate Lean primary execution paths.
- Any provider SDK, provider credential reader, internal `LlmClient`, or background model invocation in the LLM-Driven Proof Search Environment process.
- Existing `verified` values as trusted facts.

## 11.4 Tauri client boundary

The Tauri UI MAY:

- Create a problem version.
- Display formalization candidates.
- Record fidelity approval.
- Start, pause, resume, or cancel a run.
- Display the Draft.
- Display the active Sketch graph.
- Display obligation attempts and structured diagnostics.
- Display budget state.
- Display certificate and convergence status.
- Add human-authored obligations or fidelity decisions.

The Tauri UI MUST NOT:

- Set proof status.
- Write directly to obligation or verified-lemma tables.
- Bypass the budget gateway.
- Supply arbitrary imports.
- Treat reviewer text as verified.

Suggested core API:

```text
create_problem_version
submit_formalization_candidate
approve_fidelity
create_draft
compile_initial_sketch
start_run
pause_run
resume_run
cancel_run
get_problem_state
get_obligation_graph
get_attempt_diagnostic
get_budget_state
get_certificate
stream_events
submit_human_obligation
resolve_fidelity_issue
```

---

# 12. Open questions

These decisions require a human owner before implementation. They do not change the hard invariants.

## 12.1 Lean environment scope

**Decision needed:** Which Lean and mathlib versions, imports, tactics, and plugins are allowed in the first release?

Recommended starting choice:

- One pinned Lean 4 toolchain.
- One pinned mathlib revision.
- A narrow import allowlist.
- No custom native plugins in the proof process.

Reason: reproducibility and sandbox simplicity.

## 12.2 Formalization approval UX

**Decision needed:** Who is authorized to approve fidelity for normal users?

Options:

1. Problem author approval.
2. Designated mathematical reviewer.
3. Signed trusted corpus manifest.

The system must record which method was used.

## 12.3 Trusted corpus governance

**Decision needed:** What process signs, samples, revokes, and versions trusted formalization manifests?

This is required before unattended benchmark-scale operation.

## 12.4 External role bindings

**Decision needed:** Which external runner configurations satisfy these capability tags?

```text
INFORMAL_MATH_FRONTIER
LEAN_FORMALIZATION
LEAN_PROVING
LEAN_REPAIR
COVERAGE_REVIEW
```

The proof core stores capability requirements, prompt hashes, action schemas, and attestation requirements. Provider names, model names, credentials, sampling controls, and fallback routing live exclusively in the external MCP runner.

The first implementation needs tested external role bindings and a declared fallback policy, but no provider package may be added to LLM-Driven Proof Search Environment.

## 12.5 Reviewer diversity fallback

**Decision needed:** If the external MCP runner can supply only one provider family, should the run:

- Require a human reviewer for the missing family, or
- Permit same-provider distinct models and prompts but mark convergence lower-assurance?

Recommended choice: require a human or second family for `COMPLETE`; otherwise allow only `ROOT_PROVED_COVERAGE_UNCONVERGED`.

## 12.6 Budget defaults

**Decision needed:** Product-level defaults for `max_total_cost_usd`, wall time, and review epochs.

The implementation must not invent a silent unlimited mode.

## 12.7 Sandbox architecture

**Decision needed:** Process-level sandbox for Lean and optional CAS tools on each supported OS.

Minimum requirements:

- No network from proof process.
- Read-only approved library paths.
- Write access only to a temporary problem workspace.
- CPU, memory, wall-time, and process-count limits.

## 12.8 Proof dependency inspection

**Decision needed:** Exact Lean API used to extract generated theorem constants from elaborated proof terms.

Acceptance test:

- A proof that omits a required dependency is rejected as a Sketch mismatch.
- A proof that uses an undeclared generated lemma is rejected.

## 12.9 Equivalence checker budget

**Decision needed:** Whether candidate formalization equivalence uses:

- Deterministic tactics first, then one prover call, or
- A dedicated equivalence prover configuration.

Recommended choice: deterministic tactics plus one budgeted prover call.

## 12.10 Old database migration

**Decision needed:** Whether to ship a legacy viewer or a one-time importer.

Recommended choice: read-only legacy viewer plus explicit re-verification import. Do not migrate old proof statuses.

## 12.11 Parallelism

**Decision needed:** Default outstanding MCP action-request concurrency by LLM-Driven Proof Search Environment hardware limits and external-runner capacity.

Recommended first release:

```text
2 concurrent obligations
1 candidate per obligation
portfolio mode off
1 supervised Lean worker with a serialized kernel-commit queue
```

## 12.12 Certificate export format

**Decision needed:** Whether the first certificate export is:

- JSON manifest plus Lean source bundle, or
- A signed archive containing source, `.olean` artifacts, environment manifest, and event subset.

Recommended choice: signed archive, with a human-readable JSON manifest at its root.

## 12.13 Theorem retrieval

**Decision needed:** Whether theorem retrieval is included in version 1.

Recommended choice: omit from the first proof-core milestone. Add only after the compact-context and compiler-feedback loop is stable and measured.

## 12.14 Completion assurance labels

**Decision needed:** User-facing labels for:

```text
Root kernel proved, coverage pending
Complete under configured reviewer convergence policy
Fidelity approval revoked
Legacy untrusted result
```

Labels must keep kernel truth, fidelity, and coverage confidence distinct.

---

# 13. Headless proof environment, MCP, and synthetic RL data

## 13.1 Purpose and trust boundary

LLM-Driven Proof Search Environment SHALL expose the proof core as a reproducible, machine-controlled environment in which an external MCP agent can observe proof state, submit typed actions, receive deterministic Lean-backed feedback, and continue until the task terminates or is truncated.

LLM-Driven Proof Search Environment SHALL NOT contain or invoke an LLM proposal client. The external agent host is both the MCP client and the model-inference owner. It may call a remote provider, a local model, a human, or a scripted policy. LLM-Driven Proof Search Environment does not know or care how the proposal was produced beyond the declared and optionally attested metadata required by policy.

The environment is a first-class product subsystem, but it is not a second proof engine. It wraps the same authoritative database, scheduler, budget governor, orchestrator, and Lean gateway defined in Sections 3 through 10. It MUST NOT duplicate obligation state, verification logic, theorem status, dependency composition, or budget accounting.

The trust boundary is:

```text
External LLM provider, local model, human, or scripted policy
        ^
        | provider-specific API owned outside LLM-Driven Proof Search Environment
        v
External agent host / synthetic-data runner
        |  MCP client
        v
LLM-Driven Proof Search Environment MCP server
        |
        v
Headless Episode Service
        |
        v
Authoritative LLM-Driven Proof Search Environment Orchestrator and Database
        |
        v
Supervised Lean Service
        |
        v
Lean kernel result and structured diagnostics
```

Only the Lean kernel may establish that an obligation is proved. Only the authoritative proof core may commit a verified lemma, transition an obligation to `proved`, or issue a root certificate. The external agent may propose actions. The environment may expose, score, and record committed events. Neither may manufacture proof truth.

The environment serves four distinct use cases:

1. Interactive tool use by external MCP-capable LLM agent hosts.
2. Reproducible model evaluation on formal reasoning tasks.
3. Bulk generation of verifier-backed synthetic trajectories by an external runner.
4. Reinforcement-learning interaction using deterministic proof-state transitions and Lean-derived rewards.

## 13.2 Environment authority model

The authoritative state transition function SHALL be implemented in the Rust core. Tauri and the MCP server call that function. Optional HTTP or Gym compatibility layers SHALL be MCP clients or thin adapters to the same service and MUST NOT contain provider clients or proof rules.

The canonical transition is conceptually:

```text
step(current_episode_revision, action_request_id, typed_action)
    -> accepted_or_rejected
    -> proof_core_transition
    -> Lean_result_when_required
    -> next_observation_or_action_request
    -> reward_components
    -> terminated
    -> truncated
    -> structured_diagnostics
    -> next_episode_revision
```

A transport adapter or external agent MUST NOT:

- Write directly to obligation, edge, proposal, lemma, certificate, or budget tables.
- Mark a theorem proved.
- Set its own reward from model output.
- Hide a Lean failure by converting it into a successful tool response.
- Maintain a second episode-specific copy of the proof graph as an authority.
- Bypass the reserve, lease, commit, release, and settlement protocol.

The LLM-Driven Proof Search Environment process MUST NOT:

- Import provider SDKs.
- Read provider API keys.
- Select a provider or model.
- Invoke model inference.
- Retry provider transport.
- Parse provider-specific streaming formats.
- Continue a model-dependent transition when no external action has been submitted.

## 13.3 Environment manifest

Every environment release SHALL publish a versioned manifest containing at least:

```text
EnvironmentManifest
- environment_id: String
- environment_version: SemVer
- protocol_version: SemVer
- database_schema_version: SemVer
- reward_policy_version: SemVer
- observation_schema_version: SemVer
- action_schema_version: SemVer
- trajectory_schema_version: SemVer
- lean_version: String
- lake_environment_hash: Hash
- base_theorem_environment_hash: Hash
- deterministic: Boolean
- supports_seed: Boolean
- supports_snapshot: Boolean
- supports_replay: Boolean
- supported_task_kinds: TaskKind[]
- supported_termination_reasons: Enum[]
- supported_truncation_reasons: Enum[]
- maximum_action_bytes: Integer
```

Environment versions are independent from the desktop application version. A trajectory MUST record every manifest version required to replay or interpret it.

## 13.4 Task definitions

Training and evaluation begin from immutable, versioned task definitions. A task is not merely a prompt. It binds a visible objective to hidden evaluator state and a pinned proof environment.

```text
EnvironmentTask
- id: UUID
- task_family_id: String
- task_revision: SemVer
- kind: obligation_proof | compiler_repair | decomposition | formalization |
        coverage_discovery | dependency_selection | root_completion
- problem_version_id: UUID
- initial_obligation_id: Optional<UUID>
- visible_instructions: Text
- hidden_evaluator_config: ArtifactRef
- allowed_action_kinds: ActionKind[]
- reward_policy_id: String
- completion_policy_id: String
- maximum_steps: Integer
- maximum_tokens: Integer
- maximum_cost_micro_usd: Integer
- wall_time_limit_ms: Integer
- seed_policy: fixed | parameterized
- source_provenance: Provenance
- license: String
- split: train | validation | test | private_eval
- content_hash: Hash
```

The task compiler SHALL produce two separate views:

- **Agent view:** only information the policy model is allowed to observe.
- **Evaluator view:** hidden expected properties, private test obligations, anti-leakage checks, and policy configuration.

Hidden evaluator data MUST NOT appear in observations, MCP resources, model prompts, public trajectories, or logs returned to the model.

### Initial task scope

The first environment release SHOULD prioritize the task kinds already supported by the rebuilt core:

1. Prove one ready obligation.
2. Repair a failed Lean proposal from structured diagnostics.
3. Decompose a blocked obligation into formal child statements.
4. Select a useful verified dependency from an approved local lemma set.
5. Complete the root proof from an existing verified dependency closure.

Formalization and coverage-discovery tasks SHOULD remain later milestones because they require stronger fidelity and admission policies.

## 13.5 Episode lifecycle

An episode is an isolated interaction with one immutable task definition.

```text
Episode
- id: UUID
- task_id: UUID
- task_revision: SemVer
- problem_version_id: UUID
- environment_version: SemVer
- protocol_version: SemVer
- reward_policy_version: SemVer
- seed: Integer
- status: active | awaiting_external_action | terminated | truncated | failed | archived
- current_step: Integer
- current_revision: Integer
- initial_state_hash: Hash
- current_state_hash: Hash
- budget_account_id: UUID
- started_at: Timestamp
- last_active_at: Timestamp
- completed_at: Optional<Timestamp>
- termination_reason: Optional<Enum>
- truncation_reason: Optional<Enum>
```

Required lifecycle operations:

```text
create_episode(task_id, seed, policy_options)
reset_episode(episode_id, seed)
observe_episode(episode_id)
step_episode(episode_id, expected_revision, idempotency_key, action)
snapshot_episode(episode_id)
restore_episode(snapshot_id)
status_episode(episode_id)
close_episode(episode_id)
replay_episode(trajectory_id)
export_trajectory(episode_id, format)
```

Resetting the same task under the same environment version, Lean environment hash, task revision, and seed MUST produce the same initial semantic state hash.

Episodes MUST be isolated. No obligation, proposal, diagnostic, hidden evaluator field, model response, or budget state from one episode may contaminate another.

## 13.6 Observation contract

An observation is the bounded proof state shown to the policy model. It is not a dump of the database or the complete problem history.

```text
Observation
- episode_id: UUID
- episode_revision: Integer
- step_index: Integer
- task_kind: TaskKind
- requested_role: ExternalRole
- action_request_id: UUID
- visible_objective: Text
- root_theorem_signature: Text
- selected_obligation: ObligationObservation
- approved_dependencies: LemmaSummary[]
- compact_context: Text
- latest_lean_diagnostics: LeanDiagnostic[]
- distilled_failure_lessons: Text[]
- allowed_actions: ActionDescriptor[]
- remaining_budget: BudgetObservation
- model_call_lease_policy: ModelCallLeasePolicy
- proof_progress: ProofProgressObservation
- state_hash: Hash
```

The observation policy SHALL follow the context evacuation rules in Section 10.4. It SHOULD contain only the target obligation, approved dependencies, compact diagnostics, and bounded failure lessons required for the next action.

By default, observations MUST NOT expose:

- Hidden evaluator state.
- Future task variants or private evaluation cases.
- A completed proof for the target obligation.
- Unapproved generated lemmas.
- Raw Draft text unless the task explicitly evaluates Draft-to-Sketch behavior.
- Other episodes or model trajectories.
- Database credentials, provider secrets, provider routing, filesystem paths, or sandbox controls.

## 13.7 Typed action contract

The model SHALL act through a versioned, bounded action union. Free-form text may be included as payload, but the environment transition itself MUST be typed.

Initial actions:

```text
Action
- submit_draft
- submit_formalization_candidate
- submit_sketch_proposal
- submit_lean_proposal
- submit_repair_proposal
- propose_decomposition
- submit_review_proposals
- select_dependency
- request_compact_hint
- declare_blocked
- abandon_attempt
```

Representative action shapes:

```text
SubmitLeanProposal
- action_request_id: UUID
- model_call_lease_id: Optional<UUID>
- obligation_id: UUID
- candidate_source: Text
- declared_dependency_ids: UUID[]
- external_agent_metadata: ExternalAgentMetadata
- declared_usage: Optional<ModelUsage>
```

```text
ProposeDecomposition
- parent_obligation_id: UUID
- child_statements: LeanStatementProposal[]
- proposed_edges: EdgeProposal[]
- natural_rationale: Optional<Text>
```

```text
RequestCompactHint
- obligation_id: UUID
- hint_kind: dependency_summary | diagnostic_explanation | statement_normalization
```

The environment MUST reject unknown fields, oversized payloads, stale episode revisions, invalid obligation references, undeclared dependency imports, and unsupported action kinds.

The external agent MUST NOT directly submit:

- A new obligation status.
- A verified lemma record.
- A reward.
- A certificate.
- A budget commit.
- A reviewer acceptance decision.
- A state hash or revision override.

## 13.8 External action request, lease, and step semantics

LLM-Driven Proof Search Environment advances internally until it requires a model-produced artifact. It then persists an immutable `ActionRequest`, transitions the episode to `awaiting_external_action`, and returns the bounded observation through MCP.

A compliant external runner performs these stages:

1. Call `episode_observe` and receive the active `ActionRequest`.
2. Optionally call `model_call_reserve` before inference when the run uses LLM-Driven Proof Search Environment cost accounting.
3. Invoke the selected provider or local model outside LLM-Driven Proof Search Environment.
4. Parse the model output into the allowed typed action.
5. Call `episode_step` with the action-request ID, expected revision, idempotency key, optional lease ID, typed action, and usage metadata.

Every submitted step SHALL execute in this order:

1. Validate protocol version, episode status, expected revision, action-request ID, idempotency key, and action schema.
2. Confirm that the action request is still active and that the submitted action is allowed for its role.
3. Validate or settle the external model-call lease when one is required.
4. Reserve the maximum possible LLM-Driven Proof Search Environment-controlled validation and Lean cost.
5. Apply repetitive-response, prohibited-construct, size, dependency, and preflight guards.
6. Stage the action against the authoritative proof state.
7. Invoke deterministic validation and the Lean gateway when required.
8. Commit or reject proof-state changes transactionally.
9. Commit or release internal reservations and settle, expire, or reject the external lease.
10. Calculate reward components from committed evidence.
11. Evaluate termination and truncation policies.
12. Append one immutable trajectory event containing the external action metadata.
13. Advance deterministically until the next external action request or terminal state.
14. Return the next observation, action request, reward, and structured diagnostics.

A rejected action MUST leave the semantic proof state unchanged. It still produces a trajectory event and may consume budget already spent on validation or Lean execution.

A duplicate idempotency key MUST return the original step result or a deterministic duplicate response. It MUST NOT apply the action twice.

No step implementation may invoke an LLM.

## 13.9 Reward model

Rewards SHALL be calculated by a versioned deterministic policy from proof-core and Lean evidence. The model may observe reward, but it may not propose, edit, or certify it.

The raw reward vector is authoritative. A scalar aggregation is a replaceable training policy.

Recommended initial reward components:

```text
RewardComponents
- action_schema_valid
- proposal_parsed
- proposal_elaborated
- target_statement_exact_match
- unsolved_goal_reduction
- diagnostic_novelty
- duplicate_response_penalty
- invalid_dependency_penalty
- obligation_kernel_proved
- dependency_composition_proved
- centrality_weighted_closure
- root_certificate_proved
- step_efficiency
- token_efficiency
- cost_efficiency
- budget_violation_penalty
- sandbox_violation_penalty
```

Hard reward rules:

1. `obligation_kernel_proved` is positive only when the exact stored theorem statement is accepted in the pinned Lean environment and the verified lemma commit succeeds.
2. `dependency_composition_proved` is positive only when the composition checks in Section 5.5 pass.
3. `root_certificate_proved` is positive only when the exact root theorem is kernel-checked and the certificate transaction commits.
4. LLM reviewers, natural-language critics, sampling, CAS checks, or model self-assessment MUST NOT generate proof rewards.
5. Parser success, elaboration progress, or reduced unsolved goals MAY provide bounded shaping rewards, but they MUST remain visibly distinct from theorem discharge.
6. Unrecognized constraints, missing diagnostics, tool failures, and verifier errors MUST fail closed and MUST NOT receive the corresponding positive reward.
7. Reward weights MUST be recorded by policy version. Changing weights MUST NOT rewrite historical raw evidence.

### Reward-hacking defenses

The environment SHALL test and guard against:

- Repeated syntactically different but semantically identical failed proposals.
- Empty proofs, placeholders, `sorry`, unsafe axioms, or disallowed imports.
- Artificial diagnostic churn that does not improve the proof state.
- Dependency declaration inflation.
- Excessive hint requests.
- Claiming completion without a committed certificate.
- Triggering infrastructure errors to avoid negative reward.

## 13.10 Termination and truncation

Termination and truncation MUST remain separate.

### Natural termination

An episode terminates when its task-defined objective is deterministically complete, for example:

- the target obligation is kernel proved
- the required repair is kernel proved
- an admitted decomposition is committed
- the root certificate is committed
- the model correctly declares a task blocked under a task policy that treats this as a terminal outcome

### External truncation

An episode is truncated when stopped by an external limit or infrastructure condition:

- maximum steps
- token budget
- monetary budget
- wall-time limit
- invalid-action limit
- Lean timeout threshold
- external-agent lease timeout or runner-unavailable threshold
- sandbox failure
- operator cancellation
- process crash recovery boundary

A truncated episode MUST NOT be reported as successful proof completion.

## 13.11 MCP-only model execution surface

MCP SHALL be the canonical and only model-facing execution surface. The external agent host is the MCP client. LLM-Driven Proof Search Environment is the MCP server.

The first MCP server SHOULD expose a small tool surface:

```text
environment_describe
task_list
task_describe
episode_create
episode_observe
model_call_reserve
model_call_release
episode_step
episode_status
episode_snapshot
episode_restore
episode_close
trajectory_export
```

`episode_observe` returns the current bounded observation and active `ActionRequest`. It never triggers inference.

`model_call_reserve` issues an optional budget lease to a trusted external runner before that runner calls its model. It never calls the model.

`episode_step` accepts the typed result after external inference and routes it through the authoritative transition function.

The environment SHOULD use one typed `episode_step` tool rather than one MCP tool for every proof operation. This limits tool explosion and ensures all model artifacts pass through the same action union and transition pipeline.

Suggested MCP resources:

```text
proofsearch://environment/manifest
proofsearch://environment/action-schema
proofsearch://environment/observation-schema
proofsearch://environment/role-contracts
proofsearch://tasks/{task_id}
proofsearch://episodes/{episode_id}/observation
proofsearch://episodes/{episode_id}/action-request
proofsearch://episodes/{episode_id}/diagnostics/latest
proofsearch://episodes/{episode_id}/trajectory
```

MCP responses MUST preserve structured diagnostics and protocol versions. They MUST NOT collapse a Lean error into a prose-only failure.

The first deployment SHOULD bind to local stdio or localhost. Remote MCP exposure requires scoped authentication, authorization, rate limits, audit logging, and explicit operator configuration.

No MCP server tool may accept provider credentials or provider-specific request bodies.

## 13.12 External runners and compatibility adapters

LLM-Driven Proof Search Environment SHALL NOT contain a model runner that imports provider SDKs. Bulk evaluation and synthetic-data generation are performed by a separate external runner acting as an MCP client.

### External synthetic-data runner

The runner MAY support repeated execution across task sets, models, sampling configurations, seeds, and policy configurations while enforcing:

- maximum total cost
- maximum total tokens
- per-episode limits
- wall-clock deadline
- model-call count
- bounded concurrency
- provider retry policy
- resumability without duplicate committed steps

The runner owns provider credentials, provider clients, model selection, provider retries, streaming, and cancellation. LLM-Driven Proof Search Environment owns tasks, observations, action admission, Lean verification, rewards, state transitions, trajectories, and export.

For strict budget enforcement, the runner MUST request and settle LLM-Driven Proof Search Environment model-call leases. A configured external-call budget without an active trusted consumer is not a proof-correctness defect, but it is a cost-governance defect and must be reported.

### Gymnasium-compatible wrapper

A Python Gymnasium wrapper MAY exist as an MCP client and map:

```text
reset(seed, options) -> observation, info
step(action) -> observation, reward, terminated, truncated, info
close()
```

The wrapper MUST NOT call a model automatically unless it is explicitly operating as the external agent runner. It MUST NOT implement proof rules, rewards, termination policy, or state transitions.

### HTTP or gRPC compatibility

HTTP or gRPC MAY be provided for administration, artifact transfer, or high-throughput non-model integrations. It is not an alternative hidden model path. Any model-producing workflow must remain attributable to an external actor and must submit the same typed action contract, preferably through MCP.

## 13.13 Trajectory record

Every accepted or rejected step SHALL append one immutable trajectory event.

```text
TrajectoryEvent
- event_id: UUID
- trajectory_id: UUID
- episode_id: UUID
- task_id: UUID
- step_index: Integer
- parent_event_id: Optional<UUID>
- environment_version: SemVer
- protocol_version: SemVer
- lean_environment_hash: Hash
- reward_policy_version: SemVer
- action_request_id: UUID
- external_runner_config_hash: Optional<Hash>
- declared_model_config_hash: Optional<Hash>
- model_call_lease_id: Optional<UUID>
- usage_attestation_level: Optional<Enum>
- observation_hash: Hash
- observation: Observation
- raw_model_output: Optional<ArtifactRef>
- parsed_action: Action
- action_accepted: Boolean
- proposal_attempt_id: Optional<UUID>
- lean_result: Optional<StructuredLeanResult>
- diagnostics: LeanDiagnostic[]
- proof_events_committed: ProofEventRef[]
- reward_components: RewardComponents
- scalar_reward: Optional<Number>
- state_hash_before: Hash
- state_hash_after: Hash
- terminated: Boolean
- truncated: Boolean
- termination_reason: Optional<Enum>
- truncation_reason: Optional<Enum>
- model_metadata: Optional<ModelMetadata>
- token_usage: Optional<TokenUsage>
- cost_micro_usd: Integer
- latency_ms: Integer
- created_at: Timestamp
```

Trajectories MUST preserve failures. Parse errors, type mismatches, unsolved goals, invalid imports, duplicate responses, repairs, and abandoned branches are valuable training data when accurately labeled.

The trajectory record SHALL reference existing `proposal_attempts`, `verified_lemmas`, obligations, and certificates rather than duplicating those records as competing authorities.

## 13.14 Replay and determinism

Replay SHALL reconstruct an episode without invoking an LLM. It reuses the recorded typed actions and verifies that the authoritative state machine produces the same committed proof events and semantic state hashes.

Replay MUST check:

- task content hash
- environment and protocol versions
- database schema version
- Lean version and environment hash
- reward policy version
- action ordering
- idempotency behavior
- proof commit outcomes
- state hash after every step
- termination or truncation result

A divergence MUST fail at the first mismatching step and identify the field or event that differs.

External model nondeterminism is not replayed. The raw model response and parsed action are historical inputs. Replay verifies the environment response to those inputs.

## 13.15 Synthetic data products

The canonical trajectory MAY be transformed into multiple derived datasets without changing the original record.

Supported derived views SHOULD include:

- supervised proof-proposal pairs
- compiler-diagnostic repair pairs
- successful multi-step proof trajectories
- failed and recovered trajectories
- preference pairs derived from deterministic proof outcomes and cost
- step-level RL tuples
- obligation-decomposition examples
- dependency-selection examples
- model evaluation summaries
- oracle-trust and tool-use traces

Derived data MUST preserve references to:

- source task and split
- canonical trajectory and event IDs
- model and prompt versions
- Lean environment hash
- reward policy
- licensing and provenance
- redaction policy
- generator and exporter versions

A preference pair MUST NOT be labeled from an LLM judge alone when deterministic Lean outcomes are available. The pair construction policy SHALL state exactly which evidence made one trajectory preferable.

## 13.16 Dataset governance and contamination control

Synthetic generation SHALL use stable train, validation, test, and private evaluation splits.

The system MUST prevent leakage through:

- parameter variants of the same theorem family crossing protected splits
- hidden evaluator lemmas appearing in observations or retrieval indexes
- completed certificates entering prompts for their own target tasks
- replay logs from evaluation episodes entering training exports without explicit approval
- model-specific private data being exposed to other runs
- theorem retrieval returning a target-equivalent proof from a protected split

Every dataset export SHALL include a manifest containing:

- dataset ID and version
- source task families and revisions
- split policy and contamination checks
- environment, Lean, protocol, and reward versions
- model configurations
- trajectory counts and outcome distribution
- checksums
- license and provenance
- filtering and redaction rules
- known limitations

## 13.17 Security and sandboxing

The environment executes model-generated Lean source and MUST treat it as untrusted input.

Required controls:

- process isolation for Lean workers
- bounded CPU, memory, wall time, process count, and file size
- no network access from proof workers by default
- allowlisted imports and package environment
- temporary per-episode workspaces
- canonical path validation
- no shell interpolation of model text
- output-size limits
- cleanup after timeout or crash
- structured classification of sandbox failures
- local-only MCP binding by default

The proof worker MUST reject `sorry`, unsafe axioms, disallowed imports, environment mutation, and any construct forbidden by the trusted theorem policy.

## 13.18 Environment storage additions

Add the following tables or equivalent append-only stores. They supplement the proof schema and MUST NOT duplicate its authority.

```text
environment_tasks
episodes
action_requests
model_call_leases
episode_steps
episode_snapshots
trajectory_exports
dataset_manifests
external_runner_configs
external_run_jobs
```

`episode_steps` SHALL reference proof-core records such as `proposal_attempts`, `verified_lemmas`, proof events, and certificates. It MUST NOT contain a second mutable obligation status or duplicate verified theorem body that can drift from the core.

## 13.19 Environment invariants

The following invariants are mandatory:

1. **Lean-only positive proof reward:** no kernel-backed proof event, no theorem-discharge reward.
2. **One proof authority:** adapters and episodes cannot mutate proof status outside the core transition service.
3. **Episode isolation:** no cross-episode state, diagnostic, budget, hidden-data, or artifact leakage.
4. **Deterministic reset:** identical pinned inputs and seed produce the same initial semantic state.
5. **Replayability:** recorded actions reproduce committed proof events and state hashes.
6. **Budget enforcement:** no LLM-Driven Proof Search Environment-controlled Lean or tool call occurs without a reservation; no compliant external inference occurs without a model-call lease when the run policy requires one.
7. **External-model boundary:** LLM-Driven Proof Search Environment contains no provider client, credentials, inference call, or provider retry loop.
8. **Fail-closed diagnostics:** parser, verifier, sandbox, and infrastructure uncertainty cannot become success.
9. **No hidden-answer leakage:** evaluator-only data never crosses the observation boundary.
10. **MCP action parity:** the MCP server and direct Rust conformance harness produce identical transitions for identical typed actions; optional wrappers are tested as MCP clients.
11. **Append-only trajectory truth:** failures and retries are preserved rather than rewritten into a clean success story.
12. **Version binding:** task, environment, Lean, schema, reward, role, lease, and protocol versions are recorded for every episode.
13. **Termination integrity:** truncation is never reported as natural task success.

## 13.20 Required environment tests

Before the environment may be described as RL-compatible, CI SHALL cover:

- deterministic reset across processes
- episode isolation and contamination attempts
- stale revision and duplicate idempotency handling
- direct Rust transition service and MCP server parity
- optional Gym wrapper parity as an MCP client
- proof that no LLM-Driven Proof Search Environment binary imports provider SDKs or reads provider API-key environment variables
- external-runner disconnect leaves proof state unchanged
- model-call lease denial, expiry, settlement, and misreported-usage handling
- hidden evaluator leakage through observations, resources, logs, and exports
- reward-hacking proposals
- exact zero reward versus missing evidence
- Lean timeout and sandbox failure behavior
- budget exhaustion and truncation
- crash between Lean verification and database commit
- replay of accepted and rejected actions
- replay divergence after version mismatch
- trajectory schema validation
- dataset manifest and checksum validation
- train/test theorem-family contamination checks
- local MCP end-to-end proof episode
- external MCP runner resume without duplicate proof commits

## 13.21 Current implementation alignment

The current rebuilt Rust components already provide most of the internal environment machinery:

- The SQLite schema supplies immutable problem versions, obligations, edges, proposal attempts, and verified lemmas.
- The Lean gateway supplies deterministic validation and structured diagnostics.
- The budget governor supplies internal-operation reservations and can be extended with external model-call leases.
- The priority scheduler supplies deterministic work selection and progress features.
- The compact context builder supplies bounded observations.
- The orchestrator loop supplies the authoritative state transition logic and must be converted from internal-call assumptions to a reactive action-request state machine.

The environment work is therefore primarily an extraction and protocol task, not a rewrite. The next implementation boundary is to make the orchestrator emit typed action requests and accept typed MCP submissions without any provider client in the LLM-Driven Proof Search Environment process.

### Immediate next build

1. Remove or quarantine the planned internal LLM proposal adapter.
2. Convert the orchestrator into a reactive `advance -> ActionRequest -> episode_step` state machine.
3. Extract a framework-independent Rust `EpisodeService` over that orchestrator.
4. Define versioned task, role, observation, action-request, action, step-result, reward, lease, and trajectory schemas.
5. Add isolated episode reset, revision, idempotency, snapshot, and replay.
6. Expose the service through MCP over local stdio.
7. Implement repetitive-response and proposal preflight guards on submitted actions, independent of provider transport.
8. Build a separate external MCP runner for model routing and synthetic-data generation.
9. Add an MCP-client Gym wrapper if required by training infrastructure.
10. Add conformance, contamination, replay, lease-accounting, and reward-hacking tests.

---

## Implementation milestone sequence

This sequence is normative for minimizing risk, though it does not add new architecture.

```text
Milestone 1
- Problem versions
- Mandatory root theorem
- Fidelity approval gate
- Pinned Lean environment

Milestone 2
- Obligations and one edge table
- Exact theorem discharge
- Content-addressed verified lemmas
- Root certificate without reviewers

Milestone 3
- Budget governor
- Compact context builder
- Structured diagnostics
- Compiler-feedback retry

Milestone 4
- Draft and Sketch compiler
- Decomposition policy
- High-leverage scheduler

Milestone 5
- Diverse reviewer epochs
- Proposal admission
- Convergence monitor

Milestone 6
- Framework-independent Rust EpisodeService
- Versioned environment, task, observation, action, reward, and trajectory schemas
- Deterministic reset, snapshot, replay, and episode isolation

Milestone 7
- MCP server over local stdio
- HTTP and Gymnasium-compatible adapters
- Direct adapter parity tests

Milestone 8
- External MCP synthetic-data runner (separate process/package)
- Synthetic trajectory and dataset export
- Reward-hacking, contamination, and replay conformance suite

Milestone 9
- Tauri UI adapter
- Legacy read-only viewer
- Certificate export
- Environment and dataset operations UI
```

No milestone may reintroduce a non-Lean acceptance path as a temporary shortcut.

## Final architectural statement

LLM-Driven Proof Search Environment’s core is not a conversation, a vote, or a chain of plausible statements. It is an immutable formal target, a dynamically discovered graph of formal obligations, and a content-addressed Lean certificate that proves the obligations compose to the root. Models may plan, formalize, propose, repair, and search for missing coverage. Only the Lean kernel may discharge a theorem, and only deterministic state plus measured reviewer convergence may complete a proof run.

The headless environment makes that same proof machine reproducible and model-callable. The MCP server presents state and accepts typed actions. External runners and optional Gym wrappers may invoke models outside LLM-Driven Proof Search Environment and submit those actions, but they may never become alternative proof authorities. This separation is what allows LLM-Driven Proof Search Environment to generate high-value synthetic RL data: every positive proof signal is tied to a replayable state transition and a kernel-checked formal artifact.
