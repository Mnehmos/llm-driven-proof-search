# Mathematical Claim Engine

## Binding Product and Implementation Specification

**Document status:** Normative  
**Target release:** `1.0.0`  
**Intended location:** repository root as `SPEC.md`  
**Primary implementation language:** Rust  
**Primary formal verifier:** Lean 4  
**Primary external protocol:** Model Context Protocol  
**Primary deployment model:** local-first, single-machine, production software  
**Design doctrine:** AI proposes. Systems validate. Commits are controlled. The trace remembers.

---

# 0. Authority of this document

This document is the product contract for the repository.

It defines:

- what must be built;
- what must not be built;
- what counts as mathematically established;
- what counts as a finished software feature;
- how the implementation agent must work;
- the conditions under which work may stop.

When the code, README, issue text, agent assumption, or prior implementation conflicts with this specification, this specification wins unless an accepted Architecture Decision Record explicitly amends it.

This is not a brainstorming document, prototype brief, or aspirational roadmap. It is an implementation specification for a finished product.

## 0.1 No prototype clause

There is no prototype phase and no prototype deliverable.

The implementation agent must not stop after producing any of the following:

- a schema scaffold;
- a partial database;
- a CLI skeleton;
- an MCP server with placeholder handlers;
- a mock verifier;
- a happy-path demo;
- a single successful pilot;
- generated documentation without functioning software;
- an architecture that is not exercised end to end;
- a release that depends on the originating local database;
- a feature described as "MVP complete" while acceptance criteria remain unmet.

Incremental work is expected. Partial work may be committed. The final stopping condition is the complete Definition of Done in this document.

Pilots are acceptance tests for the product. They are not substitutes for the product.

## 0.2 Interpretation rule

When two designs satisfy the requirements, choose the simpler design.

When simplicity conflicts with a trust invariant, reproducibility, mathematical fidelity, data integrity, or security boundary, preserve the invariant and implement the simplest design that preserves it.

Do not trade away diligence in the name of simplicity. Do not add complexity in the name of hypothetical future scale.

---

# 1. Mission

The Mathematical Claim Engine accepts a mathematical source or statement from any level of mathematics and constructs a persistent, portable, machine-readable record that can:

1. identify and normalize the claim;
2. connect it to mathematical concepts and prior work;
3. produce one or more exact formalizations;
4. review whether each formalization faithfully represents the source;
5. search for edge cases and counterexamples;
6. prove, disprove, repair, classify, reduce, or leave the claim honestly open;
7. verify authoritative artifacts with Lean or another explicit certificate checker;
8. preserve successful attempts, failed attempts, diagnostics, and repairs;
9. promote reusable definitions and theorems;
10. construct machine-readable pedagogy from first principles to the research frontier;
11. publish portable, reproducible releases;
12. derive safe training, preference, reinforcement-learning, and evaluation tasks.

The product is a mathematical knowledge-production and verification system. It is not merely a theorem-completion tool.

## 1.1 Product boundary

The product operates on mathematical claims. It does not attempt to contain all mathematics at release time.

"Every level of mathematics" means that the workflow, schema, trust model, and pedagogy model must support:

- elementary statements;
- textbook theorems;
- competition problems;
- undergraduate and graduate mathematics;
- research formalizations;
- open conjectures;
- finite computational claims;
- false, ambiguous, malformed, and repairable statements.

The `1.0.0` product is complete when it can process these classes correctly through the full lifecycle. It is not required to pre-populate a complete curriculum of all mathematics.

## 1.2 Useful terminal outcomes

An investigation may end with any of the following useful outcomes:

- a kernel-verified proof;
- a verified counterexample;
- a formal disproof;
- a corrected statement;
- a conditional theorem with explicit assumptions;
- an equivalence or reduction;
- a classification theorem;
- a verified finite certificate;
- a proved method obstruction;
- an independent reproduction of prior work;
- reusable formal infrastructure;
- a precise unresolved obligation;
- a machine-readable lesson, exercise, misconception, or frontier note.

The system must never manufacture a proof-like success merely to avoid an open outcome.

---

# 2. Governing invariants

These invariants must be enforced in code, database constraints, verifier policy, CI, or release policy. Prompt instructions do not count as enforcement.

| Invariant | Required enforcement |
|---|---|
| An agent cannot mark a claim proved or disproved | No direct status-mutation API exists |
| A model response is never proof authority | Only verifier-produced evidence may be authoritative |
| A source claim is distinct from a formal statement | Separate immutable entities and versions |
| One claim may have multiple formalizations | One-to-many model; no canonical overwrite |
| Changing a formal statement invalidates prior fidelity and proof applicability | New immutable formalization version |
| Kernel correctness and statement fidelity are independent | Separate evidence axes |
| Empirical failure to find a counterexample proves nothing | Empirical evidence cannot derive universal truth |
| Every authoritative result is portable | Release contains all material needed without the operational database |
| Logical dependencies and teaching prerequisites are different relations | Separate edge namespaces |
| Failed attempts remain visible | Append-only run history and immutable failure evidence |
| Public export is fail-closed | License, provenance, hash, trust, and redaction gates |
| Model inference is external | No provider SDKs, API keys, or model routing in the core |
| Every canonical mutation is traceable | Append-only event chain and actor/run attribution |
| Old versions are not silently rewritten | Immutable versions and explicit supersession |
| Novelty is not inferred from absence of search results | Separate reviewed novelty evidence |
| A release never relies on undocumented local state | Self-contained manifest and replay instructions |
| A clean build and a faithful theorem are distinct claims | Separate reproducibility and fidelity records |
| A replayed episode is not itself the mathematical proof | Proof authority references the checked artifact |

---

# 3. Development doctrine and hierarchy of controls

This repository follows the guidance of the Vibe Coder's Bible:

> Trust AI to propose. Verify before commit.

The software must be designed so that generation-level hallucinations may occur as untrusted proposals, but cannot silently become committed mathematical truth or production state.

## 3.1 Hierarchy of controls

Every hazardous capability must be addressed from strongest to weakest control.

### Elimination

Remove the hazard where possible.

- No provider credentials in the engine.
- No arbitrary shell tool exposed to agents.
- No direct SQL access exposed to agents.
- No direct proof-status mutation.
- No direct protected-branch writes.
- No network access in authoritative verifier jobs.
- No broad filesystem writes from verifier code.
- No automatic public export of restricted proof bodies.
- No unpinned dependencies in public releases.
- No generic plugin execution in `1.0.0`.

### Substitution

Replace dangerous mechanisms with safer ones.

- Typed actions instead of raw commands.
- Allowlisted verifier invocations instead of shell access.
- Content-addressed artifact references instead of opaque local paths.
- Temporary workspaces instead of repository-wide writes.
- Deterministic witness checkers instead of trusting solver output.
- Dry-run release previews instead of immediate publication.
- Immutable formalization variants instead of statement mutation.
- External taxonomy crosswalks instead of unreviewed content copying.

### Engineering controls

- Rust types and exhaustive enums.
- Committed JSON Schemas.
- Database constraints and migrations.
- Explicit state machines.
- Compare-and-swap revisions.
- Job leases and idempotency keys.
- Sandboxed and resource-limited verifier subprocesses.
- Content hashes and environment manifests.
- Append-only run events.
- Clean CI builds.
- Axiom audits and proof-closure scans.
- Release verification and replay.

### Administrative controls

- Architecture Decision Records.
- Issue-first implementation.
- Review roles for fidelity and release approval.
- Release and correction policies.
- Licensing and provenance review.
- Deprecation and migration policy.
- Incident, takedown, and disclosure procedure.

### PPE

- Agent instructions.
- Coding conventions.
- Reminders to search before rebuilding.
- Warnings against novelty overclaims.
- Manual vigilance.

PPE is useful but is never accepted as the only control for a high-consequence operation.

---

# 4. The implementation agent's looping goal

The implementation agent must operate a persistent delivery loop until the complete product satisfies the Definition of Done.

## 4.1 Required loop

```text
while DefinitionOfDone is not satisfied:
    1. Read SPEC.md and the current repository state.
    2. Read the implementation ledger, open issues, failures, and ADRs.
    3. Select the highest-priority unmet acceptance criterion that is not blocked.
    4. Confirm existing code and dependencies before designing new abstractions.
    5. Write or update the issue-level plan and explicit acceptance checks.
    6. Implement the smallest complete production slice that advances the criterion.
    7. Add or update tests, schemas, migrations, documentation, and operational controls.
    8. Run all local checks relevant to the change.
    9. Perform a self-review against this spec and the hierarchy of controls.
   10. Record evidence, decisions, known limitations, and exact commands run.
   11. Commit one coherent change.
   12. Update the implementation ledger.
   13. Repeat without waiting for a new prompt.
```

## 4.2 Work-selection priority

Select work in this order:

1. broken build, data corruption, proof-authority, or security defect;
2. blocked end-to-end acceptance criterion;
3. missing core domain capability;
4. missing verifier or portability capability;
5. missing pedagogy or export capability;
6. migration and compatibility work;
7. performance work supported by measurement;
8. ergonomic improvements;
9. optional polish.

Do not prioritize visual polish, abstraction, or speculative scale ahead of an incomplete product lifecycle.

## 4.3 Stop conditions

The implementation agent may stop only when one of these conditions holds:

### Completion

Every Definition of Done item passes from a clean checkout and a release candidate has been produced and verified.

### Irreducible external blocker

A decision, credential, legal approval, inaccessible source, or external system is strictly required and no conservative reversible default is safe.

When blocked, the agent must:

1. document the exact blocker;
2. document every attempted resolution;
3. identify the smallest human decision required;
4. continue all unrelated work;
5. stop only if all remaining work is blocked.

"The task is large," "the problem is difficult," "the feature is future work," and "a prototype now would be easier" are not valid stop conditions.

## 4.4 No fake completion

A feature is not complete unless it is:

- integrated into the real path;
- durable across process restart;
- covered by tests;
- documented for users and maintainers;
- observable in failure;
- included in migrations where needed;
- protected by applicable controls;
- exercised by an acceptance test;
- included in release verification.

Mocks and stubs may exist only in tests. A mock-backed path cannot satisfy a product acceptance criterion.

---

# 5. Product workflows

The engine must support five complete workflows.

## 5.1 Claim intake

```text
source ingestion
→ claim extraction
→ normalization
→ concept classification
→ duplicate and prior-art search
→ formalization candidates
```

## 5.2 Truth investigation

```text
claim and formalization
→ edge-case analysis
→ counterexample search
→ library and literature search
→ proof or disproof plan
→ verifier-gated attempts
→ result or explicit frontier
```

## 5.3 Reusable knowledge promotion

```text
verified local result
→ deduplication
→ generalization review
→ stable declaration
→ dependency edges
→ canonical searchable record
```

## 5.4 Pedagogy construction

```text
concept and claim graph
→ prerequisites
→ explanation
→ examples and nonexamples
→ counterexamples and misconceptions
→ exercises and mastery checks
→ frontier placement
```

## 5.5 Publication and learning export

```text
canonical objects and evidence
→ policy validation
→ portable release
→ clean replay
→ MathCorpus or MCIP projection
→ RL and evaluation tasks
```

---

# 6. Architecture

## 6.1 Required architecture

The `1.0.0` implementation is a local-first modular monolith.

```text
External model host or human
            │
            ├── MCP
            └── CLI
                   │
                   ▼
        one Rust application binary
          ┌─────────────────────┐
          │ domain and policies │
          │ query and context   │
          │ jobs and runs       │
          │ release builder     │
          └──────────┬──────────┘
                     │
       ┌─────────────┼──────────────┐
       ▼             ▼              ▼
   SQLite        artifact store   Lean worker
   canonical     local CAS        subprocess
   state
                     │
                     ▼
             portable releases
```

One binary may expose subcommands such as `serve`, `worker`, `doctor`, `release`, and ordinary CLI operations. Separate deployable services are not required.

## 6.2 Required technology choices

- Rust stable, current edition used by the repository.
- One SQLite database in WAL mode.
- One content-addressed artifact directory.
- One durable SQLite-backed jobs table.
- One Lean 4 verifier implementation.
- One MCP adapter.
- One CLI.
- Committed JSON Schemas generated from or checked against Rust types.
- SHA-256 for canonical content and artifact identities.
- SQLite FTS5 for full-text search.
- Structured JSON logs plus human-readable CLI output.

## 6.3 Deliberately excluded from `1.0.0`

Do not add any of the following unless this specification is amended by ADR and measured evidence:

- microservices;
- Kubernetes;
- Redis;
- Kafka or another message broker;
- a graph database;
- a vector database;
- an embedded model router;
- provider-specific inference SDKs;
- a generic workflow language;
- a general plugin marketplace;
- multiple proof assistants;
- a browser dashboard;
- arbitrary code execution supplied by agents;
- automatic public novelty claims;
- automatic merging of competing formalizations.

## 6.4 Simplicity rules

- Prefer modules over crates until a real compile, ownership, or reuse boundary exists.
- Prefer explicit enums over stringly typed status fields.
- Prefer one canonical representation over synchronized duplicates.
- Prefer a typed edge table over a graph database.
- Prefer exact search and FTS before embeddings.
- Prefer direct functions over internal RPC.
- Prefer a narrow Lean adapter over a generic plugin system.
- Do not introduce an abstraction until at least two concrete product paths require it, except where a trust boundary requires the abstraction immediately.

---

# 7. Repository layout

The implementation should converge on this structure. Existing code may be migrated incrementally, but `1.0.0` must present a coherent layout.

```text
SPEC.md
README.md
CHANGELOG.md
LICENSE
mcl.toml.example

src/
  main.rs
  config.rs
  domain/
  store/
  artifacts/
  graph/
  runs/
  jobs/
  verifier/
  query/
  context/
  pedagogy/
  release/
  mcp/
  cli/
  policy/
  import/

schemas/
  source/
  concept/
  claim/
  formalization/
  artifact/
  evidence/
  pedagogy/
  release/
  mcip/

migrations/
fixtures/
  elementary_false_claim/
  textbook_theorem/
  bh_formalization/
  erdos_647/

tests/
  integration/
  adversarial/
  release/

docs/
  architecture/
  decisions/
  operations/
  trust/
  formats/
  migration/
  implementation/
    STATUS.md
    BLOCKERS.md
    RELEASE_CHECKLIST.md

.github/
  workflows/
```

The README is an entry point. It must link to this specification rather than duplicate it.

---

# 8. Canonical data model

The canonical unit is a mathematical claim and its evidence graph.

The physical store may use a generic immutable record/version mechanism, but the logical API must expose typed entities.

## 8.1 Source

A source is the origin of a mathematical object.

Examples:

- paper;
- textbook;
- benchmark;
- repository;
- webpage;
- dataset;
- user statement;
- conversation excerpt;
- historical archive.

Required fields:

- stable ID;
- immutable version hash;
- source type;
- title or label;
- authors or origin;
- canonical locator;
- acquisition date;
- license and redistribution status;
- content hash where content is stored;
- citation metadata;
- redaction class;
- provenance notes.

## 8.2 Concept

A concept is a mathematical idea rather than a truth-valued assertion.

Examples:

- prime number;
- covariance;
- compactness;
- false discovery rate;
- Selberg sieve.

Required fields:

- name;
- aliases;
- description;
- subject domains;
- related formal declarations;
- external taxonomy crosswalks;
- pedagogy metadata references;
- provenance.

A concept does not have one universal difficulty level.

## 8.3 Claim

A claim is a truth-valued assertion, question, definition obligation, or classification target.

Required fields:

- source reference;
- normalized informal statement;
- claim kind;
- logical shape where known;
- assumptions;
- variables and domain notes;
- concept links;
- source citations;
- ambiguity notes;
- current version hash.

Claim kinds include:

```text
universal
existential
equality
inequality
equivalence
classification
finite_computation
open_question
definition_soundness
method_claim
```

## 8.4 Formalization

A formalization is one exact formal interpretation of a claim.

Required fields:

- claim version;
- formal system;
- environment reference;
- module artifact;
- declaration name;
- exact theorem type or declaration hash;
- import manifest;
- formalization notes;
- fidelity evidence references;
- verification evidence references.

A claim may have multiple formalizations. No formalization silently replaces another.

## 8.5 Artifact

An artifact is a content-addressed file or structured object.

Examples:

- Lean module;
- proof term;
- counterexample witness;
- generated data;
- LRAT certificate;
- axiom report;
- build log;
- explanation;
- release manifest.

Required fields:

- SHA-256 hash;
- media type;
- byte size;
- storage path derived from hash;
- creation source;
- license or restriction;
- optional semantic metadata.

## 8.6 Evidence

Evidence records what supports a statement about an exact object version.

Evidence kinds include:

```text
lean_elaboration
lean_kernel_proof
lean_kernel_refutation
certificate_replay
bounded_computation
empirical_search
statement_fidelity_review
literature_review
novelty_review
axiom_audit
proof_closure_scan
clean_rebuild
comparator_run
human_review
```

Required fields:

- subject object and exact version;
- evidence kind;
- result;
- authority class;
- producing run;
- artifact references;
- verifier or reviewer identity;
- environment manifest;
- timestamp;
- supersession or staleness metadata.

## 8.7 Edge

Edges are typed and versioned relationships.

### Logical edges

```text
logic.uses_definition
logic.depends_on
logic.implies
logic.equivalent_to
logic.contradicts
logic.generalizes
logic.specializes
logic.formalizes
```

### Pedagogical edges

```text
pedagogy.hard_prerequisite
pedagogy.soft_prerequisite
pedagogy.motivates
pedagogy.example_of
pedagogy.counterexample_to
pedagogy.misconception_for
pedagogy.recommended_next
```

### Research edges

```text
research.uses_technique
research.blocks_method
research.repairs
research.reduces_to
research.open_obligation_of
```

### Provenance edges

```text
provenance.derived_from
provenance.cites
provenance.independently_reproduces
provenance.supersedes
provenance.upstreamed_to
```

### Implementation edges

```text
implementation.declared_in
implementation.imports
implementation.generated_from
implementation.verified_by
implementation.replayed_by
```

Hard pedagogical prerequisites must remain acyclic. Logical equivalence may form cycles.

## 8.8 Run and event

A run is one execution history.

Run kinds:

```text
formalize
prove
disprove
counterexample_search
library_search
literature_review
generalize
audit
pedagogy_build
release_build
migration
```

A run is not mathematical authority.

Every run contains append-only hash-chained events. Events include typed actions, inputs, outputs, diagnostics, lease changes, and evidence links.

## 8.9 Learning unit

A learning unit is a machine-readable pedagogical artifact.

Unit kinds include:

```text
motivation
definition
explanation
example
nonexample
counterexample
misconception
worked_proof
exercise
mastery_check
application
history
frontier_note
```

Required fields:

- target concept or claim;
- audience track;
- learning objectives;
- prerequisite edges;
- grounded source and formal references;
- content artifact;
- review state;
- license;
- training eligibility.

## 8.10 Environment

An environment pins the verifier context.

Required fields:

- Lean toolchain;
- Mathlib or dependency revisions;
- import manifest;
- project configuration hashes;
- platform and trust profile;
- verifier command template;
- resource limits;
- environment hash.

## 8.11 Release

A release is an immutable portable snapshot of selected objects, edges, evidence, artifacts, and replay instructions.

A release is not complete until it verifies without the originating operational database.

---

# 9. Physical persistence model

The physical model should remain small.

```text
records
record_versions
edges
artifacts
evidence
runs
run_events
jobs
environments
releases
schema_migrations
```

## 9.1 Immutable versions

Every canonical object has:

- a stable object ID, preferably UUIDv7;
- one or more immutable content versions;
- a current head pointer;
- optional tombstone or supersession state.

Updates create new versions. They do not rewrite old content.

## 9.2 Canonical hashes

```text
record_version_hash =
SHA256(schema_version || NUL || canonical_json(payload))

artifact_hash =
SHA256(raw_bytes)

environment_hash =
SHA256(canonical_json(environment_manifest))

run_event_hash =
SHA256(previous_event_hash || canonical_json(event))
```

Canonical JSON must have deterministic key ordering, number representation, Unicode handling, and whitespace rules. Golden test vectors are mandatory.

Timestamps, local paths, machine names, and database row numbers must not enter content identity hashes.

## 9.3 Content-addressed artifact store

Artifacts are stored under a deterministic path such as:

```text
artifacts/sha256/ab/cd/<full-hash>
```

Writes are atomic:

1. write to a temporary file;
2. fsync where supported;
3. verify the hash;
4. rename into place;
5. commit the database reference.

The engine must reject path traversal and symlink escapes.

---

# 10. Independent status axes

Do not use one overloaded status field.

## 10.1 Statement fidelity

```text
unreviewed
attested
benchmark_aligned
verified
rejected
superseded
```

`verified` requires evidence-backed review that the formal statement represents the source claim at the declared fidelity level.

## 10.2 Formal verification

```text
unsubmitted
elaboration_failed
kernel_failed
kernel_verified
certificate_verified
publication_verified
stale
```

## 10.3 Research status

```text
not_started
active
open
conditionally_resolved
proved
disproved
malformed
ambiguous
superseded
```

Research status is derived from evidence. It is not directly set.

## 10.4 Novelty status

```text
not_assessed
known_result
new_formalization
new_application_candidate
new_proof_candidate
new_theorem_candidate
expert_reviewed
```

No automated search may produce `expert_reviewed`.

## 10.5 Publication status

```text
private
quarantined
releasable
released
retracted
```

## 10.6 Training status

```text
ineligible
quarantined
eligible_private
eligible_public
held_out_eval
```

---

# 11. Derived truth rules

No agent action may directly set `proved` or `disproved`.

## 11.1 Proved source claim

A source claim is derived as proved only if there exists a formalization version such that:

1. its fidelity status is `verified` for the relevant source claim version;
2. its proof evidence is authoritative and current;
3. its environment and dependencies are pinned;
4. no required artifact is missing or stale;
5. applicable publication policy has not identified a disqualifying axiom or unsafe escape.

## 11.2 Disproved source claim

A source claim is derived as disproved only if there exists a fidelity-verified formalization and an authoritative checked refutation of that exact formalization.

## 11.3 Conditional result

A conditional theorem is represented as its own claim with explicit assumptions. It must not silently promote the unconditional source claim.

## 11.4 Ambiguity and repair

If a source statement is ambiguous, incompatible formalization variants remain separate and the source claim remains ambiguous until review selects or refines the intended meaning.

A repaired claim is a new claim linked to the original with explicit strengthening, weakening, or repair edges.

---

# 12. Source and claim intake

## 12.1 Intake sequence

Every new source statement follows this sequence:

1. record source and licensing;
2. preserve original text without silent correction;
3. extract one or more candidate claims;
4. normalize variables, assumptions, quantifiers, and scope;
5. classify logical shape;
6. identify concepts;
7. search exact and near duplicate claims;
8. search formal declarations;
9. search cited and relevant literature;
10. propose formalization variants;
11. record unresolved ambiguity.

## 12.2 Statement normalization

Normalization must not alter mathematical meaning without creating a new version and documenting the change.

The system must explicitly detect and preserve issues such as:

- missing quantifiers;
- hidden domain assumptions;
- undefined terminology;
- overloaded notation;
- finite versus infinite scope;
- asymptotic versus pointwise claims;
- existence versus construction;
- equality versus isomorphism;
- exact versus approximate numerical claims;
- theorem versus heuristic;
- source terminology conflicts.

---

# 13. Formalization and fidelity

## 13.1 Multiple formalizations

The engine must support multiple formalizations of one source claim, including:

- weak and strong versions;
- finite and asymptotic versions;
- classical and constructive versions;
- alternate representations;
- exact source-paper definitions and simplified explanatory models;
- benchmark-aligned targets.

## 13.2 Fidelity review levels

A fidelity review must state what was reviewed:

```text
surface_syntax
mathematical_statement
definition_mapping
source_paper_correspondence
benchmark_hash_alignment
expert_domain_review
```

A simplified model may be valuable, but it must not be labeled as the exact source theorem unless the bridge is reviewed.

## 13.3 Role separation

The authoring agent may attest to a formalization, but verified fidelity requires a role-separated review record. The reviewer may be a human or an explicitly authorized independent review process, but not the same unreviewed model output that authored the statement.

## 13.4 Statement change invalidation

Any change to the declaration type, assumptions, imports that alter notation or definitions, universes, or referenced definition bodies creates a new formalization version. Existing fidelity and proof evidence remains attached to the old version.

---

# 14. Counterexample-first investigation

The engine must not assume every claim should be proved.

## 14.1 Triage order

Before expensive proof search:

1. inspect trivial and boundary cases;
2. inspect empty, zero, one, and minimal-size cases;
3. query known counterexamples;
4. search bounded instances where meaningful;
5. compare to stronger and weaker known claims;
6. attempt proof and disproof in parallel when justified.

## 14.2 Logical asymmetry

For a universal claim `∀ x, P x`, one verified witness satisfying `¬ P x` disproves it.

For an existential claim `∃ x, P x`, one verified witness proves it.

Failure to find a witness or counterexample is empirical evidence only.

## 14.3 Counterexample package

A promoted counterexample contains:

- exact witness;
- exact formalization refuted;
- formal or deterministic checker;
- verification evidence;
- minimization evidence where useful;
- explanation of the failing assumption;
- proposed repaired claims;
- provenance to the source and search run.

## 14.4 Statement repair

Repair operations include:

- add a missing hypothesis;
- exclude a boundary case;
- weaken a conclusion;
- restrict a domain;
- change pointwise to asymptotic;
- split into cases;
- replace equality with an appropriate equivalence or isomorphism.

Repairs create new claim versions or new claims. They never silently edit the original.

---

# 15. Research runs and branch value

## 15.1 Core proof actions

Proof-oriented runs support:

```text
Solve
SubmitModule
Decompose
GiveUp
```

These are execution actions, not global ontology types.

## 15.2 Run-local obligations

Tactical obligations remain local to a run unless explicitly promoted.

Promotion to a canonical claim requires:

- a stable statement;
- a useful name;
- verified evidence;
- duplicate search;
- dependency record;
- declared reuse or publication value.

This prevents tactical subgoals from flooding the global graph.

## 15.3 Branch-value policy

A research branch must eventually produce at least one of:

1. verified theorem;
2. verified counterexample;
3. corrected statement;
4. proved obstruction;
5. reusable infrastructure;
6. sharper frontier obligation;
7. evidence that materially changes prioritization.

A branch that repeatedly produces none of these is frozen, not deleted. The freeze record states why the branch was stopped and what would justify reopening it.

## 15.4 Failed attempts

Failed attempts are preserved with:

- exact input;
- action type;
- generated artifact;
- verifier diagnostics;
- environment;
- failure classification;
- repair link where one exists;
- redaction and training status.

Repeated identical failures should be deduplicated while preserving occurrence counts and contexts.

---

# 16. Verification and proof authority

## 16.1 Lean 4 scope

Lean 4 is the only authoritative formal backend required for `1.0.0`.

The internal verifier interface may be narrow enough to support future certificate adapters, but no second proof assistant or generic plugin framework is implemented before release.

## 16.2 Authoritative evidence

Accepted authoritative evidence includes:

- Lean kernel-checked theorem;
- Lean kernel-checked refutation;
- kernel re-evaluation of finite `decide` proofs;
- deterministic certificate replay through an explicitly reviewed adapter;
- Comparator verification for publication packages.

Raw solver verdicts and ordinary program output are not authoritative.

## 16.3 Hole and unsafe policy

An authoritative proof closure must reject or explicitly quarantine:

- `sorry`;
- `admit`;
- `sorryAx`;
- undeclared custom axioms;
- `unsafe` proof escapes;
- `extern` or `implemented_by` in the proof authority path;
- `native_decide` as proof authority unless a future approved policy provides an independently replayable trust story.

An intentional `sorry` may exist in an isolated `Challenge.lean`, provided it is excluded from the solved proof closure and the release clearly marks it as the challenge statement.

## 16.4 Axiom audit

Publication evidence must record the transitive axiom surface of headline declarations. Expected standard axioms may be allowlisted by policy. Unexpected axioms fail publication.

## 16.5 Local and publication trust profiles

### Local development profile

- runs on the user's supported host, including Windows;
- uses temporary directories, sanitized environment variables, path containment, timeouts, and resource limits where available;
- reports honestly that this is not a hardened virtualization boundary.

### Publication CI profile

- runs from a clean checkout on a fresh GitHub-hosted Linux runner;
- installs pinned toolchains;
- disables unneeded network access during verification where practical;
- rebuilds all required modules;
- performs hole, unsafe, dependency, and axiom audits;
- optionally runs Comparator;
- retains logs and reports as release evidence.

The system must report which profile produced each evidence record.

## 16.6 Replay

Replay re-executes recorded typed actions and verifies event-chain integrity.

Replay may establish:

- trajectory integrity;
- reproducibility of submitted proof actions;
- consistency with the pinned environment.

Replay does not establish:

- statement fidelity;
- novelty;
- scientific importance;
- correctness of an informal explanation;
- correctness of an external source.

---

# 17. Search and context compilation

## 17.1 Required search modes

`1.0.0` supports:

- stable ID lookup;
- version hash lookup;
- artifact hash lookup;
- declaration-name lookup;
- formal-statement hash lookup;
- full-text search using FTS5;
- graph traversal;
- concept filtering;
- environment-aware Lean declaration lookup;
- prior-failure search.

No vector database is required.

## 17.2 Search before construction

Before creating a definition, theorem, proof pattern, or repair, the agent must search:

1. the canonical store;
2. the active formal environment;
3. full Mathlib where configured;
4. relevant external libraries such as Statlib;
5. prior failed and successful campaign artifacts.

The software should make this the easiest path through context and API design. Prompt reminders are not sufficient.

## 17.3 Deterministic context compiler

The engine compiles the smallest useful context from:

- active claim and formalization;
- open obligations;
- direct logical dependencies;
- relevant concept definitions;
- source excerpts;
- top declaration-search results;
- deduplicated failure patterns;
- recently accepted artifacts;
- explicit trust boundary;
- remaining budget.

Excluded by default:

- full conversation histories;
- unrelated successful proofs;
- repeated diagnostics;
- generated certificate bodies;
- private chain-of-thought;
- superseded formalizations.

Every included context item carries an object ID and version hash.

---

# 18. Machine-readable pedagogy

## 18.1 Pedagogy is not decoration

Pedagogy is a first-class product output and has its own graph. It is not generated prose appended after proof completion.

## 18.2 Required learning-unit fields

Each learning unit includes:

- target concept or claim;
- audience track;
- entry assumptions;
- learning objectives;
- hard prerequisites;
- soft prerequisites;
- grounded references;
- explanation artifact;
- examples;
- nonexamples;
- counterexamples;
- misconceptions;
- exercises;
- mastery checks;
- formal references;
- applications;
- frontier references;
- review and training status.

## 18.3 First-principles-to-frontier path

A complete concept path may contain:

```text
motivation
→ vocabulary
→ definitions
→ representations
→ examples and nonexamples
→ computational intuition
→ standard theorems
→ proof techniques
→ verified formal artifacts
→ applications
→ limitations
→ open questions
→ current research frontier
```

## 18.4 Separate dependency meanings

A pedagogical prerequisite does not imply logical theorem dependence.

The system must support:

- a theorem that logically depends on advanced machinery but is taught first through examples;
- a concept that is pedagogically useful before its formal foundations;
- multiple curriculum paths for the same concept.

## 18.5 External taxonomies

External taxonomies such as Marble are represented with stable crosswalk records and source licenses.

They are not silently imported as the canonical ontology. Copying licensed content requires an explicit partition, attribution, and export policy.

---

# 19. Corpus, RL, and evaluation exports

## 19.1 Canonical state versus projection

The canonical store contains mathematics, evidence, provenance, and pedagogy. Training datasets are deterministic projections from frozen releases.

Training records never become the source of truth.

## 19.2 Required task families

The release exporter supports at least:

| Task family | Input | Target |
|---|---|---|
| Formalization | source claim | faithful formal statement |
| Fidelity selection | source plus variants | reviewed matching variant |
| Counterexample | universal claim | verified witness |
| Statement repair | false claim plus witness | corrected claim |
| Declaration retrieval | obligation | relevant library declaration |
| Decomposition | formal target | productive obligations |
| Proof generation | obligation | kernel-accepted proof |
| Proof repair | failed proof plus diagnostics | repaired proof |
| Generalization | specific theorem | reusable theorem |
| Explanation | formal artifact plus audience | grounded explanation |
| Curriculum ordering | concept set | prerequisite graph |
| Frontier selection | research graph | justified next obligation |

## 19.3 Training records

Training records may include:

- exact task input;
- structured actions;
- verifier diagnostics;
- accepted artifacts;
- rejected attempts;
- repair trajectories;
- trust labels;
- provenance;
- cost and model metadata;
- licenses and restrictions.

Private model chain-of-thought is not required and must not be treated as proof evidence.

## 19.4 Leakage controls

Train, validation, public test, and held-out evaluation splits must account for:

- theorem dependency components;
- equivalent formalizations;
- shared source papers;
- generated certificate families;
- common proof variants;
- benchmark identity;
- time of publication.

Random row-level splitting is not acceptable for serious evaluation.

## 19.5 MathCorpus and MCIP

The product exports versioned MathCorpus-compatible packets and MCIP evidence bundles.

MathCorpus remains a curated publication and learning layer. It is not a runtime dependency of the engine or of downstream mathematical libraries.

---

# 20. Portable releases

## 20.1 Release contents

A release bundle contains at minimum:

```text
manifest.json
objects/
edges/
evidence/
artifacts/
environments/
licenses/
replay/
reports/
exports/
```

For a published formal theorem, the bundle includes:

- original source and citations;
- normalized claim;
- exact formalization;
- Lean source;
- dependency manifest;
- environment manifest;
- proof evidence;
- hole and unsafe scan;
- axiom report;
- clean-build report;
- fidelity review;
- provenance and authorship disclosure;
- logical graph;
- pedagogy graph where applicable;
- redaction and training status;
- exact replay commands.

## 20.2 Portability acceptance test

The release test must:

1. build a release;
2. copy it to a clean temporary location;
3. remove or hide the operational database;
4. verify all hashes;
5. rebuild or replay the authoritative artifacts;
6. confirm the same release manifest hash.

A release that cannot pass this test is invalid.

## 20.3 Comparator package

For selected capstone proofs, the release builder supports:

```text
Challenge.lean
Solution.lean
config.json
formalization.yaml
verification.json
```

Comparator status becomes stale when the challenge, solution, dependency manifest, theorem source, or Comparator configuration changes.

---

# 21. Agent-facing API

The public MCP surface must stay small. Internally, modules may have more functions.

The recommended tool families are:

```text
system
query
source
claim
formalization
research
verify
pedagogy
release
```

Each family uses a discriminated `action` enum.

## 21.1 System

```text
describe
health
capabilities
policy
doctor
```

## 21.2 Query

```text
search
get
graph
context
declaration_lookup
failure_search
```

## 21.3 Source

```text
propose
version
cite
attach_artifact
```

## 21.4 Claim

```text
propose
normalize
version
relate
repair
review_fidelity
```

## 21.5 Formalization

```text
propose
elaborate
version
attach_environment
compare
```

## 21.6 Research

```text
start
observe
lease
submit
freeze
close
```

Proof submissions use typed `Solve`, `SubmitModule`, `Decompose`, and `GiveUp` variants.

## 21.7 Verify

```text
check
status
replay
audit
clean_build
```

## 21.8 Pedagogy

```text
propose
link
validate
review
path
```

## 21.9 Release

```text
preview
build
verify
publish_metadata
export
```

There is no `mark_proved`, `mark_certified`, raw shell, raw SQL, or unrestricted file-write action.

---

# 22. CLI contract

The same application layer used by MCP must be accessible through CLI commands.

Required commands include:

```text
mcl init
mcl doctor
mcl serve
mcl source ...
mcl claim ...
mcl formalization ...
mcl research ...
mcl verify ...
mcl pedagogy ...
mcl release ...
mcl search ...
mcl import ...
mcl migrate ...
```

All mutating commands support:

- `--dry-run` where meaningful;
- machine-readable JSON output;
- idempotency keys;
- explicit actor/run attribution;
- nonzero exit status on validation failure.

The CLI must never implement a separate domain path from MCP.

---

# 23. Jobs, concurrency, and crash recovery

## 23.1 Durable jobs

Long operations use a SQLite-backed jobs table with:

- stable job ID;
- job type;
- canonical input hash;
- state;
- priority;
- lease owner;
- lease expiration;
- attempt count;
- progress summary;
- result artifact;
- last error;
- timestamps.

## 23.2 Job states

```text
queued
leased
running
succeeded
failed
cancelled
blocked
```

Expired leases return jobs to the queue unless the operation is known to have committed an idempotent result.

## 23.3 Concurrency targets

`1.0.0` must support:

- at least 25 concurrent metadata and search clients;
- at least 100 queued investigations;
- configurable verifier concurrency;
- local default verifier concurrency of one;
- deterministic conflict handling for concurrent canonical writes.

The product does not claim that one workstation can run 100 Lean kernels simultaneously.

## 23.4 Compare-and-swap

Mutations that depend on a current object version require the expected head hash. If the head changed, the mutation fails with a structured conflict and does not overwrite newer work.

## 23.5 Idempotency

Verifier, import, release, and canonical mutation requests accept an idempotency key. Retrying a completed request returns the existing result.

---

# 24. Security and trust boundaries

## 24.1 External model boundary

The core contains:

- no provider SDKs;
- no model API keys;
- no model routing;
- no streaming inference loop;
- no provider retry logic.

The external host is the policy. The engine is the environment and verifier-backed state machine.

## 24.2 Filesystem boundary

- All working paths are under configured roots.
- Canonicalization occurs before access checks.
- Symlink and path traversal escapes are rejected.
- Verifier output is copied into CAS only after validation and hashing.
- Archive extraction enforces file-count, path, and size limits.

## 24.3 Process boundary

Verifier commands are allowlisted and assembled from typed inputs. The agent cannot supply arbitrary executable names or shell fragments.

## 24.4 Network boundary

Authoritative verification runs without network access where the platform permits. Required dependencies are fetched before the verification phase and pinned by hash or revision.

## 24.5 Resource boundary

Every long-running operation has:

- wall-clock timeout;
- output-size limit;
- memory profile or documented platform limitation;
- cancellation support;
- cleanup procedure;
- structured timeout or resource-exhaustion result.

## 24.6 Secrets

The engine must work without secrets. CI credentials used for release publication are supplied by the hosting platform and are unavailable to verifier subprocesses.

---

# 25. Observability and operations

## 25.1 Structured logs

Every log record includes:

- timestamp;
- level;
- operation;
- request or run ID;
- object IDs and version hashes where safe;
- duration;
- result classification;
- error code.

Proof bodies and restricted source text are not logged by default.

## 25.2 Health and doctor

`mcl doctor` checks:

- database access and migrations;
- artifact-store read/write integrity;
- Lean toolchain availability;
- configured environment manifests;
- schema consistency;
- FTS indexes;
- stale leases;
- release prerequisites;
- disk-space warnings.

## 25.3 Backups

The product documents and tests backup and restore for:

- SQLite database;
- artifact store;
- configuration;
- release bundles.

A backup is not considered valid until a restore test succeeds.

## 25.4 Error design

All public errors have:

- stable code;
- human-readable message;
- retryability classification;
- affected object and version where safe;
- suggested corrective action.

Do not expose raw internal stack traces as the only error surface.

---

# 26. Migration from existing proof search

The redesign must preserve prior work without inheriting the old ontology as the new architecture.

## 26.1 Migration mapping

| Existing object | New destination |
|---|---|
| problem version | claim plus formalization |
| source statement | source plus claim version |
| root formal statement | formalization version |
| episode | run |
| trajectory event | run event |
| obligation | run-local obligation or promoted claim |
| verification layer | evidence |
| formalization plan | research-plan artifact |
| research dossier | collection and typed graph |
| candidate construction | artifact plus empirical evidence |
| empirical search | investigation run |
| reasoning log | non-authoritative run event |
| proof export | release input |
| MCIP bundle | portable evidence interchange |
| MathCorpus packet | curated release projection |

## 26.2 Non-promoting import

Migration must not upgrade trust.

An imported artifact retains its existing fidelity, proof, publication, and training state unless new evidence is produced under the new system.

## 26.3 Preservation requirements

Preserve:

- original identifiers;
- timestamps;
- statement hashes;
- environment hashes;
- proof bodies;
- diagnostics;
- negative histories;
- event hashes;
- replay instructions;
- redaction state;
- attribution.

## 26.4 Compatibility period

The legacy server may remain read-only and replay-compatible during migration. New canonical writes must use the new domain core after the cutover milestone.

---

# 27. Test strategy

Testing is a product feature.

## 27.1 Unit tests

Cover:

- canonical serialization;
- content hashing;
- state derivation;
- policy decisions;
- edge validation;
- license and redaction gates;
- path validation;
- environment hashes;
- status staleness.

## 27.2 Property tests

Cover:

- canonical JSON determinism;
- hash stability;
- version immutability;
- idempotency;
- event-chain integrity;
- graph cycle rules;
- release manifest closure.

## 27.3 Integration tests

Cover:

- CLI and MCP using the same application path;
- claim-to-formalization lifecycle;
- counterexample and repair lifecycle;
- proof verification;
- crash and restart during jobs;
- concurrent CAS conflict;
- legacy import;
- release build and replay.

## 27.4 Adversarial tests

The suite must include at least these cases:

| Test | Expected result |
|---|---|
| Agent submits `sorry` | authoritative verification fails |
| Agent attempts to set `proved` | impossible by API |
| Agent proves a weakened theorem | formalization passes; source claim stays unresolved |
| Agent changes one hypothesis | new formalization version; old evidence does not apply |
| Two agents write from same head | one succeeds; one receives conflict |
| Database is removed after release | release still verifies |
| Counterexample search finds nothing | claim remains open |
| Counterexample witness is invalid | refutation rejected |
| Duplicate theorem is proposed | existing match is surfaced |
| Dependency is unpinned | publication fails |
| Custom axiom appears | publication fails unless explicitly allowed by policy |
| Restricted proof body is exported | public export fails closed |
| Artifact changes by one byte | artifact and release hashes change |
| Pedagogy hard edge creates a cycle | commit rejected |
| Citation lacks source metadata | literature evidence rejected |
| Novelty search finds no match | status remains candidate, not established novelty |
| Challenge changes after Comparator | Comparator status becomes stale |
| Agent exceeds budget | run pauses or closes without state corruption |
| Path traversal is attempted | request rejected |
| Process crashes after artifact write before DB commit | orphan handling is deterministic and safe |

## 27.5 Golden fixtures

Golden fixtures pin:

- canonical JSON;
- object hashes;
- environment hashes;
- release manifests;
- representative CLI and MCP JSON responses;
- migration outputs.

## 27.6 No coverage theater

A numeric line-coverage threshold is not a substitute for behavioral coverage. Critical state transitions, trust rules, migrations, and release paths require explicit tests even if aggregate coverage is high.

---

# 28. Continuous integration

Every pull request runs:

```text
format check
lint with warnings denied
unit tests
property tests
integration tests
schema consistency check
migration forward test
migration restore test
security and path tests
fixture hash check
release smoke test
```

Changes touching Lean verification, formal schemas, or release logic also run the Lean integration suite.

The protected release workflow runs:

- clean checkout;
- pinned dependency installation;
- all tests;
- all four product pilots;
- hole and unsafe scan;
- axiom audits;
- release build;
- database-independent release replay;
- public export redaction audit;
- artifact and manifest retention.

A green CI badge alone is not the Definition of Done. It is one required control.

---

# 29. Four mandatory product pilots

The product is not release-ready until all four pilots pass through the real architecture.

## 29.1 Pilot A: elementary false statement

Statement:

> Every prime number is odd.

Required behavior:

1. ingest source;
2. normalize universal claim;
3. formalize exact claim;
4. find witness `2`;
5. verify the refutation;
6. derive `disproved`;
7. propose repaired claim excluding `2`;
8. review fidelity;
9. prove repaired claim;
10. create explanation, counterexample, misconception, and exercise;
11. export release and RL tasks.

## 29.2 Pilot B: textbook theorem

Statement:

\[
1 + 3 + \cdots + (2n-1) = n^2.
\]

Required behavior:

1. source and concept graph;
2. formalization;
3. at least two verified proof variants;
4. promotion of useful intermediate results;
5. logical dependencies;
6. pedagogical prerequisites;
7. worked proof and exercises;
8. release and RL export.

## 29.3 Pilot C: research formalization

Use the BH formalization.

Required behavior:

1. ingest paper and repository sources;
2. represent exact headline claim;
3. import or rebuild formalization and certificate evidence;
4. preserve generated certificate provenance;
5. distinguish reusable statistics from paper-specific data;
6. run clean verification and audits;
7. produce publication package;
8. emit MathCorpus and MCIP records;
9. verify release without the source database.

## 29.4 Pilot D: open frontier campaign

Use Erdős problem 647.

Required behavior:

1. import known results, formalizations, failures, and open obligations;
2. separate known mathematics, new formalization, and novelty candidates;
3. preserve negative routes and method obstructions;
4. index reusable intermediate lemmas;
5. derive honest open status;
6. build a living first-principles-to-frontier pedagogy path;
7. freeze a portable checkpoint;
8. generate frontier-selection and proof-repair tasks without claiming the problem solved.

---

# 30. Definition of Done for `1.0.0`

The product is complete only when every item below is satisfied.

## 30.1 Installation and operation

- A clean checkout builds using documented commands on the supported Windows development environment and Linux CI.
- `mcl init` creates a working local instance.
- `mcl doctor` reports a healthy installation.
- MCP and CLI operate over the same canonical service layer.
- Process restart preserves all committed state and resumes or safely requeues durable jobs.

## 30.2 Core lifecycle

- Sources, concepts, claims, formalizations, artifacts, evidence, edges, runs, learning units, environments, and releases are fully implemented.
- Multiple formalizations per claim work end to end.
- Fidelity review works end to end.
- Counterexample, repair, proof, disproof, and open outcomes work end to end.
- Truth status is derived and cannot be directly mutated.
- Verified intermediate results can be promoted and searched.

## 30.3 Verification

- Lean verification uses pinned environments.
- Authoritative proof and refutation evidence is recorded against exact formalization versions.
- Hole, unsafe, and axiom policies are enforced.
- Replay works and reports its exact trust boundary.
- Publication CI produces retained evidence.

## 30.4 Search and context

- Exact, FTS, graph, declaration, and failure searches work.
- Context compilation is deterministic and provenance-bearing.
- Agents outside the originating campaign can locate and reuse verified results.

## 30.5 Pedagogy

- Hard and soft prerequisites are distinct.
- Learning units support explanations, examples, counterexamples, misconceptions, exercises, mastery checks, and frontier notes.
- Curriculum paths can be queried.
- External taxonomy crosswalks preserve source and license.

## 30.6 Releases and exports

- Release bundles are complete, hashed, licensed, and policy-checked.
- Releases verify without the operational database.
- MathCorpus and MCIP export works.
- RL and evaluation exports work with leakage-aware splits.
- Public exports fail closed on restricted or incomplete provenance.

## 30.7 Migration

- Legacy proof-search evidence imports without silent trust promotion.
- Original IDs, hashes, histories, and negative attempts are preserved.
- The four pilot fixtures are represented in the new architecture.

## 30.8 Quality and operations

- All CI checks pass.
- All adversarial tests pass.
- Backup and restore is tested.
- Migrations are documented and tested.
- Structured errors and logs are implemented.
- No placeholder handlers exist on required paths.
- No critical-path TODO, FIXME, panic-only behavior, or undocumented manual database edit remains.
- User, operator, trust, data-format, and contributor documentation is complete.
- A release candidate is built, replayed, and tagged `1.0.0`.

The agent must not declare completion before this checklist is mechanically and manually reviewed.

---

# 31. Implementation order

Implement in this order unless a defect requires reprioritization.

## Phase 1: Governance and executable skeleton

Deliver:

- root specification;
- ADR framework;
- implementation ledger;
- one real binary;
- configuration loader;
- SQLite migrations;
- artifact directory;
- health and doctor commands;
- CI baseline.

The binary must already use the real database and artifact store. No mock architecture.

## Phase 2: Canonical records and trace

Deliver:

- immutable records and versions;
- canonical JSON;
- hashes;
- typed edges;
- artifacts;
- runs and event chains;
- exact and FTS search;
- CLI and MCP shared path.

## Phase 3: Formalization and Lean authority

Deliver:

- environment manifests;
- formalization records;
- Lean elaboration;
- proof and refutation checking;
- verifier jobs;
- replay;
- audits;
- derived truth status.

Complete Pilot A.

## Phase 4: Research execution

Deliver:

- run actions;
- obligations;
- leases;
- CAS;
- counterexample search records;
- statement repair;
- failure and repair search;
- branch freeze;
- intermediate result promotion.

Complete Pilot B.

## Phase 5: Pedagogy

Deliver:

- learning units;
- pedagogy graph;
- prerequisite validation;
- curriculum queries;
- external crosswalks.

## Phase 6: Release, corpus, and RL

Deliver:

- portable release;
- clean replay;
- policy gates;
- MathCorpus and MCIP export;
- RL task export;
- leakage-aware splits;
- Comparator package support.

Complete Pilot C.

## Phase 7: Legacy migration and frontier operation

Deliver:

- legacy importer;
- non-promoting migration;
- large campaign search and context;
- frontier checkpoint support.

Complete Pilot D and the full Definition of Done.

---

# 32. Required repository memory

The repository is the durable memory of implementation.

The agent must maintain:

## `docs/implementation/STATUS.md`

Contains:

- current phase;
- completed acceptance criteria with evidence;
- active issue;
- next highest-priority criteria;
- exact last validation commands;
- current release readiness.

## `docs/implementation/BLOCKERS.md`

Contains only real blockers with:

- description;
- impact;
- attempts;
- smallest required decision;
- unblocked work that continues.

## `docs/implementation/RELEASE_CHECKLIST.md`

Mirrors the Definition of Done and links each item to tests, commands, reports, or artifacts.

## `docs/decisions/ADR-*.md`

Required for decisions that:

- change architecture;
- add infrastructure;
- change trust policy;
- change schema semantics;
- change release compatibility;
- create a new security boundary.

## GitHub issues

Every nontrivial change is attached to an issue with acceptance criteria. One issue should correspond to one coherent deliverable, not an indefinite theme.

---

# 33. Commit and review discipline

## 33.1 Before editing

- inspect relevant source;
- search for existing implementation;
- read active ADRs;
- confirm issue acceptance criteria;
- identify applicable trust and migration impact.

## 33.2 Before commit

Run the relevant subset, and normally all, of:

```text
cargo fmt --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace
schema consistency checks
migration tests
integration tests
mcl doctor
pilot or release smoke tests
```

Record exact commands and outcomes in the issue or implementation ledger.

## 33.3 Commit shape

- One coherent change per commit.
- No unrelated cleanup mixed with functional changes.
- Commit message states the product outcome, not merely the file operation.
- Generated files are reproducible and documented.
- No force push to shared protected branches.

## 33.4 Self-review

Before commit, answer:

1. What untrusted proposal can reach this code?
2. What decides whether it becomes canonical state?
3. Is the control stronger than a prompt instruction?
4. Can a retry duplicate or corrupt state?
5. Can this result be reproduced without hidden local state?
6. Does the change weaken statement fidelity, proof authority, privacy, or licensing?
7. Is there a simpler design that preserves the invariants?
8. Are tests checking behavior rather than merely implementation detail?

---

# 34. Prohibited shortcuts and anti-patterns

The agent must not:

- create a direct `proved` boolean;
- treat the current episode as the canonical theorem record;
- store only hashes that cannot be resolved outside the database;
- conflate source text with formal statements;
- conflate proof verification with fidelity review;
- claim novelty from a failed search;
- call empirical evidence proof;
- hide failures by deleting runs;
- use theorem count as the primary progress metric;
- create one MCP tool per database table;
- add microservices or a graph database preemptively;
- build a vector search stack before exact and FTS search are measured;
- expose arbitrary shell access;
- trust generated certificate data without a checked bridge;
- make MathCorpus or proof search a dependency of canonical downstream libraries;
- import external taxonomy content without license and semantic review;
- stop with a demo while the Definition of Done remains open;
- label a missing feature "future work" when it is required by this spec;
- paper over a blocker with a mock in the production path;
- silently alter the meaning of a formalized theorem during refactoring;
- claim local process isolation is stronger than the operating system actually provides.

---

# 35. Release governance

## 35.1 Versioning

- Product versions follow Semantic Versioning.
- Record and release schemas carry explicit versions.
- Breaking schema or public API changes require migration and release notes.
- Release manifests are immutable.

## 35.2 Corrections and retractions

Published errors are corrected through new versions and explicit supersession or retraction records. Released artifacts are not silently replaced.

## 35.3 Authorship and AI disclosure

Releases distinguish:

- mathematical source authors;
- formal statement authors;
- proof authors or generating systems;
- reviewers;
- verifier authority;
- deterministic generators;
- human and model contributions;
- literature lineage.

## 35.4 Licensing

Every exported object has a resolved license or explicit restriction. Unknown or incompatible licensing blocks public export.

---

# 36. Product acceptance command

The repository must eventually provide one command that performs the complete release acceptance suite from a clean checkout, for example:

```text
mcl acceptance --all --clean
```

The command must:

1. initialize a fresh instance;
2. run migrations;
3. run all tests and audits;
4. execute the four pilots through real interfaces;
5. build portable releases;
6. remove the operational database used for each release;
7. replay and verify each bundle;
8. generate MathCorpus, MCIP, RL, and evaluation exports;
9. produce a signed or hashed acceptance report;
10. exit nonzero on any unmet requirement.

The exact command name may differ. The capability may not.

---

# 37. Final agent instruction

Build the complete product described here.

Do not optimize for a compelling demo. Optimize for a system whose claims can be trusted, whose failures remain visible, whose releases survive the originating machine, whose pedagogy is machine-readable, and whose data can train future mathematical agents without confusing model output with mathematical authority.

Work in small, controlled, tested commits. Keep the architecture deliberately simple. Preserve every important trust boundary. Continue the implementation loop until the complete Definition of Done passes.

> AI proposes. Systems validate. Commits are controlled. The trace remembers.


# Constructiveness Profile (Normative)

Every formalization MUST carry an independent constructiveness profile.

The implementation SHALL distinguish:

1. Proof-construction process (agents, proof search, decomposition, replay).
2. Logical constructiveness of the final verified proof.

The first NEVER determines the second.

Required metadata:

- logic_profile: constructive | classical | mixed
- uses_classical_choice
- uses_excluded_middle
- uses_propext
- axiom_report_hash
- witness_kind:
  - none
  - explicit_witness
  - algorithm
  - finite_certificate
  - counterexample
- algorithm_extractable
- certificate_backed
- counterexample_constructive
- review_status

These fields SHALL be derived from verifier evidence whenever possible.

The engine SHOULD support queries such as:

- Show only fully constructive proofs.
- Find classical proofs with executable witnesses.
- Find proofs using Classical.choice.
- Find constructive counterexamples.
- Find certificate-backed but nonconstructive proofs.

This metadata SHALL be included in release bundles and MathCorpus exports.
