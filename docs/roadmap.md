# ChatDB capability levels and roadmap

This document defines what ChatDB currently does, what it does not yet do, and
what has to be built next — in that order, not the reverse. Each level is
defined operationally: by required artifacts, required tools, and a concrete
test of whether the level has actually been reached, not by aspiration.

**v0.3.1 is Level 2.** Everything below Level 2 is done. Level 3 and Level 4
are open issues, not shipped features — this doc exists so a PR that adds a
feature can say which level it's building toward, instead of drifting.

## Why levels, not just a feature list

A flat issue list makes every feature look equally load-bearing. It isn't.
`SubmitModule` (Level 2) had to exist before formalization planning (Level 3)
was even worth building, because a plan that can't be checked against a real
kernel is just prose. Level 4 (research workbench) needs Level 3's
formalization planning underneath it for the same reason: a research dossier
with no path to a checked module is a wiki page, not a workbench. The level
ordering is a dependency order, not a priority ranking imposed after the fact.

## The levels

### Level 0 — kernel checker

**Definition:** Lean 4 + Mathlib can check one theorem body given to it directly.

**Status:** Done (prerequisite of everything else in this repo).

**Does NOT count:** anything that isn't an actual `lake env lean` invocation
against the pinned toolchain. No self-assessment, no "looks right."

### Level 1 — audited proof episode

**Definition:** A single theorem attempt is wrapped in an episode: typed
actions (`Solve`/`Decompose`/`GiveUp`), CAS-guarded steps, hash-chained
trajectory events, replay, and reward — proof soundness and statement
fidelity tracked as independent claims (`kernel_verified` vs `certified`).

**Required artifacts:** `episodes`, `episode_obligations`,
`episode_verified_lemmas`, trajectory events, budget ledger.

**Required tools:** `problem_create`, `episode_create`, `episode_observe`,
`attempt_claim`, `episode_step` (`Solve`/`Decompose`/`GiveUp`),
`episode_status`, `episode_close`, `trajectory_export`, `episode_replay`,
`proof_export`.

**Status:** Done. This is the environment described in the original
`CHATDB_SPEC.md` two-phase-commit / hash-chain design.

**Does NOT count:** proving a theorem outside the episode/attempt state
machine (e.g. a bare Lean file with no attempt record, no CAS check, no
trajectory event) — there'd be nothing to replay or audit.

### Level 2 — small local Lean development *(current: v0.3.1)*

**Definition:** A proof attempt can be more than one theorem body — a small
local theory of helper `def`s and helper `theorem`s plus a root theorem,
assembled by the server into one namespaced module and verified as a unit,
including declarations that must forward-reference each other.

**Required artifacts:** `episode_verified_modules`,
`episode_verified_module_items`, `AssembledModule`/`AssembledItem` (see
`crates/chatdb-core/src/lean/module.rs`).

**Required tools/actions:** `SubmitModule` action
(`LeanModuleItem::Def`/`Theorem`/`MutualGroup`), staged (all-or-nothing)
verification, DB-lock-free Lean calls, `proof_export(format="lean")`
byte-for-byte replay of a verified module.

**Required schema:** immutable per-problem `import_manifest_json`/hash (real
compile-checked, not name-shape-checked).

**Required tests/playtests:** the v0.3.1 overnight module sprint (see
`docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md`) — algebraic
inequalities, structural and well-founded recursion, list predicates, and
mutual recursion, all `kernel_verified` against the real toolchain.

**Related issues:** #1, #2, #3, #4 (foundation — closed), #19 (mutual
recursion — closed), #5, #6, #7 (bridge issues, open — see below).

**Status:** Done for the core mechanic (`SubmitModule` + mutual groups +
persistence/replay/export). The three **bridge issues** (#5, #6, #7) are
still open and sit at the Level 2 → Level 3 seam:

- **#5** — a structural-math benchmark ladder for cases `native_decide`
  brute force can't handle, i.e. proof this Level 2 mechanism scales past toy
  examples.
- **#6** — module-aware statement fidelity: a module can be root-proof
  kernel-verified while helper definitions carry a prose-only bridge (integer
  encoding, bijection, domain restriction) that fidelity review has never
  looked at. This is the semantic-skeleton/backtranslation work.
- **#7** — human-readable exposition alongside verified Lean artifacts, so a
  verified module doesn't read as "a pile of correct Lean fragments" with no
  narrative.

**Does NOT count:** proving each helper as a *separate* episode/theorem with
no shared namespace or joint verification — that's still Level 1 done twice,
not a local theory.

### Level 3 — formalization assistant

**Definition:**

```text
informal problem/proof sketch
→ extracted mathematical claims
→ required definitions/concepts
→ Mathlib coverage map
→ missing lemmas
→ planned module skeletons
→ promoted obligations
```

Level 3 is translation and planning from informal math into formal
proof-development work. **It is not discovery** — it doesn't search for new
constructions or results, it structures a plan for formalizing ones a human
or external model already has in mind.

**Required artifacts (not yet built):**
- `drafts` / `draft_moves` — an explicitly untrusted informal-planning
  artifact (issue #23). A draft can never mark anything proved.
- `formalization_plans` / `formalization_plan_items` — required concepts,
  Mathlib coverage, missing definitions/lemmas, planned modules, planned
  obligations (issue #10).
- A Mathlib librarian index beyond exact-name lookup — search by
  type/namespace/usage example, always advisory (issue #25).
- `proof_patterns` / `proof_pattern_applications` — reusable repair doctrine
  mined from real attempts, always a hint, never a status change (issue #24).

**Required tools/actions (not yet built):** `draft_create`, `draft_observe`,
`draft_extract_moves`, `formalization_plan_create_from_draft`,
`formalization_plan_promote_module_skeleton`,
`formalization_plan_promote_obligations`, `mathlib_search_declarations`,
`mathlib_search_by_type`, `mathlib_import_suggest`.

**Required boundary:** every Level 3 artifact is advisory. A draft, a plan
item, a librarian hit, or a proof pattern can shape what a client tries next,
but none of them can mark an obligation proved, change fidelity status, or
affect certification — only a real Lean kernel pass can. This mirrors the
Level 2 trust boundary (model proposes, server assembles, Lean verifies) one
level up the stack: model/plan proposes, Level 3 structures, Lean still
verifies.

**Related issues:** #10, #23, #24, #25 (core), #6 (bridge, shared with Level
2 — module-aware fidelity is a prerequisite for planning around modules
honestly).

**Level 3 MVP** (in dependency order — revised from the original draft after
reading all four issue bodies closely: #24 has no dependency on drafts or
plans at all, since it hooks into data that already exists (episode
obligations, failure lessons, attempt history), so it doesn't need to come
last):
1. **#24 — Proof-pattern memory.** ✅ Shipped in v0.3.2. Fully independent of
   drafts/plans; a reusable failure_signature → recommended_repair library,
   seeded from the v0.3.1 overnight sprint, surfaced via
   `proof_pattern_search` and recorded via `proof_pattern_record_application`
   (insert-only — never touches proof/fidelity/certification status). See
   `docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md` for the
   seed provenance.
2. **#23 + #10 — Draft artifacts and formalization plans.** ✅ Shipped
   together in v0.3.3, exactly as flagged: both issues wanted to own a
   `formalization_plans`/`formalization_plan_items` schema
   (`formalization_plan_create_from_draft` vs. `formalization_plan_create`),
   so they were designed and implemented as one feature rather than two.
   `draft_create`/`draft_observe`/`draft_extract_moves` preserve informal
   reasoning and structured moves (construction, auxiliary_lemma, case_split,
   induction, reduction, bijection, counterexample_search, asymptotic_step,
   external_citation, unknown); `formalization_plan_create` (optionally
   seeded from selected draft moves)/`_observe`/`_update`/`_add_item`/
   `_attach_lookup` track planned concepts/definitions/lemmas/modules and
   their Mathlib coverage. `formalization_plan_promote_item_to_obligation`
   only records a metadata LINK to an obligation that already exists
   (created through a normal, budget-accounted `Decompose` action) — it
   never creates one itself, mirroring #24's advisory-layer boundary. The
   vestigial `episode_drafts`/`episode_formalization_candidates` tables from
   the original pre-SubmitModule spec were left untouched (still dead code,
   noted on issue #23) — this feature uses fresh `drafts`/`draft_moves`
   tables instead, since the old ones didn't fit either issue's shape.
4. #25 — Mathlib librarian (plans need real coverage data, not guesses).

**Status:** #24 shipped (v0.3.2). #23 + #10 shipped together (v0.3.3). #25 open.

**Does NOT count:** an LLM freehand-writing a formalization plan in its
response text with no ChatDB-tracked artifact, no promotion path to a
`SubmitModule` skeleton, and no record of what Mathlib coverage was actually
checked versus assumed.

### Level 4 — research workbench

**Definition:**

```text
research dossier
candidate constructions
small-case / counterexample search
external theorem / citation boundaries
multi-layer proof status
expert review artifacts
```

Level 4 is a durable workspace where serious mathematical attempts (the kind
that span days, cite external results, and need small-case computational
search before anyone commits to a proof strategy) can be searched,
structured, reviewed, and partially formalized without losing provenance.
**It is not autonomous theorem discovery** — a human or external model still
drives the search; Level 4 makes sure that search leaves a durable, honest
trail instead of disappearing into chat scrollback.

**Required artifacts (not yet built):** research dossiers (#9), candidate
construction artifacts (#8), external theorem/citation/assumption boundary
records (#11), asymptotic statement support (#12), multi-layer verification
status (#13), expert-review artifacts and a role-separated ledger (#14),
empirical math lab for small-case/counterexample/construction search (#26),
paper/PDF ingestion with citation and gap tracking (#27).

**Required boundary:** an external citation is a tracked assumption, never a
substitute for a Lean proof of the cited fact — Level 4 must make clear which
parts of a research attempt are kernel-verified versus cited versus still
open, at all times, not just at the end.

**Related issues:** #8, #9, #11, #12, #13, #14, #26, #27 (core), #7 (bridge,
shared with Level 2 — exposition matters even more once a dossier spans
citations and partial results).

**Level 4 MVP:**
1. #8 — Candidate constructions
2. #9 — Research dossiers
3. #11 — Citation boundaries
4. #26 — Empirical math lab
5. #27 — Paper ingestion

**Serious research-grade version** (beyond MVP): #12 (asymptotics), #13
(multi-layer verification), #14 (expert review).

**Status:** Not started. Fully open, and blocked on Level 3's formalization
planning existing first — a research dossier with no formalization-planning
layer underneath it has no path from "candidate construction" to "checked
module."

**Does NOT count:** a research dossier that only stores prose notes with no
link to any Lean artifact, obligation, or formalization plan item — that's a
wiki, not a workbench.

### Level 5 — discovery loop

**Definition (forward-looking, not yet scoped into issues):** the system
proposes its own candidate constructions or conjectures, not just structures
ones a human/model already brought to it, and can run many candidates through
the Level 3/4 machinery to see which survive.

**Status:** Not scoped. No issues yet. Do not start building this before
Level 3 and Level 4 are real — a discovery loop generating plans that nothing
downstream can formalize or search around is pure motion.

### Level 6 — serious math collaborator

**Definition (forward-looking):** the full loop — discovery, formalization
planning, research-workbench provenance, and expert review — operating
together on genuinely open problems (the "tackle Putnam and Erdős problems"
goal), with every claim traceable back to either a Lean kernel pass or an
explicitly tracked, reviewed external citation.

**Status:** Not scoped. This is the destination the other levels are built
toward, not a near-term milestone.

## Issue-to-level map

| Level | Core issues | Bridge issues (shared with adjacent level) |
|---|---|---|
| 1 | #1–#4 (closed) | — |
| 2 | #19 (closed) | #5, #6, #7 (open) |
| 3 | #10, #23, #24, #25 | #6 (shared with 2) |
| 4 | #8, #9, #11, #12, #13, #14, #26, #27 | #7 (shared with 2) |
| docs/roadmap | #20, #21, #22 | — |

## What this roadmap is not

This is not a commitment to build every issue listed here in order, and it is
not a substitute for reading the individual issues before starting one — each
has its own acceptance criteria and required regression tests. It exists so
that before an agent or contributor starts a Level 3 or Level 4 feature, they
can check: does the thing underneath this already exist? If Level 2's
bridge issues (#5–#7) or the Level 3 MVP order above aren't satisfied yet,
that's a sign to build the prerequisite first, not to skip ahead.
