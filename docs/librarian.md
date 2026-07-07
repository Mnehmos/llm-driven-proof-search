# Mathlib librarian (issue #25)

Level 3's formalization-assistant layer needs more than
`lean_declaration_lookup` — that tool answers "does this exact name resolve
under this import manifest?", which is essential but assumes the caller
already knows the exact declaration name. Real formalization work often
starts without that: an agent knows *roughly* what it needs ("something
about sums of squares") and needs help finding the actual Mathlib surface.
The librarian is that help — a search/hint system, explicitly **outside the
trusted proof transaction**.

## Trust boundary

Same principle as every other Level 3 advisory layer in this repo (proof-pattern
memory, drafts, formalization plans): **the librarian can suggest, never
decide.** A search hit or an attached librarian result:

- cannot mark anything proved
- cannot certify a source claim
- cannot mutate a problem's import manifest
- cannot silently add an import to an existing problem version

Any name the librarian surfaces still has to go through the same path every
other declaration does: `problem_create(problem_imports=[...])` to actually
extend a problem's import manifest (real-compile-checked, immutable per
problem_version), and a real Lean kernel pass to prove anything with it.
`test_librarian_suggestion_cannot_change_proof_status` verifies this the same
way this session's other advisory-layer tests do — not as a comment, but as a
byte-level snapshot of `episodes`/`episode_obligations` before and after
exercising every librarian tool, asserting no row changed.

## Data sources — what's actually implemented vs. deferred

The issue's "Data sources" section explicitly says to *start with local,
deterministic sources* and marks a prebuilt offline Mathlib index as
*optional*. This implementation takes that literally:

**Implemented:**
- **The real, pinned Mathlib source tree.** `mathlib_search_declarations`
  scans every `.lean` file under
  `<PROOFSEARCH_LEAN_PROJECT_PATH>/.lake/packages/mathlib/Mathlib/` (or the legacy
  `lake-packages/` Lake layout) for declaration names containing a
  case-insensitive substring. This is the real pinned library — not a mock,
  not a curated subset — so every hit is grounded in what the kernel would
  actually see.
- **This LLM-Driven Proof Search Environment instance's own verified artifacts.**
  `mathlib_search_local_artifacts` searches `episode_verified_lemmas` and
  `episode_verified_module_items` for declarations this exact instance has
  already proven — a "this or something like it worked before here"
  precedent, distinct from a Mathlib-library result.

**Deliberately deferred (not built this round):**
- **A precomputed/exported offline index** (the issue's
  `mathlib_librarian_export_index`). Scanning ~111MB of real Mathlib source
  takes a fraction of a second — a separately-maintained index would add
  staleness risk (drifting out of sync with the actual pinned commit)
  without a real speed benefit at this scale. If the pinned Mathlib grows
  much larger, or search moves beyond substring matching, this call should
  be revisited.
- **Type-signature search** (`mathlib_search_by_type`). Matching by type
  would need either full Lean elaboration or a structured pre-parsed
  database of every declaration's type — a much bigger lift than a name
  scan. The `type_match` confidence value is kept in the shared vocabulary
  (a client can supply it manually via
  `formalization_plan_attach_librarian_result`) but no current tool produces
  it. Scoped out honestly rather than faked.
- **A separate `mathlib_import_suggest` tool.** Every
  `mathlib_search_declarations` hit already carries its derived
  `import_module` (mechanically: a Mathlib file's path maps 1:1 to its
  import string, e.g. `Mathlib/Algebra/Group/Basic.lean` →
  `Mathlib.Algebra.Group.Basic`), so a standalone lookup-by-name-only tool
  would just be re-deriving the same thing a search result already returned.
- **Namespace-qualified name resolution.** A declaration nested in
  `namespace Foo ... end Foo` is reported by its file-local name (`bar`), not
  the fully qualified `Foo.bar` — tracking namespace nesting while scanning
  would add real parsing complexity for a scanning MVP. A caller can infer
  the qualified name from nearby `namespace`/`end` lines in the returned
  snippet's file if needed.

## What IS handled: modifiers, attributes, dotted queries

Found via this session's own end-to-end testing against the real Mathlib
checkout, not by inspection alone — worth calling out since the first pass
missed these:

- **Modifier- and attribute-prefixed declarations.** `protected theorem foo`,
  `private noncomputable def bar`, `@[simp] theorem baz` are all found and
  reported under their REAL keyword (`theorem`/`def`), not the modifier or
  attribute — confirmed to matter for roughly 80% of real Mathlib files.
  Missing this wasn't just a coverage gap: a query that should hit a
  modifier-prefixed declaration could otherwise return an unrelated
  `exact_match` elsewhere instead, a false-confidence result, not merely an
  incomplete one.
- **Dotted queries.** `Nat.factorization` (the form a declaration is
  *referenced* by, not how it's *written* in source) is matched on its last
  segment (`factorization`), since scanned names are file-local only. A
  trailing/bare dot (e.g. `"Nat."`) falls back to the original query rather
  than degrading into an empty-string match-everything scan.

## Confidence vocabulary

Every result carries one of:

| Value | Meaning | Produced by |
|---|---|---|
| `exact_match` | The name matches exactly | `mathlib_search_declarations` |
| `nearby_name` | A similarly-named declaration was found | `mathlib_search_declarations` |
| `type_match` | Matched by type signature (not by name) | *(none yet — reserved)* |
| `usage_example` | A prior local LLM-Driven Proof Search Environment artifact used this/a similar name | `mathlib_search_local_artifacts` |
| `unknown` | No useful signal | *(a client can supply this manually)* |

## Tools

- **`mathlib_search_declarations { query, limit? }`** — real-Mathlib-source
  search. Returns `mathlib_available: false` (not an error) if lean-checker
  isn't set up, so callers can distinguish "not set up here" from "genuinely
  no matches." Each hit: `declaration_name`, `keyword` (theorem/lemma/def/...),
  `import_module`, `file_relative_path`, `signature_snippet`, `confidence`.
- **`mathlib_search_local_artifacts { query, limit? }`** — searches this
  instance's own verified lemma/module-item names. Every hit is
  `confidence: "usage_example"`.
- **`formalization_plan_attach_librarian_result { plan_item_id, declaration_name, confidence, import_module?, snippet? }`**
  — attaches a librarian result to a formalization plan item (issue #10),
  updating `mathlib_coverage_status` (`exact_match` → `found`;
  `nearby_name`/`type_match`/`usage_example` → `partial`; `unknown` →
  `unknown`) — the same coverage vocabulary
  `formalization_plan_attach_lookup` already writes, so a plan item's
  coverage status reads consistently regardless of which tool populated it.
  Candidate names accumulate across multiple attached results (deduped);
  the full latest result (confidence/import/snippet) overwrites
  `lookup_result_json`, matching `formalization_plan_attach_lookup`'s
  existing "latest wins" convention on that field. Rejects attaching to a
  plan item that isn't `status = 'open'` (already promoted or dropped) —
  same guard `formalization_plan_attach_lookup` uses.

## Performance note

`mathlib_search_declarations` does a synchronous filesystem scan (no DB lock
held — it doesn't touch the database at all) rather than an async/streamed
read, matching this codebase's existing convention of calling `std::fs`
directly for filesystem checks (see `crates/proofsearch-core/src/lean/mod.rs`).
Collection is capped at 2000 raw hits internally (independent of the
caller's requested `limit`) to bound memory for a degenerate very-short
query; results are sorted (exact matches first, then by name length, then
alphabetically) before truncating to the requested limit, so a good match
found late in the scan isn't dropped in favor of a worse match found early.
