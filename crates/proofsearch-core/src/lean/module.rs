//! Structured Lean module submissions.
//!
//! The server assembles the Lean file; the client never sends raw Lean
//! commands. This is the module-level analogue of `verify_exact`'s
//! single-theorem wrapping, and it preserves the same import / declaration-name
//! injection hardening (`valid_lean_module_path` in the MCP layer, and the
//! per-string command scan below).
//!
//! The trust boundary: a client supplies only mathematical *content* — type
//! signatures, statements, bodies, proof terms, and namespace-local names. The
//! server renders every structural keyword (`def` / `theorem`), the namespace,
//! the imports, and the server-owned `set_option`s. Anything a client string
//! could do to escape its declaration (start a new top-level command such as
//! `import`, `axiom`, `namespace`, or a sibling `theorem`) is rejected here,
//! *before* the source ever reaches Lean.

use serde::{Deserialize, Serialize};

use crate::hashing::canonical_hash;
use crate::models::action::{LeanModuleItem, ModuleTheorem, MutualMember, ProofFormat};

/// A token that must never appear (as a whole word) anywhere inside any
/// client-supplied string. Each would open a fresh top-level Lean command and so
/// let a def body or proof term inject a declaration (e.g. `axiom cheat :
/// False`) or reshape the module (`namespace`, `end`, `import`) — banned
/// ANYWHERE, not merely at the start of a line: Lean does not require a new
/// top-level command to begin on its own line, only that the preceding term is
/// syntactically complete, so `0 theorem cheat : True := trivial` on a single
/// line opens a real `theorem` command exactly as `0\n\ntheorem cheat ...`
/// does. The client submits helper declarations as their own structured items;
/// it never writes these keywords itself.
const PROHIBITED_LEADING_TOKENS: &[&str] = &[
    // structural / scope — the server owns these
    "import", "namespace", "end", "section", "open", "set_option", "attribute",
    "variable", "universe", "mutual", "deriving", "export",
    // declaration keywords — every declaration is a separate structured item
    "def", "theorem", "lemma", "example", "abbrev", "instance", "structure",
    "inductive", "class", "axiom", "opaque", "unsafe", "partial", "noncomputable",
    // declaration MODIFIERS: Lean allows these immediately before a declaration
    // keyword (`private theorem cheat : False := ...`), so a scanner that only
    // recognizes the declaration keyword itself is bypassed by prefixing one of
    // these. There is no legitimate non-declaration use of these words at the
    // start of a top-level line, so banning them outright is safe.
    "private", "protected", "local", "scoped",
    // metaprogramming / evaluation — never allowed from a client
    "macro", "macro_rules", "syntax", "elab", "notation", "initialize", "run_cmd",
    "#eval", "#check", "#print", "#reduce", "#synth",
];

/// Tokens that are forbidden *anywhere* (as whole words) in a client string,
/// not just at line start: they defeat verification (`sorry`/`admit` typecheck
/// but prove nothing — the kernel only emits a warning) or smuggle a trusted
/// construct mid-line (`axiom`, `unsafe`, `opaque`). `sorry`/`admit` are also
/// caught by the gateway's kernel-warning scan; rejecting them here fails fast
/// and keeps a soundness hole from ever reaching a staged compile.
const PROHIBITED_ANYWHERE_TOKENS: &[&str] = &[
    "sorry", "admit", "axiom", "unsafe", "opaque", "native_decide",
];

/// Why a submitted module was rejected before it could be assembled. These are
/// deterministic policy failures (no Lean invocation), distinct from a staged
/// kernel failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModulePolicyError {
    /// A declaration name is not a single namespace-local identifier.
    InvalidName { name: String, reason: String },
    /// A client string contains a construct the client is not allowed to send.
    ProhibitedConstruct { item: String, token: String, detail: String },
    /// A `MutualGroup` does not have at least two members — a group of one
    /// (or zero) has no forward-reference problem to solve and is not a
    /// legitimate use of a `mutual` block.
    InvalidMutualGroup { detail: String },
    /// The module declares the same local name twice (including the root).
    DuplicateName { name: String },
    /// The root theorem's statement does not hash-match the registered root.
    RootStatementMismatch { expected_hash: String, actual_hash: String },
    /// Issue #64: a module declaration's name occurs as a free identifier in
    /// the hash-pinned root statement. The statement hash pins the TEXT, but a
    /// free identifier in that text resolves against the module's own
    /// namespace first — so a module-local `def C := fun _ => 0` under a
    /// statement mentioning `C` would silently prove a different proposition
    /// under the same hash. Only the designated solution slot (a name ending
    /// in `_solution`, the find-the-value convention benchmark statements are
    /// registered with) may be declared by the module.
    ShadowsRootStatementIdentifier { name: String },
    /// The module is empty (no root theorem content) or otherwise malformed.
    Empty { detail: String },
    /// A hashing failure while building the manifest (should be unreachable).
    Internal(String),
}

impl std::fmt::Display for ModulePolicyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModulePolicyError::InvalidName { name, reason } =>
                write!(f, "invalid declaration name {:?}: {}", name, reason),
            ModulePolicyError::ProhibitedConstruct { item, token, detail } =>
                write!(f, "{} contains a prohibited construct {:?}: {}", item, token, detail),
            ModulePolicyError::InvalidMutualGroup { detail } =>
                write!(f, "invalid mutual group: {}", detail),
            ModulePolicyError::DuplicateName { name } =>
                write!(f, "duplicate declaration name {:?} in module", name),
            ModulePolicyError::RootStatementMismatch { expected_hash, actual_hash } =>
                write!(f, "root theorem statement hash {} does not match the registered root statement hash {}", actual_hash, expected_hash),
            ModulePolicyError::ShadowsRootStatementIdentifier { name } =>
                write!(f, "module declaration {:?} shadows a free identifier occurring in the root theorem statement — a module-local binding for a name the hash-pinned statement references could silently change what the statement means (issue #64). Only the designated solution slot (a name ending in `_solution`) may be declared by the module; reference library declarations by their qualified names or rely on the problem's registered open context instead", name),
            ModulePolicyError::Empty { detail } => write!(f, "malformed module: {}", detail),
            ModulePolicyError::Internal(m) => write!(f, "internal module-assembly error: {}", m),
        }
    }
}

/// One assembled, policy-checked declaration, with the hashes persistence and
/// replay need. `depends_on` is best-effort: the names of other items whose
/// identifier appears (as a whole word) in this item's content — normally only
/// earlier items, except for a `MutualGroup` member, which may legitimately
/// depend on a sibling declared later in the same group (that's the point of
/// the group).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AssembledItem {
    pub order: usize,
    /// "def" | "theorem" | "root_theorem"
    pub kind: String,
    pub lean_name: String,
    pub statement_or_type_hash: String,
    pub body_hash: String,
    pub depends_on: Vec<String>,
    /// `Some(group_index)` for every member of the same `MutualGroup`
    /// (0-based, unique per module), `None` for a standalone item or the root
    /// theorem. Purely informational — replay/export never key on it, since
    /// the exact source re-assembles from `module_items_json` regardless.
    pub mutual_group: Option<u32>,
}

/// A module that passed policy and was rendered to Lean source, but has not yet
/// been kernel-checked. The gateway compiles `.source` in a staged location and
/// only writes to `LeanChecker/Verified` if the whole thing passes.
#[derive(Debug, Clone)]
pub struct AssembledModule {
    /// Full Lean source: imports, server set_options, `namespace ... end`.
    pub source: String,
    /// `ProofSearch.P_<problem>`.
    pub namespace: String,
    /// SHA-256 of `source` — the exact bytes the kernel checked.
    pub module_source_hash: String,
    /// Canonical hash over the ordered `item_manifest` (kind, name, hashes) —
    /// stable across whitespace/rendering changes to `source`.
    pub declaration_manifest_hash: String,
    pub item_manifest: Vec<AssembledItem>,
    /// The sanitized root theorem's local name.
    pub root_lean_name: String,
}

/// Rejects a name that is not a single namespace-local Lean identifier. No dots
/// (a dotted name could escape the generated namespace or shadow a real Mathlib
/// declaration), no whitespace, no leading digit, and nothing that could break
/// out of the `def <name>` / `theorem <name>` position.
fn check_name(name: &str) -> Result<(), ModulePolicyError> {
    let invalid = |reason: &str| ModulePolicyError::InvalidName { name: name.to_string(), reason: reason.to_string() };
    if name.is_empty() {
        return Err(invalid("empty"));
    }
    if name.len() > 128 {
        return Err(invalid("longer than 128 characters"));
    }
    if name.contains('.') {
        return Err(invalid("must be a single namespace-local identifier — no dots (would escape the generated namespace)"));
    }
    if name == "_root_" || name.starts_with("_root_") {
        return Err(invalid("must not reference the global `_root_` namespace"));
    }
    let mut chars = name.chars();
    let first = chars.next().unwrap();
    if !(first.is_ascii_alphabetic() || first == '_') {
        return Err(invalid("must start with an ASCII letter or underscore"));
    }
    if !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'') {
        return Err(invalid("may contain only ASCII letters, digits, underscore, or prime"));
    }
    Ok(())
}

/// True if `token` occurs in `haystack` as a whole word (not as a substring of a
/// longer identifier). Word chars are Lean identifier chars.
fn contains_word(haystack: &str, token: &str) -> bool {
    let is_word = |c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '#' || c == '!' || c == '?';
    let bytes_ok = |idx: usize, len: usize| {
        let before_ok = idx == 0 || !haystack[..idx].chars().next_back().map(is_word).unwrap_or(false);
        let after = idx + len;
        let after_ok = after >= haystack.len() || !haystack[after..].chars().next().map(is_word).unwrap_or(false);
        before_ok && after_ok
    };
    let mut start = 0;
    while let Some(pos) = haystack[start..].find(token) {
        let idx = start + pos;
        if bytes_ok(idx, token.len()) {
            return true;
        }
        start = idx + 1;
        if start >= haystack.len() { break; }
    }
    false
}

/// Scans one client-supplied string for prohibited constructs. `label`
/// identifies the field for diagnostics (e.g. `def foo body`).
///
/// Every check here is position-independent — a whole-word or substring match
/// ANYWHERE in `content`, never "only at the start of a line". Lean does not
/// require a new top-level command to begin on its own line; it only requires
/// the preceding term to be syntactically complete. A scan keyed on line-start
/// position is bypassed by e.g. a def body of `0 theorem cheat : True :=
/// trivial` on a single line — Lean parses `def evil := 0` as complete, then a
/// fresh `theorem cheat : True := trivial` command, exactly as the newline-
/// separated form `0\n\ntheorem cheat ...` does. Checking anywhere, not just at
/// line-start, closes that bypass.
fn check_content(label: &str, content: &str) -> Result<(), ModulePolicyError> {
    // Whole-word bans anywhere: structural/scope keywords, declaration keywords,
    // declaration modifiers, metaprogramming commands (PROHIBITED_LEADING_TOKENS
    // — misleadingly named for a now-removed line-start-only check, kept as one
    // list since every one of these is a reserved Lean keyword with no
    // legitimate non-declaration use), plus sorry/admit/axiom/unsafe/opaque/
    // native_decide (PROHIBITED_ANYWHERE_TOKENS — silent soundness holes or
    // trusted-construct smuggling). None of these can legitimately appear as a
    // bare identifier in submitted math content (they're all reserved words),
    // so banning them outright — anywhere — costs nothing but closes the gap.
    for token in PROHIBITED_LEADING_TOKENS.iter().chain(PROHIBITED_ANYWHERE_TOKENS.iter()) {
        if contains_word(content, token) {
            return Err(ModulePolicyError::ProhibitedConstruct {
                item: label.to_string(),
                token: token.to_string(),
                detail: format!("`{}` is not permitted anywhere in a submitted module — the server owns scope/imports/declarations; submit any needed declaration as its own structured item", token),
            });
        }
    }
    // Attribute lists (`@[...]`) precede a declaration exactly like a modifier
    // does, but aren't a single fixed word, so they can't be a token-list entry
    // — banned as a literal substring anywhere in the content instead. Bare `@`
    // (explicit-argument application, e.g. `@id Nat n`) is legitimate
    // proof-term syntax and is deliberately untouched; only the 2-char `@[`
    // prefix (an attribute LIST) is banned.
    if content.contains("@[") {
        return Err(ModulePolicyError::ProhibitedConstruct {
            item: label.to_string(),
            token: "@[".to_string(),
            detail: "an attribute (`@[...]`) is not permitted anywhere in a submitted module — attributes precede declarations, and every declaration must be its own structured item".to_string(),
        });
    }
    Ok(())
}

/// Best-effort dependency detection: which of `candidate_names` appears (as a
/// whole word) in `content`.
fn detect_deps(content: &str, candidate_names: &[String]) -> Vec<String> {
    candidate_names.iter().filter(|n| contains_word(content, n)).cloned().collect()
}

/// Issue #62: an import-manifest entry may be an `open` directive instead of a
/// module path — `"open Polynomial"`, `"open scoped BigOperators"`, or
/// `"open Polynomial Real Filter"`. Upstream benchmark files (e.g.
/// PutnamBench) activate scoped notation (`ℤ[X]`, `∠`, `π`) via `open` lines,
/// and a registered statement that relies on them cannot elaborate inside the
/// assembled module namespace without that context; without it, `ℤ[X]` parses
/// as `getElem` indexing and unknown lowercase identifiers silently auto-bind
/// as implicits — the statement can elaborate to something OTHER than the
/// intended mathematics. Carrying the open context inside the import manifest
/// means the existing `import_manifest_hash` pins it for replay/result
/// cross-checks with no schema change.
///
/// Returns the canonicalized directive (single-space separated, exactly
/// `open [scoped] <Path> [<Path> ...]`) when `entry` is a valid open
/// directive, `None` otherwise. Validation is the security boundary for the
/// interpolation into Lean source: only `open`, an optional `scoped`, and
/// dotted identifier paths — no newlines, comment syntax, or command
/// separators can survive, and the RENDERED text is the canonical
/// reconstruction from parsed tokens, never the raw entry.
pub fn parse_open_directive(entry: &str) -> Option<String> {
    if entry.len() > 512 {
        return None;
    }
    let mut tokens = entry.split_whitespace();
    if tokens.next()? != "open" {
        return None;
    }
    let rest: Vec<&str> = tokens.collect();
    let (scoped, paths) = match rest.split_first() {
        Some((&"scoped", tail)) => (true, tail),
        _ => (false, &rest[..]),
    };
    if paths.is_empty() {
        return None;
    }
    let valid_namespace_path = |s: &str| {
        !s.is_empty()
            && s.len() <= 256
            && s.split('.').all(|segment| {
                !segment.is_empty()
                    && segment.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && segment.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
            })
    };
    if !paths.iter().all(|p| valid_namespace_path(p)) {
        return None;
    }
    let mut canonical = String::from("open ");
    if scoped {
        canonical.push_str("scoped ");
    }
    canonical.push_str(&paths.join(" "));
    Some(canonical)
}

/// Splits an import manifest into (module import paths, canonical `open`
/// directives), preserving order within each group. An entry that starts with
/// the word `open` but fails [`parse_open_directive`] validation is returned
/// with the IMPORTS (where it renders as a visibly broken `import open ...`
/// line and fails the compile loudly) rather than being silently dropped or
/// spliced raw into an `open` position — fail closed, fail visible.
pub fn partition_import_manifest(manifest: &[String]) -> (Vec<String>, Vec<String>) {
    let mut imports = Vec::new();
    let mut opens = Vec::new();
    for entry in manifest {
        match parse_open_directive(entry) {
            Some(canonical) => opens.push(canonical),
            None => imports.push(entry.clone()),
        }
    }
    (imports, opens)
}

/// Issue #64: the ASCII identifier tokens occurring free-standing in a root
/// statement. A token immediately preceded by `.` is a qualified-name suffix
/// or field projection (`Finset.Icc`, `p.coeff`) — a module-local declaration
/// cannot capture it, so it is excluded. Declared module names are constrained
/// to ASCII by [`check_name`], so an ASCII scan is exhaustive for the
/// shadowing check (a unicode statement token can never equal a declarable
/// name).
/// Issue #64: rejects a module in which any declaration binds a name the root
/// statement references free. Inside the generated namespace a module-local
/// declaration wins name resolution, so under a statement mentioning `C` a
/// module could define `C := fun _ => 0` and prove a different proposition
/// under the same statement hash. The single sanctioned exception is the
/// find-the-value solution slot: a name ending in `_solution` (the convention
/// benchmark statements are registered with) is exactly the identifier the
/// module is REQUIRED to supply.
///
/// This is deliberately NOT part of [`assemble_module`]: for a client-authored
/// (ad-hoc) problem the statement author IS the module author, and a root
/// statement that references the module's own helper defs (`double 2 = 4`,
/// `isEven seed = true`) is the documented, intended SubmitModule shape.
/// The capture risk exists only when the statement text comes from someone
/// else — a registered benchmark suite — so the orchestrator applies this
/// check exactly when the target statement hash matches a registered
/// benchmark problem's target hash.
pub fn check_no_root_statement_shadowing(
    module_items: &[LeanModuleItem],
    root_theorem: &ModuleTheorem,
) -> Result<(), ModulePolicyError> {
    let statement_identifiers = root_statement_identifiers(&root_theorem.statement);
    let mut check = |name: &str| -> Result<(), ModulePolicyError> {
        if statement_identifiers.contains(name) && !name.ends_with("_solution") {
            return Err(ModulePolicyError::ShadowsRootStatementIdentifier { name: name.to_string() });
        }
        Ok(())
    };
    for item in module_items {
        match item {
            LeanModuleItem::Def { name, .. } => check(name)?,
            LeanModuleItem::Theorem { name, .. } => check(name)?,
            LeanModuleItem::MutualGroup { members } => {
                for member in members {
                    match member {
                        MutualMember::Def { name, .. } => check(name)?,
                        MutualMember::Theorem { name, .. } => check(name)?,
                    }
                }
            }
        }
    }
    check(&root_theorem.name)
}

fn root_statement_identifiers(statement: &str) -> std::collections::HashSet<String> {
    let chars: Vec<char> = statement.chars().collect();
    let mut out = std::collections::HashSet::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_' || chars[i] == '\'') {
                i += 1;
            }
            let qualified_suffix = start > 0 && chars[start - 1] == '.';
            if !qualified_suffix {
                out.insert(chars[start..i].iter().collect());
            }
        } else {
            i += 1;
        }
    }
    out
}

/// Policy-checks and assembles a structured module into Lean source under
/// `problem_namespace`, with the same import manifest a single-theorem solve
/// would use. Pure and deterministic: no Lean invocation, no filesystem.
///
/// `expected_root_statement_hash` is the problem's `root_statement_hash`; the
/// root theorem's statement must canonical-hash to exactly that.
pub fn assemble_module(
    problem_namespace: &str,
    expected_root_statement_hash: &str,
    module_items: &[LeanModuleItem],
    root_theorem: &ModuleTheorem,
    import_manifest: &[String],
) -> Result<AssembledModule, ModulePolicyError> {
    // 1. Names: each valid + unique (helpers and root share one namespace).
    let mut seen_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut ordered_names: Vec<String> = Vec::new();
    let push_name = |name: &str, seen: &mut std::collections::HashSet<String>, ordered: &mut Vec<String>| -> Result<(), ModulePolicyError> {
        check_name(name)?;
        if !seen.insert(name.to_string()) {
            return Err(ModulePolicyError::DuplicateName { name: name.to_string() });
        }
        ordered.push(name.to_string());
        Ok(())
    };
    for item in module_items {
        match item {
            LeanModuleItem::Def { name, .. } => push_name(name, &mut seen_names, &mut ordered_names)?,
            LeanModuleItem::Theorem { name, .. } => push_name(name, &mut seen_names, &mut ordered_names)?,
            LeanModuleItem::MutualGroup { members } => {
                if members.len() < 2 {
                    return Err(ModulePolicyError::InvalidMutualGroup {
                        detail: format!("a mutual group needs at least 2 members, got {} — a single declaration has no forward-reference to solve, submit it as a bare `def`/`theorem` item instead", members.len()),
                    });
                }
                for member in members {
                    let name = match member {
                        MutualMember::Def { name, .. } => name,
                        MutualMember::Theorem { name, .. } => name,
                    };
                    push_name(name, &mut seen_names, &mut ordered_names)?;
                }
            }
        }
    }
    push_name(&root_theorem.name, &mut seen_names, &mut ordered_names)?;

    // 2. Root statement must hash-match the registered root — a module can never
    // silently prove a different (e.g. weakened) goal.
    let actual_root_hash = canonical_hash(&root_theorem.statement).map_err(ModulePolicyError::Internal)?;
    if actual_root_hash != expected_root_statement_hash {
        return Err(ModulePolicyError::RootStatementMismatch {
            expected_hash: expected_root_statement_hash.to_string(),
            actual_hash: actual_root_hash,
        });
    }

    if root_theorem.statement.trim().is_empty() {
        return Err(ModulePolicyError::Empty { detail: "root theorem statement is empty".to_string() });
    }
    if root_theorem.proof_term.trim().is_empty() {
        return Err(ModulePolicyError::Empty { detail: "root theorem proof_term is empty".to_string() });
    }

    // 3. Content policy on every client string.
    for (i, item) in module_items.iter().enumerate() {
        match item {
            LeanModuleItem::Def { name, type_signature, body } => {
                check_content(&format!("def `{}` (item {}) type", name, i), type_signature)?;
                check_content(&format!("def `{}` (item {}) body", name, i), body)?;
            }
            LeanModuleItem::Theorem { name, statement, proof_term } => {
                check_content(&format!("theorem `{}` (item {}) statement", name, i), statement)?;
                check_content(&format!("theorem `{}` (item {}) proof", name, i), proof_term)?;
            }
            LeanModuleItem::MutualGroup { members } => {
                for (j, member) in members.iter().enumerate() {
                    match member {
                        MutualMember::Def { name, type_signature, body } => {
                            check_content(&format!("mutual group (item {}) def `{}` (member {}) type", i, name, j), type_signature)?;
                            check_content(&format!("mutual group (item {}) def `{}` (member {}) body", i, name, j), body)?;
                        }
                        MutualMember::Theorem { name, statement, proof_term } => {
                            check_content(&format!("mutual group (item {}) theorem `{}` (member {}) statement", i, name, j), statement)?;
                            check_content(&format!("mutual group (item {}) theorem `{}` (member {}) proof", i, name, j), proof_term)?;
                        }
                    }
                }
            }
        }
    }
    check_content("root theorem statement", &root_theorem.statement)?;
    check_content("root theorem proof", &root_theorem.proof_term)?;

    // 4. Render. Imports first (ALL import lines must precede any command), then
    // server-owned set_options, then the namespace with defs, helper theorems,
    // and finally the root theorem. `open` directives carried in the manifest
    // (issue #62) are emitted just inside the namespace, mirroring where the
    // upstream benchmark file's own `open` lines sat relative to its theorem.
    let (module_imports, open_directives) = partition_import_manifest(import_manifest);
    let mut source = String::new();
    for module in &module_imports {
        source.push_str(&format!("import {}\n", module));
    }
    source.push_str("set_option linter.unusedTactic false\n");
    source.push_str("set_option linter.unreachableTactic false\n");
    // Issue #63: Mathlib's Polynomial/Real/Measure values are noncomputable,
    // so any solution `def` over them fails Lean's compiler under a plain
    // `def`. The whole module is wrapped in a `noncomputable section` (the
    // standard Mathlib idiom): it changes nothing for theorems and lets defs
    // hold noncomputable values without the client ever writing the (banned)
    // `noncomputable` keyword itself. Soundness is untouched — the kernel
    // still checks every definition and proof; only code generation is
    // skipped.
    source.push_str("noncomputable section\n");
    source.push_str(&format!("\nnamespace {}\n\n", problem_namespace));
    if !open_directives.is_empty() {
        for open_directive in &open_directives {
            source.push_str(open_directive);
            source.push('\n');
        }
        source.push('\n');
    }

    let mut item_manifest: Vec<AssembledItem> = Vec::new();
    let mut declared_so_far: Vec<String> = Vec::new();
    // A monotonic assembly-order counter, distinct from `module_items`'s own
    // index: a single `MutualGroup` item expands into several manifest rows
    // (one per member), so `order` can no longer just be the client's item
    // index — it has to be unique across every persisted row (the
    // `episode_verified_module_items` table enforces `UNIQUE(module_id,
    // item_order)`).
    let mut next_order: usize = 0;
    let mut next_mutual_group: u32 = 0;

    for item in module_items.iter() {
        match item {
            LeanModuleItem::Def { name, type_signature, body } => {
                source.push_str(&render_def(name, type_signature, body));
                item_manifest.push(AssembledItem {
                    order: next_order,
                    kind: "def".to_string(),
                    lean_name: name.clone(),
                    statement_or_type_hash: canonical_hash(&type_signature).map_err(ModulePolicyError::Internal)?,
                    body_hash: canonical_hash(&body).map_err(ModulePolicyError::Internal)?,
                    depends_on: detect_deps(&format!("{}\n{}", type_signature, body), &declared_so_far),
                    mutual_group: None,
                });
                next_order += 1;
                declared_so_far.push(name.clone());
            }
            LeanModuleItem::Theorem { name, statement, proof_term } => {
                // Helper theorems are always flattened (issue #51 scopes the
                // raw-block transport to the root proof only).
                source.push_str(&render_theorem(name, statement, proof_term, ProofFormat::FlatTacticSequence));
                item_manifest.push(AssembledItem {
                    order: next_order,
                    kind: "theorem".to_string(),
                    lean_name: name.clone(),
                    statement_or_type_hash: canonical_hash(&statement).map_err(ModulePolicyError::Internal)?,
                    body_hash: canonical_hash(&proof_term).map_err(ModulePolicyError::Internal)?,
                    depends_on: detect_deps(&format!("{}\n{}", statement, proof_term), &declared_so_far),
                    mutual_group: None,
                });
                next_order += 1;
                declared_so_far.push(name.clone());
            }
            LeanModuleItem::MutualGroup { members } => {
                // Every member of the group is declared BEFORE any member's
                // `depends_on` is computed — that's the whole point of the
                // group: `isEven` may reference `isOdd` even though `isOdd` is
                // rendered after it, because both are inside the same `mutual`
                // block and Lean resolves them together.
                let member_names: Vec<String> = members.iter().map(|m| match m {
                    MutualMember::Def { name, .. } => name.clone(),
                    MutualMember::Theorem { name, .. } => name.clone(),
                }).collect();
                let mut group_declared = declared_so_far.clone();
                group_declared.extend(member_names.iter().cloned());

                let group_index = next_mutual_group;
                next_mutual_group += 1;

                let mut group_source = String::new();
                for member in members {
                    match member {
                        MutualMember::Def { name, type_signature, body } => {
                            group_source.push_str(&render_def(name, type_signature, body));
                            item_manifest.push(AssembledItem {
                                order: next_order,
                                kind: "def".to_string(),
                                lean_name: name.clone(),
                                statement_or_type_hash: canonical_hash(&type_signature).map_err(ModulePolicyError::Internal)?,
                                body_hash: canonical_hash(&body).map_err(ModulePolicyError::Internal)?,
                                depends_on: detect_deps(&format!("{}\n{}", type_signature, body), &group_declared),
                                mutual_group: Some(group_index),
                            });
                            next_order += 1;
                        }
                        MutualMember::Theorem { name, statement, proof_term } => {
                            group_source.push_str(&render_theorem(name, statement, proof_term, ProofFormat::FlatTacticSequence));
                            item_manifest.push(AssembledItem {
                                order: next_order,
                                kind: "theorem".to_string(),
                                lean_name: name.clone(),
                                statement_or_type_hash: canonical_hash(&statement).map_err(ModulePolicyError::Internal)?,
                                body_hash: canonical_hash(&proof_term).map_err(ModulePolicyError::Internal)?,
                                depends_on: detect_deps(&format!("{}\n{}", statement, proof_term), &group_declared),
                                mutual_group: Some(group_index),
                            });
                            next_order += 1;
                        }
                    }
                }
                source.push_str("mutual\n\n");
                source.push_str(&indent(group_source.trim_end()));
                source.push_str("\n\nend\n\n");
                declared_so_far.extend(member_names);
            }
        }
    }

    // Root theorem last. Goes through the same render_theorem/normalize_and_indent
    // path every other item uses — this is raw, client-supplied leaf content
    // (the actual goal being proved), not an already-rendered structural
    // block, so it needs the same issue #41 normalization, not the old
    // blind-uniform-add indent() a prior version of this fix missed here.
    source.push_str(&render_theorem(&root_theorem.name, &root_theorem.statement, &root_theorem.proof_term, root_theorem.proof_format));
    item_manifest.push(AssembledItem {
        order: next_order,
        kind: "root_theorem".to_string(),
        lean_name: root_theorem.name.clone(),
        statement_or_type_hash: actual_root_hash.clone(),
        body_hash: canonical_hash(&root_theorem.proof_term).map_err(ModulePolicyError::Internal)?,
        depends_on: detect_deps(&format!("{}\n{}", root_theorem.statement, root_theorem.proof_term), &declared_so_far),
        mutual_group: None,
    });

    source.push_str(&format!("end {}\n", problem_namespace));
    // Closes the issue-#63 `noncomputable section` (LIFO with the namespace).
    source.push_str("end\n");

    let module_source_hash = canonical_hash(&source).map_err(ModulePolicyError::Internal)?;
    let declaration_manifest_hash = canonical_hash(&item_manifest.iter().map(|it| {
        (it.order, it.kind.clone(), it.lean_name.clone(), it.statement_or_type_hash.clone(), it.body_hash.clone())
    }).collect::<Vec<_>>()).map_err(ModulePolicyError::Internal)?;

    Ok(AssembledModule {
        source,
        namespace: problem_namespace.to_string(),
        module_source_hash,
        declaration_manifest_hash,
        item_manifest,
        root_lean_name: root_theorem.name.clone(),
    })
}

/// Renders a `def` declaration exactly as the top-level and `mutual`-group
/// paths both need it — a single shared shape so a member inside a `mutual`
/// block compiles to identical Lean as a standalone `Def` would.
fn render_def(name: &str, type_signature: &str, body: &str) -> String {
    if type_signature.trim().is_empty() {
        format!("def {} :=\n{}\n\n", name, normalize_and_indent(body))
    } else {
        format!("def {} : {} :=\n{}\n\n", name, type_signature.trim(), normalize_and_indent(body))
    }
}

/// Renders a `theorem` declaration — the `Theorem`/`mutual`-group analogue of
/// [`render_def`].
fn render_theorem(name: &str, statement: &str, proof_term: &str, format: ProofFormat) -> String {
    format!("theorem {} : {} := by\n{}\n\n", name, statement.trim(), normalize_proof(proof_term, format))
}

/// Indents every line of a string by two spaces, with NO per-line
/// normalization — for re-indenting an already-correctly-formed, multi-
/// declaration block (e.g. a `mutual` group's concatenated member
/// declarations, each already rendered by [`render_def`]/[`render_theorem`])
/// by one more structural level. Such a block's lines are deliberately NOT
/// uniformly indented (each member's own header sits at column 0 relative to
/// the block, its body at column 2), so [`normalize_and_indent`]'s
/// uniform-vs-flatten logic would wrongly collapse that real structure. Use
/// this only for re-indenting already-assembled Lean text; use
/// `normalize_and_indent` for raw, client-supplied leaf content (a body or
/// proof_term string).
fn indent(s: &str) -> String {
    s.lines().map(|l| format!("  {}", l)).collect::<Vec<_>>().join("\n")
}

/// Indents a client-supplied leaf `body`/`proof_term` string by two spaces —
/// the base indent Lean 4.32+ requires for the first token after `:= by` (or
/// a `def ... :=` on its own line) — while normalizing the client's own
/// per-line indentation first (issue #41).
///
/// Lean's tactic-block parser is whitespace-sensitive: every line at the
/// SAME column as the block's first tactic is a sequential sibling; a line
/// indented MORE than that is parsed as nested under the preceding tactic,
/// not as its sibling. A client that writes the first tactic flush and
/// indents the rest "to show they're part of the block" (a natural,
/// human/LLM-typical style, but not how Lean's syntax actually works) was
/// silently reinterpreted as nesting rather than sequencing, failing with a
/// misleading error that gave no hint the real problem was formatting.
///
/// If every non-blank line already shares one common indentation level
/// (including the ordinary single-line case, and a block someone already
/// indented uniformly), that relationship is preserved exactly as authored —
/// adding the same uniform base indent keeps it uniform. Otherwise (mismatched
/// per-line indentation), every line is flattened to one level before the
/// base indent is applied. This can only ever help: a non-uniformly indented
/// multi-line term reaches the kernel with a 0% success rate today (this
/// exact case is issue #41's repro), so flattening turns a guaranteed
/// rejection into a real elaboration attempt. The tradeoff is that a proof
/// intentionally relying on Lean's relative-indentation nesting (e.g. a `·`
/// focus block with a deeper-indented sub-tactic) would have that nesting
/// discarded too — but that fails loudly (an out-of-scope identifier, since a
/// name introduced only inside the nested block is no longer in scope for a
/// sibling line), never a silent wrong-proof accept, and is no worse than
/// today's guaranteed failure for the same non-uniform input.
pub(crate) fn normalize_and_indent(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let non_blank_indents: Vec<usize> = lines.iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .collect();
    let uniform = non_blank_indents.windows(2).all(|w| w[0] == w[1]);

    if uniform {
        lines.iter().map(|l| format!("  {}", l)).collect::<Vec<_>>().join("\n")
    } else {
        lines.iter().map(|l| format!("  {}", l.trim())).collect::<Vec<_>>().join("\n")
    }
}

/// Issue #51: `raw_lean_block` transport — strip only the COMMON left margin
/// and re-base it to the module's two-space indent, preserving each line's
/// RELATIVE indentation. Unlike [`normalize_and_indent`]'s flattening, a proof
/// that intentionally uses Lean's indentation structure (focus bullets `·`,
/// nested blocks) keeps its shape. Leading whitespace in submitted proofs is
/// single-byte spaces, so slicing at the byte offset `min_indent` is safe.
/// This only rewrites leading whitespace; it never touches tactic text, and
/// the kernel remains the sole authority on the result.
fn rebase_preserving_relative_indent(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let min_indent = lines.iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    lines.iter()
        .map(|l| {
            if l.trim().is_empty() {
                String::new()
            } else {
                format!("  {}", &l[min_indent..])
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Dispatch a proof body through the transport format the caller declared
/// (issue #51). Whitespace-only; the Lean kernel still decides the outcome.
pub(crate) fn normalize_proof(s: &str, format: ProofFormat) -> String {
    match format {
        ProofFormat::FlatTacticSequence => normalize_and_indent(s),
        ProofFormat::RawLeanBlock => rebase_preserving_relative_indent(s),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn manifest() -> Vec<String> {
        vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()]
    }

    fn root(statement: &str, proof: &str) -> ModuleTheorem {
        ModuleTheorem { name: "root_thm".to_string(), statement: statement.to_string(), proof_term: proof.to_string(), proof_format: ProofFormat::FlatTacticSequence }
    }

    fn root_fmt(statement: &str, proof: &str, proof_format: ProofFormat) -> ModuleTheorem {
        ModuleTheorem { name: "root_thm".to_string(), statement: statement.to_string(), proof_term: proof.to_string(), proof_format }
    }

    fn root_hash(statement: &str) -> String {
        canonical_hash(&statement.to_string()).unwrap()
    }

    /// Issue #41's exact repro: a naturally-formatted multi-line proof term
    /// with the first tactic flush and the rest indented by 2. Before the
    /// fix, this shape always produced a mismatched indentation level that
    /// Lean's whitespace-sensitive parser reinterpreted as nesting rather
    /// than sequencing; normalize_and_indent must flatten it to one uniform
    /// level instead of blindly adding a fixed prefix to each line.
    #[test]
    fn normalize_and_indent_flattens_mismatched_first_line_indentation() {
        let input = "intro a ha b hb\n  refine foo\n  ring";
        let out = normalize_and_indent(input);
        assert_eq!(out, "  intro a ha b hb\n  refine foo\n  ring",
            "mismatched per-line indentation must be flattened to one uniform level, not blindly re-prefixed: {out:?}");
    }

    /// A proof term whose lines already share one indentation level
    /// (including a block someone already indented themselves) must be
    /// preserved exactly as authored — adding the same uniform base indent
    /// keeps it uniform, so this must NOT be flattened.
    #[test]
    fn normalize_and_indent_preserves_already_uniform_indentation() {
        let input = "  intro a ha b hb\n  refine foo\n  ring";
        let out = normalize_and_indent(input);
        assert_eq!(out, "    intro a ha b hb\n    refine foo\n    ring",
            "already-uniform per-line indentation must be preserved (just re-based), not stripped: {out:?}");
    }

    #[test]
    fn normalize_and_indent_handles_single_line() {
        assert_eq!(normalize_and_indent("norm_num"), "  norm_num");
    }

    /// A blank line inside a multi-line proof must not force a spurious
    /// "mismatched indentation" flatten — blank lines are excluded from the
    /// uniformity check.
    #[test]
    fn normalize_and_indent_ignores_blank_lines_for_uniformity_check() {
        let input = "  intro a\n\n  ring";
        let out = normalize_and_indent(input);
        assert_eq!(out, "    intro a\n  \n    ring",
            "a blank line must not defeat the uniform-indent detection for otherwise-matching lines: {out:?}");
    }

    /// Regression for a real bug found by adversarial review while fixing
    /// issue #41: assemble_module's root-theorem rendering originally called
    /// the OLD, unfixed indent() directly on root_theorem.proof_term instead
    /// of going through render_theorem/normalize_and_indent like every other
    /// item — meaning the actual goal being proved in a SubmitModule call
    /// (the root theorem) was still exposed to the exact bug this fix exists
    /// for. Confirms assemble_module's assembled source reflects the
    /// flattened, normalized proof for a mismatched-indentation root
    /// proof_term, not the double-indented (and Lean-misparsed) original.
    #[test]
    fn assemble_module_normalizes_root_theorem_proof_term_indentation() {
        let r = root("1 + 1 = 2", "intro\n  norm_num");
        let asm = assemble_module("ProofSearch.P_abc", &root_hash("1 + 1 = 2"), &[], &r, &manifest()).unwrap();
        assert!(asm.source.contains("theorem root_thm : 1 + 1 = 2 := by\n  intro\n  norm_num"),
            "root theorem's mismatched-indentation proof_term must be flattened to one uniform level, not blindly re-prefixed: {}", asm.source);
    }

    /// Issue #51: raw_lean_block preserves RELATIVE indentation (focus bullets
    /// keep their nesting), whereas flat_tactic_sequence flattens it. Same
    /// input, two transport formats, two different rendered shapes.
    #[test]
    fn raw_block_preserves_relative_indentation() {
        let input = "constructor\n  · exact h1\n  · exact h2";
        assert_eq!(normalize_proof(input, ProofFormat::RawLeanBlock),
            "  constructor\n    · exact h1\n    · exact h2",
            "raw_lean_block must keep the two-space focus-bullet nesting under a re-based margin");
        assert_eq!(normalize_proof(input, ProofFormat::FlatTacticSequence),
            "  constructor\n  · exact h1\n  · exact h2",
            "flat_tactic_sequence must flatten the mismatched nesting to one level (issue #41 behavior)");
    }

    /// raw_lean_block strips only the COMMON left margin and re-bases it, so a
    /// pre-indented block keeps its internal relative structure.
    #[test]
    fn raw_block_strips_common_margin_and_rebases() {
        let input = "  intro h\n    cases h";
        assert_eq!(normalize_proof(input, ProofFormat::RawLeanBlock),
            "  intro h\n    cases h",
            "the common 2-space margin is stripped and a 2-space base re-added, so the +2 relative indent survives");
    }

    /// Issue #51 acceptance at the assembly layer: a raw_lean_block root proof
    /// reaches the assembled module source with its nesting intact.
    #[test]
    fn assemble_module_root_theorem_raw_block_preserves_nesting() {
        let r = root_fmt("p ∧ q", "constructor\n  · exact h1\n  · exact h2", ProofFormat::RawLeanBlock);
        let asm = assemble_module("ProofSearch.P_abc", &root_hash("p ∧ q"), &[], &r, &manifest()).unwrap();
        assert!(asm.source.contains("theorem root_thm : p ∧ q := by\n  constructor\n    · exact h1\n    · exact h2"),
            "raw_lean_block root proof must keep its focus-bullet nesting in the assembled source: {}", asm.source);
    }

    #[test]
    fn assembles_def_plus_root_under_namespace() {
        let items = vec![LeanModuleItem::Def {
            name: "double".to_string(),
            type_signature: "Nat → Nat".to_string(),
            body: "fun n => n + n".to_string(),
        }];
        let r = root("double 2 = 4", "rfl");
        let asm = assemble_module("ProofSearch.P_abc", &root_hash("double 2 = 4"), &items, &r, &manifest()).unwrap();
        assert!(asm.source.contains("import Mathlib.Tactic.Ring"), "{}", asm.source);
        assert!(asm.source.contains("namespace ProofSearch.P_abc"), "{}", asm.source);
        assert!(asm.source.contains("def double : Nat → Nat :="), "{}", asm.source);
        assert!(asm.source.contains("theorem root_thm : double 2 = 4 := by"), "{}", asm.source);
        // `end ProofSearch.P_abc` closes the namespace; the trailing bare `end`
        // closes the issue-#63 `noncomputable section`.
        assert!(asm.source.trim_end().ends_with("end ProofSearch.P_abc\nend"), "{}", asm.source);
        // manifest: def + root_theorem, root linked and hashed.
        assert_eq!(asm.item_manifest.len(), 2);
        assert_eq!(asm.item_manifest[1].kind, "root_theorem");
        assert_eq!(asm.item_manifest[1].statement_or_type_hash, root_hash("double 2 = 4"));
        assert!(!asm.module_source_hash.is_empty());
        assert!(!asm.declaration_manifest_hash.is_empty());
        // dependency detection: root uses `double`.
        assert_eq!(asm.item_manifest[1].depends_on, vec!["double".to_string()]);
    }

    /// Issue #63: the whole module sits in a `noncomputable section`, so a
    /// solution def over a noncomputable carrier (Polynomial/ℝ/Measure)
    /// compiles. The section opens before the namespace and is closed by the
    /// final bare `end`.
    #[test]
    fn assembled_module_is_wrapped_in_noncomputable_section() {
        let r = root("1 + 1 = 2", "norm_num");
        let asm = assemble_module("ProofSearch.P_abc", &root_hash("1 + 1 = 2"), &[], &r, &manifest()).unwrap();
        assert!(asm.source.contains("noncomputable section\n\nnamespace ProofSearch.P_abc"),
            "noncomputable section must open before the namespace: {}", asm.source);
        assert!(asm.source.trim_end().ends_with("end ProofSearch.P_abc\nend"),
            "the final bare `end` must close the section after the namespace closes: {}", asm.source);
    }

    /// Issue #62: `open` entries in the import manifest render as open
    /// directives just inside the namespace, not as `import` lines.
    #[test]
    fn open_manifest_entries_render_inside_namespace() {
        let mut m = manifest();
        m.push("open Polynomial".to_string());
        m.push("open scoped BigOperators".to_string());
        let r = root("1 + 1 = 2", "norm_num");
        let asm = assemble_module("ProofSearch.P_abc", &root_hash("1 + 1 = 2"), &[], &r, &m).unwrap();
        assert!(asm.source.contains("namespace ProofSearch.P_abc\n\nopen Polynomial\nopen scoped BigOperators\n\n"),
            "open directives must sit just inside the namespace: {}", asm.source);
        assert!(!asm.source.contains("import open"),
            "a valid open entry must never render as an import line: {}", asm.source);
    }

    /// Issue #62 security boundary: only `open [scoped] <dotted idents>`
    /// parses; anything else (command separators, injection attempts) is not
    /// an open directive and falls through to the visibly-broken import path.
    #[test]
    fn open_directive_parsing_is_strict_and_canonicalizing() {
        assert_eq!(parse_open_directive("open Polynomial"), Some("open Polynomial".to_string()));
        assert_eq!(parse_open_directive("open   Polynomial    Real"), Some("open Polynomial Real".to_string()));
        assert_eq!(parse_open_directive("open scoped BigOperators"), Some("open scoped BigOperators".to_string()));
        assert_eq!(parse_open_directive("open EuclideanGeometry.Sphere'"), Some("open EuclideanGeometry.Sphere'".to_string()));
        assert_eq!(parse_open_directive("Mathlib.Tactic.Ring"), None, "a plain module path is not an open directive");
        assert_eq!(parse_open_directive("open"), None, "open with no namespaces is invalid");
        assert_eq!(parse_open_directive("open scoped"), None, "open scoped with no namespaces is invalid");
        assert_eq!(parse_open_directive("open Foo\naxiom cheat : False"), None,
            "a colon token can never be a namespace path — injection attempt must not parse");
        assert_eq!(parse_open_directive("open Foo (renaming)"), None, "parenthesized open syntax is not admitted");
        // Multi-line whitespace between otherwise-valid tokens canonicalizes to
        // one line — the rendered text is rebuilt from parsed tokens, so no raw
        // newline can survive into the source even if validation is loosened.
        assert_eq!(parse_open_directive("open Foo\nBar"), Some("open Foo Bar".to_string()));
    }

    /// Issue #64: under the benchmark-statement guard, a helper def bound to a
    /// name the root statement references free is rejected — with an honest
    /// alias body just as much as a malicious one, because the checker cannot
    /// tell them apart.
    #[test]
    fn rejects_module_def_shadowing_root_statement_identifier() {
        let items = vec![LeanModuleItem::Def {
            name: "C".to_string(),
            type_signature: "Nat → Nat".to_string(),
            body: "fun _ => 0".to_string(),
        }];
        let r = root("∀ a : Nat, C a = C a", "intro a; rfl");
        let err = check_no_root_statement_shadowing(&items, &r).unwrap_err();
        assert!(matches!(err, ModulePolicyError::ShadowsRootStatementIdentifier { ref name } if name == "C"), "{:?}", err);
    }

    /// Issue #64: mutual-group members are covered by the guard too.
    #[test]
    fn rejects_mutual_member_shadowing_root_statement_identifier() {
        let items = vec![LeanModuleItem::MutualGroup { members: vec![
            MutualMember::Def { name: "isEven".to_string(), type_signature: "Nat → Bool".to_string(), body: "fun _ => true".to_string() },
            MutualMember::Def { name: "isOdd".to_string(), type_signature: "Nat → Bool".to_string(), body: "fun _ => false".to_string() },
        ]}];
        let r = root("isEven 4 = true", "rfl");
        let err = check_no_root_statement_shadowing(&items, &r).unwrap_err();
        assert!(matches!(err, ModulePolicyError::ShadowsRootStatementIdentifier { ref name } if name == "isEven"), "{:?}", err);
    }

    /// Issue #64: the `_solution` slot is the sanctioned exception — a
    /// find-the-value statement REQUIRES the module to supply exactly that
    /// name.
    #[test]
    fn solution_slot_is_exempt_from_shadow_rejection() {
        let items = vec![LeanModuleItem::Def {
            name: "putnam_1963_b1_solution".to_string(),
            type_signature: "Int".to_string(),
            body: "2".to_string(),
        }];
        let stmt = "∀ a : Int, a = putnam_1963_b1_solution ↔ a = putnam_1963_b1_solution";
        let r = root(stmt, "intro a; rfl");
        assert!(check_no_root_statement_shadowing(&items, &r).is_ok());
    }

    /// Issue #64: a qualified-name SUFFIX in the statement (`Finset.Icc`,
    /// `p.coeff`) is not capturable by a module-local declaration and must not
    /// trigger the rejection; helper names absent from the statement remain
    /// fine.
    #[test]
    fn qualified_suffixes_and_fresh_names_do_not_trigger_shadow_rejection() {
        let items = vec![
            LeanModuleItem::Def {
                name: "Icc".to_string(),
                type_signature: "Nat".to_string(),
                body: "0".to_string(),
            },
            LeanModuleItem::Theorem {
                name: "helper_step".to_string(),
                statement: "1 + 1 = 2".to_string(),
                proof_term: "norm_num".to_string(),
            },
        ];
        let stmt = "∀ n : Nat, n ∈ Finset.Icc 0 n → n = n";
        let r = root(stmt, "intro n _; rfl");
        assert!(check_no_root_statement_shadowing(&items, &r).is_ok(),
            "`Icc` occurs only as a qualified suffix (`Finset.Icc`) and must not be treated as capturable");
    }

    /// Issue #64 scoping: assemble_module itself does NOT reject a root
    /// statement referencing the module's own defs — that is the documented
    /// SubmitModule shape for client-authored problems. The guard is applied
    /// by the orchestrator only for benchmark-registered statements.
    #[test]
    fn assemble_module_itself_allows_module_supplied_identifiers() {
        let items = vec![LeanModuleItem::Def {
            name: "double".to_string(),
            type_signature: "Nat → Nat".to_string(),
            body: "fun n => n + n".to_string(),
        }];
        let r = root("double 2 = 4", "rfl");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("double 2 = 4"), &items, &r, &manifest()).is_ok());
    }

    #[test]
    fn helper_theorem_then_root() {
        let items = vec![LeanModuleItem::Theorem {
            name: "helper".to_string(),
            statement: "1 + 1 = 2".to_string(),
            proof_term: "norm_num".to_string(),
        }];
        let r = root("2 + 2 = 4", "norm_num");
        let asm = assemble_module("ProofSearch.P_x", &root_hash("2 + 2 = 4"), &items, &r, &manifest()).unwrap();
        assert!(asm.source.contains("theorem helper : 1 + 1 = 2 := by"), "{}", asm.source);
        assert!(asm.source.contains("theorem root_thm : 2 + 2 = 4 := by"), "{}", asm.source);
    }

    #[test]
    fn rejects_root_statement_hash_mismatch() {
        let r = root("1 + 1 = 3", "norm_num");
        let err = assemble_module("ProofSearch.P_x", &root_hash("1 + 1 = 2"), &[], &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::RootStatementMismatch { .. }), "{:?}", err);
    }

    #[test]
    fn rejects_axiom_injection_in_def_body() {
        // The classic escape: a body that closes its own declaration and opens a
        // fresh top-level `axiom`. Must be rejected at policy, never compiled.
        let items = vec![LeanModuleItem::Def {
            name: "evil".to_string(),
            type_signature: "Nat".to_string(),
            body: "0\n\naxiom cheat : False".to_string(),
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        match err {
            ModulePolicyError::ProhibitedConstruct { token, .. } => assert_eq!(token, "axiom"),
            other => panic!("expected ProhibitedConstruct(axiom), got {:?}", other),
        }
    }

    /// Regression: Lean does not require a new top-level command to start on its
    /// own line — only that the preceding term is syntactically complete. A
    /// leading-token scan keyed on `content.lines()` never inspects this
    /// same-line form (`def evil := 0 theorem cheat : True := trivial` parses as
    /// `def evil := 0` followed by a fresh `theorem` command in real Lean).
    /// Closed by scanning for banned tokens anywhere in the content, not just at
    /// the start of a line.
    #[test]
    fn rejects_same_line_declaration_injection() {
        let items = vec![LeanModuleItem::Def {
            name: "evil".to_string(),
            type_signature: "Nat".to_string(),
            body: "0 theorem cheat : True := trivial".to_string(),
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        match err {
            ModulePolicyError::ProhibitedConstruct { token, .. } => assert_eq!(token, "theorem"),
            other => panic!("expected ProhibitedConstruct(theorem), got {:?}", other),
        }
    }

    /// Same bypass class via a modifier instead of the bare keyword, still on
    /// one line — must be caught too, not just the bare-keyword form.
    #[test]
    fn rejects_same_line_modifier_prefixed_injection() {
        let items = vec![LeanModuleItem::Def {
            name: "evil".to_string(),
            type_signature: "Nat".to_string(),
            body: "0 private theorem cheat : True := trivial".to_string(),
        }];
        let r = root("True", "trivial");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).is_err());
    }

    /// Same bypass class via an inline attribute, still on one line.
    #[test]
    fn rejects_same_line_attribute_injection() {
        let items = vec![LeanModuleItem::Def {
            name: "evil".to_string(),
            type_signature: "Nat".to_string(),
            body: "0 @[simp] theorem cheat : True := trivial".to_string(),
        }];
        let r = root("True", "trivial");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).is_err());
    }

    /// Review feedback on #16: an attribute list (`@[simp]`) immediately before a
    /// declaration bypasses a scanner that only checks whether the first token IS
    /// the declaration keyword — the first token here is `@[simp]`, not `theorem`.
    #[test]
    fn rejects_attribute_prefixed_declaration_escape() {
        // A realistic attribute-prefixed injection always pairs the attribute
        // with its declaration keyword (`@[simp] theorem ...`), so the bare
        // whole-word ban on `theorem` alone already rejects this too — the
        // property under test is REJECTION, not which of the two independently-
        // banned tokens gets reported first. Direct `@[`-only coverage (with no
        // other violation present) lives in `rejects_same_line_attribute_injection`.
        let items = vec![LeanModuleItem::Def {
            name: "evil".to_string(),
            type_signature: "Nat".to_string(),
            body: "0\n\n@[simp] theorem cheat : False := by trivial".to_string(),
        }];
        let r = root("True", "trivial");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).is_err());
    }

    /// Review feedback on #16: `private`/`protected`/`local`/`scoped` modifiers
    /// immediately before a declaration keyword are the same escape as an
    /// attribute — the first token is the modifier, not the declaration keyword.
    /// As with the attribute case above, a realistic modifier-prefixed injection
    /// always pairs the modifier with its declaration keyword, so this asserts
    /// rejection rather than which specific token is reported.
    #[test]
    fn rejects_modifier_prefixed_declaration_escapes() {
        let cases = ["private", "protected", "local", "scoped"];
        for modifier in cases {
            let items = vec![LeanModuleItem::Def {
                name: "evil".to_string(),
                type_signature: "Nat".to_string(),
                body: format!("0\n\n{} theorem cheat : False := by trivial", modifier),
            }];
            let r = root("True", "trivial");
            assert!(
                assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).is_err(),
                "modifier {} not caught", modifier
            );
        }
    }

    /// `local notation` / `scoped notation` are top-level commands (not
    /// expressions) — a client string must not be able to declare notation, and
    /// the leading-modifier ban must catch this form too.
    #[test]
    fn rejects_local_and_scoped_notation() {
        for prefix in ["local notation", "scoped notation"] {
            let r = root("True", &format!("{} \"¤\" => cheat\ntrivial", prefix));
            let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &[], &r, &manifest()).unwrap_err();
            assert!(matches!(err, ModulePolicyError::ProhibitedConstruct { .. }), "{:?}", err);
        }
    }

    /// Explicit-argument application (`@id Nat n`) is legitimate proof-term
    /// syntax and must NOT be confused with an attribute list (`@[...]`) — only
    /// the literal `@[` prefix is banned, not a bare `@`.
    #[test]
    fn explicit_application_at_sign_is_not_confused_with_attribute() {
        let r = root("True", "have := @id Nat 0\ntrivial");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("True"), &[], &r, &manifest()).is_ok());
    }

    #[test]
    fn rejects_sorry_anywhere() {
        let r = root("True", "exact sorry");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &[], &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::ProhibitedConstruct { .. }), "{:?}", err);
    }

    #[test]
    fn rejects_dotted_name_namespace_escape() {
        let items = vec![LeanModuleItem::Def {
            name: "Mathlib.cheat".to_string(),
            type_signature: "Nat".to_string(),
            body: "0".to_string(),
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::InvalidName { .. }), "{:?}", err);
    }

    #[test]
    fn rejects_import_line_in_proof() {
        let r = root("True", "trivial\nimport Mathlib");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &[], &r, &manifest()).unwrap_err();
        match err {
            ModulePolicyError::ProhibitedConstruct { token, .. } => assert_eq!(token, "import"),
            other => panic!("expected import rejection, got {:?}", other),
        }
    }

    #[test]
    fn rejects_duplicate_names() {
        let items = vec![
            LeanModuleItem::Def { name: "f".to_string(), type_signature: "Nat".to_string(), body: "0".to_string() },
            LeanModuleItem::Def { name: "f".to_string(), type_signature: "Nat".to_string(), body: "1".to_string() },
        ];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::DuplicateName { .. }), "{:?}", err);
    }

    #[test]
    fn word_boundary_does_not_flag_substrings() {
        // `axiomatic` / `sorryish` are not the banned tokens; a def named with a
        // superstring identifier in the body must still assemble.
        let items = vec![LeanModuleItem::Def {
            name: "factorial".to_string(),
            type_signature: "Nat → Nat".to_string(),
            // contains "importance" and "endpoint" — superstrings of import/end.
            body: "fun n => n -- importance of the endpoint".to_string(),
        }];
        let r = root("True", "trivial");
        assert!(assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).is_ok());
    }

    // -- MutualGroup (issue #19) ---------------------------------------------

    /// The exact repro from issue #19: `isEven`/`isOdd`, each referencing the
    /// other. Must render inside one `mutual ... end` block, and each member's
    /// name must be visible to its sibling in the rendered source.
    #[test]
    fn mutual_group_renders_forward_referencing_defs_inside_one_block() {
        let items = vec![LeanModuleItem::MutualGroup {
            members: vec![
                MutualMember::Def {
                    name: "isEven".to_string(),
                    type_signature: "Nat → Bool".to_string(),
                    body: "fun n => match n with\n  | 0 => true\n  | (k+1) => isOdd k".to_string(),
                },
                MutualMember::Def {
                    name: "isOdd".to_string(),
                    type_signature: "Nat → Bool".to_string(),
                    body: "fun n => match n with\n  | 0 => false\n  | (k+1) => isEven k".to_string(),
                },
            ],
        }];
        let r = root("isEven 4 = true", "rfl");
        let asm = assemble_module("ProofSearch.P_x", &root_hash("isEven 4 = true"), &items, &r, &manifest()).unwrap();
        assert!(asm.source.contains("mutual\n"), "{}", asm.source);
        assert!(asm.source.contains("def isEven"), "{}", asm.source);
        assert!(asm.source.contains("def isOdd"), "{}", asm.source);
        assert!(asm.source.contains("end\n"), "{}", asm.source);
        // `mutual`/`end` appear ONLY as the server-rendered wrapper, never as
        // client-suppliable tokens — same trust boundary as every other item.
        assert!(asm.source.contains("mutual\n\n"), "{}", asm.source);

        // Manifest: two `def` rows + the root, sharing one mutual_group index,
        // and unique `order` values (both were flattened from ONE module_items
        // entry, so `order` can no longer be the client's item index).
        assert_eq!(asm.item_manifest.len(), 3);
        assert_eq!(asm.item_manifest[0].kind, "def");
        assert_eq!(asm.item_manifest[0].lean_name, "isEven");
        assert_eq!(asm.item_manifest[0].mutual_group, Some(0));
        assert_eq!(asm.item_manifest[1].kind, "def");
        assert_eq!(asm.item_manifest[1].lean_name, "isOdd");
        assert_eq!(asm.item_manifest[1].mutual_group, Some(0));
        assert_eq!(asm.item_manifest[2].kind, "root_theorem");
        assert_eq!(asm.item_manifest[2].mutual_group, None);
        let orders: std::collections::HashSet<usize> = asm.item_manifest.iter().map(|it| it.order).collect();
        assert_eq!(orders.len(), 3, "item_manifest order values must be unique: {:?}", asm.item_manifest);

        // Forward reference detected: isEven depends on isOdd even though
        // isOdd is declared AFTER it in the group.
        assert_eq!(asm.item_manifest[0].depends_on, vec!["isOdd".to_string()]);
        assert_eq!(asm.item_manifest[1].depends_on, vec!["isEven".to_string()]);
    }

    /// A group of fewer than 2 members has no forward-reference problem to
    /// solve — reject it rather than silently accepting a pointless `mutual`
    /// wrapper around a single declaration.
    #[test]
    fn rejects_mutual_group_with_fewer_than_two_members() {
        let items = vec![LeanModuleItem::MutualGroup {
            members: vec![MutualMember::Def {
                name: "lonely".to_string(),
                type_signature: "Nat".to_string(),
                body: "0".to_string(),
            }],
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::InvalidMutualGroup { .. }), "{:?}", err);

        let empty_items = vec![LeanModuleItem::MutualGroup { members: vec![] }];
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &empty_items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::InvalidMutualGroup { .. }), "{:?}", err);
    }

    /// A duplicate name between two mutual-group members (or between a group
    /// member and any other item) must still be rejected — grouping does not
    /// create a private naming scope.
    #[test]
    fn rejects_duplicate_names_within_mutual_group() {
        let items = vec![LeanModuleItem::MutualGroup {
            members: vec![
                MutualMember::Def { name: "f".to_string(), type_signature: "Nat".to_string(), body: "0".to_string() },
                MutualMember::Def { name: "f".to_string(), type_signature: "Nat".to_string(), body: "1".to_string() },
            ],
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::DuplicateName { .. }), "{:?}", err);
    }

    /// The same injection hardening applies inside a mutual-group member's
    /// content as everywhere else — grouping is not an escape hatch.
    #[test]
    fn rejects_axiom_injection_inside_mutual_group_member() {
        let items = vec![LeanModuleItem::MutualGroup {
            members: vec![
                MutualMember::Def {
                    name: "a".to_string(),
                    type_signature: "Nat".to_string(),
                    body: "0\n\naxiom cheat : False".to_string(),
                },
                MutualMember::Def { name: "b".to_string(), type_signature: "Nat".to_string(), body: "0".to_string() },
            ],
        }];
        let r = root("True", "trivial");
        let err = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap_err();
        assert!(matches!(err, ModulePolicyError::ProhibitedConstruct { .. }), "{:?}", err);
    }

    /// A mutual group may mix `Def` and `Theorem` members (e.g. a pair of
    /// mutually recursive proofs about mutually recursive defs elsewhere in
    /// the module) — the render/manifest path must handle both member kinds.
    #[test]
    fn mutual_group_supports_mixed_def_and_theorem_members() {
        let items = vec![LeanModuleItem::MutualGroup {
            members: vec![
                MutualMember::Theorem {
                    name: "helper_a".to_string(),
                    statement: "True".to_string(),
                    proof_term: "trivial".to_string(),
                },
                MutualMember::Theorem {
                    name: "helper_b".to_string(),
                    statement: "True".to_string(),
                    proof_term: "trivial".to_string(),
                },
            ],
        }];
        let r = root("True", "trivial");
        let asm = assemble_module("ProofSearch.P_x", &root_hash("True"), &items, &r, &manifest()).unwrap();
        assert!(asm.source.contains("theorem helper_a"), "{}", asm.source);
        assert!(asm.source.contains("theorem helper_b"), "{}", asm.source);
        assert_eq!(asm.item_manifest[0].kind, "theorem");
        assert_eq!(asm.item_manifest[1].kind, "theorem");
    }

    /// A standalone item declared before a mutual group, and the root theorem
    /// declared after it, must still resolve dependencies correctly against
    /// group members — the group's forward-reference exception must not leak
    /// into normal earlier/later ordering elsewhere in the module.
    #[test]
    fn mutual_group_coexists_with_standalone_items_and_root() {
        let items = vec![
            LeanModuleItem::Def { name: "seed".to_string(), type_signature: "Nat".to_string(), body: "1".to_string() },
            LeanModuleItem::MutualGroup {
                members: vec![
                    MutualMember::Def {
                        name: "isEven".to_string(),
                        type_signature: "Nat → Bool".to_string(),
                        body: "fun n => match n with\n  | 0 => true\n  | (k+1) => isOdd k".to_string(),
                    },
                    MutualMember::Def {
                        name: "isOdd".to_string(),
                        type_signature: "Nat → Bool".to_string(),
                        body: "fun n => match n with\n  | 0 => false\n  | (k+1) => isEven k".to_string(),
                    },
                ],
            },
        ];
        let r = root("isEven seed = true", "rfl");
        let asm = assemble_module("ProofSearch.P_x", &root_hash("isEven seed = true"), &items, &r, &manifest()).unwrap();
        assert_eq!(asm.item_manifest.len(), 4);
        assert_eq!(asm.item_manifest[0].lean_name, "seed");
        assert_eq!(asm.item_manifest[0].mutual_group, None);
        // Root theorem depends on isEven (used in its statement) — resolved
        // against names declared by the (now-closed) mutual group.
        assert!(asm.item_manifest[3].depends_on.contains(&"isEven".to_string()));
    }
}
