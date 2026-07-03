use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use rusqlite::{Connection, OptionalExtension, Transaction};
use uuid::Uuid;
use chrono::Utc;
use serde::Deserialize;
use schemars::JsonSchema;

use rmcp::ServerHandler;
use rmcp::model::*;
use rmcp::service::RequestContext;
use rmcp::service::RoleServer;
pub use rmcp::ErrorData as McpError;

use chatdb_proof_core::db::schema_v1;
use chatdb_proof_core::orchestrator::{lifecycle, attempts, step, trajectories};
use chatdb_proof_core::lean::{LeanGateway, RealLeanGateway};
use chatdb_proof_core::models::action::{TypedAction, ActionRequest, ActionRole, StepDisposition, LeanModuleItem, ModuleTheorem};
use chatdb_proof_core::lean::module::assemble_module;
use chatdb_proof_core::models::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use chatdb_proof_core::models::reward::{RewardComponent, RewardComponentId, RewardPolicy};
use chatdb_proof_core::hashing::canonical_hash;

/// Every problem's import manifest starts with these two; problem_imports adds to
/// them. Kept in one place so the "what does a bare problem_create get by
/// default" answer stays consistent with what RealLeanGateway historically
/// hardcoded.
const BASE_IMPORT_MANIFEST: &[&str] = &["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum"];

/// A Lean import target is written verbatim into `import {module}\n` source.
/// This is the entire security boundary for that interpolation: reject
/// anything but a dotted sequence of identifier segments so a string can never
/// contain a newline, comment, or command separator that would let it inject
/// arbitrary Lean source (e.g. `axiom cheat : False`) into every proof file
/// checked against this manifest.
fn valid_lean_module_path(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 256
        && s.split('.').all(|segment| {
            !segment.is_empty()
                && segment.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && segment.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

/// A Lean declaration name is written verbatim into `#check {name}\n` source.
/// Same boundary as `valid_lean_module_path`, slightly more permissive to
/// admit Lean identifier characters (primes, unicode letters used in
/// mathlib names) while still excluding anything that could break out of a
/// single `#check` line: whitespace, newlines, comment/command syntax.
fn valid_lean_declaration_name(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 256
        && !s.chars().any(|c| c.is_whitespace())
        && s.chars().all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '!' | '?'))
}

// ---------------------------------------------------------------------------
// Tool argument schemas
// ---------------------------------------------------------------------------

#[derive(JsonSchema, Deserialize)]
pub struct EnvironmentDescribeArgs {}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemCreateArgs {
    pub source_problem_text: String,
    pub root_formal_statement: String,
    #[serde(default)]
    pub normalized_root_rendering: Option<String>,
    #[serde(default)]
    pub environment_hash: Option<String>,
    #[serde(default)]
    pub metadata_json: Option<String>,
    /// Additional Mathlib modules (beyond the base Ring + NormNum set) this
    /// problem's proofs may import — e.g. "Mathlib.NumberTheory.Padics.PadicVal.Basic".
    /// Each is validated (a real compile check, not a name-shape check) before the
    /// problem is created; an unresolvable module is rejected outright. The
    /// resulting manifest is immutable for this problem_version — see
    /// docs/fix_plan_playtest_03.md. Broadening imports for an existing problem
    /// means creating a new problem_version with an extended list.
    #[serde(default)]
    pub problem_imports: Option<Vec<String>>,
    /// Named honestly on purpose: this is NOT a review. It sets fidelity_status
    /// to 'attested' (proving is allowed) — never 'verified'. Episodes created
    /// under 'attested' can reach outcome=kernel_verified but never 'certified',
    /// and their data is excluded from dataset exports by default. Use
    /// problem_submit_fidelity_review for a real, evidence-backed determination.
    #[serde(default)]
    pub unsafe_dev_attestation: bool,
}

#[derive(JsonSchema, Deserialize)]
pub enum FidelityDecision {
    #[serde(rename = "verified")]
    Verified,
    #[serde(rename = "rejected")]
    Rejected,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemSubmitFidelityReviewArgs {
    pub problem_version_id: String,
    pub decision: FidelityDecision,
    /// e.g. "human_review", "dual_model_review", "gold_benchmark_alignment" —
    /// free text naming how the decision was reached; not policy-enforced here.
    pub method: String,
    pub approver_id: String,
    pub rubric_version: String,
    /// The server independently recomputes source_problem_hash,
    /// root_statement_hash, and normalized_rendering_hash from the CURRENT
    /// problem_versions row and rejects the submission if these don't match —
    /// a review can only authorize the exact text it actually reviewed.
    pub source_problem_hash: String,
    pub root_statement_hash: String,
    pub rendering_hash: String,
    pub evidence_json: String,
    #[serde(default)]
    pub notes: Option<String>,
    #[serde(default)]
    pub signature: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemListArgs {
    #[serde(default)]
    pub limit: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeCreateArgs {
    pub problem_version_id: String,
    #[serde(default)]
    pub max_steps: Option<i32>,
    #[serde(default)]
    pub cost_budget_micros: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeResetArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeObserveArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct AttemptClaimArgs {
    pub episode_id: String,
    pub action_request_id: String,
    pub idempotency_key: String,
    pub expected_revision: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeStepArgs {
    pub episode_id: String,
    pub action_attempt_id: String,
    pub expected_revision: i64,
    pub claim_token: String,
    pub action: TypedAction,
    pub cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeStatusArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeCloseArgs {
    pub episode_id: String,
    pub reason: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct ModelCallReserveArgs {
    pub episode_id: String,
    pub action_attempt_id: String,
    pub runner_id: String,
    pub declared_model: String,
    pub max_input_tokens: i64,
    pub max_output_tokens: i64,
    pub reserved_cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct ModelCallSettleArgs {
    pub lease_id: String,
    pub actual_cost_micros: i64,
    pub status: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct TrajectoryExportArgs {
    pub episode_id: String,
    #[serde(default)]
    pub cursor: Option<i64>,
    #[serde(default)]
    pub page_size: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeReplayArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofExportArgs {
    pub episode_id: String,
    /// "markdown" (default): full human-readable dossier — proof tree, assembled
    /// Lean source, attempt history, integrity line. "lean": bare assembled Lean
    /// source only, ready to paste into a Mathlib project.
    #[serde(default)]
    pub format: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct LeanDeclarationLookupArgs {
    pub problem_version_id: String,
    /// Fully-qualified names to check, e.g. "Nat.factorization", "padicValNat".
    pub names: Vec<String>,
    /// false (default, fast — sub-second beyond process spawn): only checks
    /// under the problem's own manifest. A failure reports
    /// "not_available_under_current_manifest" WITHOUT determining whether that's
    /// because the name needs an import or is genuinely absent.
    /// true (slow — reliably 15-40+ seconds, since there is no persistent Lean
    /// server and the full Mathlib umbrella must be loaded from a cold process):
    /// also checks names that failed under "import Mathlib", splitting the
    /// result into "not_in_current_import_scope" vs "unknown_declaration". Only
    /// set this when that distinction is worth the wait.
    #[serde(default)]
    pub deep_check: bool,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_tool<T: JsonSchema>(name: &'static str, desc: &'static str) -> Tool {
    let settings = schemars::r#gen::SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
        // Inline nested types (e.g. TypedAction) at the parameter site instead of
        // emitting `$ref: #/definitions/...`. Many client harnesses decide whether
        // a parameter is an object by the *declared* type at the param node and do
        // not chase refs — a `$ref` there makes them ship the value as a string.
        // Inlining also sidesteps the draft-2020-12 `definitions` vs `$defs` split.
        s.inline_subschemas = true;
    });
    let generator = settings.into_generator();
    let mut schema = generator.into_root_schema_for::<T>();
    schema.schema.metadata().id = Some("https://json-schema.org/draft/2020-12/schema".to_string());
    let mut val = serde_json::to_value(&schema.schema).unwrap();
    annotate_oneof_objecthood(&mut val);
    let obj = val.as_object().unwrap().clone();
    Tool::new(name, desc, obj)
}

/// schemars emits tagged-enum schemas as a bare `oneOf` with no top-level `type`.
/// Coercion-by-declared-type clients need to see `"type": "object"` at the node
/// itself, so stamp it on wherever every branch of the oneOf is an object.
fn annotate_oneof_objecthood(val: &mut serde_json::Value) {
    match val {
        serde_json::Value::Object(obj) => {
            let all_branches_are_objects = obj.get("oneOf").and_then(|v| v.as_array()).map(|arr| {
                !arr.is_empty() && arr.iter().all(|b| b.get("type").and_then(|t| t.as_str()) == Some("object"))
            }).unwrap_or(false);
            if all_branches_are_objects && !obj.contains_key("type") {
                obj.insert("type".to_string(), serde_json::Value::String("object".to_string()));
            }
            for (_, v) in obj.iter_mut() {
                annotate_oneof_objecthood(v);
            }
        }
        serde_json::Value::Array(arr) => {
            for v in arr.iter_mut() {
                annotate_oneof_objecthood(v);
            }
        }
        _ => {}
    }
}

fn query_action_request(conn: &Connection, id: Uuid) -> Result<ActionRequest, rusqlite::Error> {
    conn.query_row(
        "SELECT id, episode_id, problem_version_id, episode_revision, request_sequence_number, role, state_hash_before, status, expiration_at, created_at FROM action_requests WHERE id = ?1",
        [id.to_string()],
        |row| {
            let id_str: String = row.get(0)?;
            let ep_id_str: String = row.get(1)?;
            let pv_id_str: String = row.get(2)?;
            let role_str: String = row.get(5)?;
            let role = match role_str.as_str() {
                "prover" => ActionRole::Prover,
                "reviewer" => ActionRole::Reviewer,
                _ => ActionRole::Human,
            };
            let created_at_str: String = row.get(9)?;
            let created_at = chrono::DateTime::parse_from_rfc3339(&created_at_str).unwrap().with_timezone(&Utc);
            let exp_str: Option<String> = row.get(8)?;
            let expiration_at = exp_str.map(|s| chrono::DateTime::parse_from_rfc3339(&s).unwrap().with_timezone(&Utc));

            Ok(ActionRequest {
                id: Uuid::parse_str(&id_str).unwrap(),
                episode_id: Uuid::parse_str(&ep_id_str).unwrap(),
                problem_version_id: Uuid::parse_str(&pv_id_str).unwrap(),
                episode_revision: row.get(3)?,
                request_sequence_number: row.get(4)?,
                role,
                state_hash_before: row.get(6)?,
                status: row.get(7)?,
                expiration_at,
                created_at,
            })
        }
    )
}

fn mcp_invalid_params(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INVALID_PARAMS, msg, None)
}

fn mcp_internal_error(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INTERNAL_ERROR, msg, None)
}

fn rs(e: impl std::fmt::Display) -> McpError {
    mcp_internal_error(e.to_string())
}

/// The problem version's environment hash, joined through an episode.
fn episode_env_hash(conn: &Connection, episode_id: &str) -> rusqlite::Result<String> {
    conn.query_row(
        "SELECT pv.environment_hash FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id WHERE e.id = ?1",
        [episode_id],
        |row| row.get(0),
    )
}

/// Small, cheap fingerprint of the episode's externally-visible progress. Not a
/// full content-addressed state hash of every obligation — good enough to chain
/// trajectory events and to give `state_hash_before` on action_requests real
/// content instead of a placeholder.
fn episode_progress_hash(tx: &Transaction, episode_id: &str) -> Result<String, McpError> {
    let (rev, steps, state): (i64, i64, String) = tx.query_row(
        "SELECT current_revision, step_count, state FROM episodes WHERE id = ?1",
        [episode_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).map_err(rs)?;
    canonical_hash(&serde_json::json!({"revision": rev, "step_count": steps, "state": state})).map_err(mcp_internal_error)
}

// ---------------------------------------------------------------------------
// Proof export rendering
// ---------------------------------------------------------------------------

struct ExportObligation {
    id: String,
    theorem_name: String,
    lean_statement: String,
    status: String,
    kind: String,
    failure_lesson: Option<String>,
}

struct ExportAttempt {
    seq: i64,
    obligation_name: String,
    action_type: String,
    detail: String,
    verdict: String,
    created_at: String,
}

fn status_marker(status: &str) -> &'static str {
    match status {
        "proved" => "✅",
        "refuted" => "❌",
        "in_progress" => "🔄",
        "open" => "⏳",
        "abandoned" | "superseded" => "🚫",
        _ => "❔",
    }
}

fn render_proof_export(conn: &Connection, episode_id: &str, format: &str) -> Result<String, McpError> {
    let ep: Option<(String, String, Option<String>, Option<String>, i64, Option<i64>, String, Option<String>)> = conn.query_row(
        "SELECT problem_version_id, state, outcome, termination_reason, step_count, cost_budget_micros, created_at, completed_at
         FROM episodes WHERE id = ?1",
        [episode_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?, row.get(7)?)),
    ).optional().map_err(rs)?;
    let Some((pv_id, state, outcome, term_reason, step_count, budget_left, created_at, completed_at)) = ep else {
        return Err(mcp_invalid_params(format!("unknown episode_id: {}", episode_id)));
    };

    let (source_text, root_statement, fidelity_status, manifest_json, manifest_hash, env_hash):
        (String, String, String, String, String, String) = conn.query_row(
        "SELECT source_problem_text, root_formal_statement, fidelity_status,
                import_manifest_json, import_manifest_hash, environment_hash
         FROM problem_versions WHERE id = ?1",
        [&pv_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?)),
    ).map_err(rs)?;
    // The export must be a receipt of what the verifier actually compiled, not a
    // reconstructed approximation — so the assembled Lean source carries the
    // problem's real, immutable import manifest (never a hardcoded Ring/NormNum
    // stub). A malformed stored manifest should never silently degrade to a lie;
    // fall back to the base set only if parsing fails, and that fallback is itself
    // the historical default, not a guess at the problem's needs.
    let import_manifest: Vec<String> = serde_json::from_str::<Vec<String>>(&manifest_json)
        .unwrap_or_else(|_| vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()]);

    // Verified modules (issue #4): a SubmitModule proves its obligation as a
    // whole. When present, the export renders the EXACT module source —
    // re-assembled deterministically from the stored structured items, so its
    // hash equals the recorded module_source_hash — making the lean export
    // byte-for-byte replayable and the dossier show the development, not just a
    // proof tree.
    #[derive(Deserialize)]
    struct StoredModule { module_items: Vec<LeanModuleItem>, root_theorem: ModuleTheorem }
    struct RenderedModule { source: String, source_hash: String, items: Vec<(i64, String, String)> }
    let mut rendered_modules: Vec<RenderedModule> = Vec::new();
    {
        let ns16 = pv_id.replace('-', "");
        let problem_namespace = format!("ChatDB.P_{}", &ns16[..16.min(ns16.len())]);
        let mut mstmt = conn.prepare(
            "SELECT id, root_statement_hash, module_items_json, module_source_hash
             FROM episode_verified_modules WHERE episode_id = ?1 ORDER BY verified_at ASC",
        ).map_err(rs)?;
        let rows: Vec<(String, String, String, String)> = mstmt
            .query_map([episode_id], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)))
            .map_err(rs)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(rs)?;
        for (mod_id, root_hash, items_json, src_hash) in rows {
            let Ok(stored) = serde_json::from_str::<StoredModule>(&items_json) else { continue };
            let Ok(asm) = assemble_module(&problem_namespace, &root_hash, &stored.module_items, &stored.root_theorem, &import_manifest) else { continue };
            let mut istmt = conn.prepare(
                "SELECT item_order, item_kind, lean_name FROM episode_verified_module_items WHERE module_id = ?1 ORDER BY item_order ASC",
            ).map_err(rs)?;
            let items: Vec<(i64, String, String)> = istmt
                .query_map([&mod_id], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)))
                .map_err(rs)?
                .collect::<Result<Vec<_>, _>>()
                .map_err(rs)?;
            rendered_modules.push(RenderedModule { source: asm.source, source_hash: src_hash, items });
        }
    }

    let mut stmt = conn.prepare(
        "SELECT id, theorem_name, lean_statement, status, kind, failure_lesson
         FROM episode_obligations WHERE episode_id = ?1 ORDER BY created_at ASC",
    ).map_err(rs)?;
    let obligations: Vec<ExportObligation> = stmt.query_map([episode_id], |row| {
        Ok(ExportObligation {
            id: row.get(0)?, theorem_name: row.get(1)?, lean_statement: row.get(2)?,
            status: row.get(3)?, kind: row.get(4)?, failure_lesson: row.get(5)?,
        })
    }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT parent_obligation_id, dependency_obligation_id FROM episode_obligation_edges
         WHERE parent_obligation_id IN (SELECT id FROM episode_obligations WHERE episode_id = ?1)",
    ).map_err(rs)?;
    let edges: Vec<(String, String)> = stmt.query_map([episode_id], |row| Ok((row.get(0)?, row.get(1)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    // Walk trajectory: collect winning proofs per obligation + full attempt history.
    let mut stmt = conn.prepare(
        "SELECT event_sequence_number, event_type, payload_json, created_at FROM trajectory_events
         WHERE episode_id = ?1 ORDER BY event_sequence_number ASC",
    ).map_err(rs)?;
    let events: Vec<(i64, String, String, String)> = stmt.query_map([episode_id], |row| {
        Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
    }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    let name_of = |oid: &Option<String>| -> String {
        oid.as_ref()
            .and_then(|o| obligations.iter().find(|x| &x.id == o))
            .map(|x| x.theorem_name.clone())
            .unwrap_or_else(|| "—".to_string())
    };

    let mut winning_proof: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut attempts: Vec<ExportAttempt> = Vec::new();
    let (mut first_hash, mut last_hash) = (String::new(), String::new());

    for (seq, event_type, payload_json, ev_created) in &events {
        if event_type != "action_committed" {
            continue;
        }
        let Ok(payload) = serde_json::from_str::<serde_json::Value>(payload_json) else { continue };
        let action = &payload["action"];
        let action_type = action["type"].as_str().unwrap_or("?").to_string();
        let obligation_id = payload["obligation_id"].as_str().map(|s| s.to_string());
        let accepted = payload["accepted"].as_bool().unwrap_or(false);
        let disposition = payload["disposition"].as_str().unwrap_or("?");
        let outcome = payload["outcome"].as_str();

        let (detail, verdict) = match action_type.as_str() {
            "solve" => {
                let proof = action["proof_term"].as_str().unwrap_or("").to_string();
                if accepted && outcome == Some("kernel_pass") {
                    if let Some(oid) = &obligation_id {
                        winning_proof.insert(oid.clone(), proof.clone());
                    }
                }
                let verdict = if disposition != "accepted" {
                    format!("⚠️ {}", disposition)
                } else if outcome == Some("kernel_pass") {
                    "✅ kernel_pass".to_string()
                } else {
                    format!("❌ {}", outcome.unwrap_or("kernel_fail"))
                };
                (format!("`{}`", proof.trim().replace('\n', " ; ")), verdict)
            }
            "decompose" => {
                let subs: Vec<String> = action["sub_lemmas"].as_array().map(|a| {
                    a.iter().filter_map(|v| v.as_str()).map(|s| format!("`{}`", s)).collect()
                }).unwrap_or_default();
                (format!("split into {}", subs.join(" and ")), if accepted { "✅ accepted".to_string() } else { format!("⚠️ {}", disposition) })
            }
            "give_up" => ("gave up".to_string(), "🏳️".to_string()),
            other => (other.to_string(), disposition.to_string()),
        };

        attempts.push(ExportAttempt {
            seq: *seq,
            obligation_name: name_of(&obligation_id),
            action_type,
            detail,
            verdict,
            created_at: ev_created.clone(),
        });
    }

    // Hash chain endpoints for the integrity line.
    let chain: Option<(String, String, i64)> = conn.query_row(
        "SELECT (SELECT event_hash FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number ASC LIMIT 1),
                (SELECT event_hash FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number DESC LIMIT 1),
                (SELECT COUNT(*) FROM trajectory_events WHERE episode_id = ?1)",
        [episode_id],
        |row| Ok((row.get::<_, Option<String>>(0)?.unwrap_or_default(), row.get::<_, Option<String>>(1)?.unwrap_or_default(), row.get(2)?)),
    ).optional().map_err(rs)?;
    if let Some((f, l, _)) = &chain {
        first_hash = f.clone();
        last_hash = l.clone();
    }
    let event_count = chain.map(|(_, _, n)| n).unwrap_or(0);

    // Assembled Lean source: proved obligations, children before parents (leaves
    // carry no unproved deps by construction), root last.
    fn children_of<'a>(pid: &str, obligations: &'a [ExportObligation], edges: &[(String, String)]) -> Vec<&'a ExportObligation> {
        edges.iter().filter(|(p, _)| p == pid)
            .filter_map(|(_, c)| obligations.iter().find(|o| &o.id == c))
            .collect()
    }
    fn push_postorder<'a>(
        o: &'a ExportObligation,
        obligations: &'a [ExportObligation],
        edges: &[(String, String)],
        out: &mut Vec<&'a ExportObligation>,
    ) {
        for c in children_of(&o.id, obligations, edges) {
            push_postorder(c, obligations, edges, out);
        }
        if !out.iter().any(|x| x.id == o.id) {
            out.push(o);
        }
    }
    let root = obligations.iter().find(|o| o.kind == "root");
    let mut lean_order: Vec<&ExportObligation> = Vec::new();
    if let Some(r) = root {
        push_postorder(r, &obligations, &edges, &mut lean_order);
    }
    // Orphans (obligations not reachable from root) still deserve to show up.
    for o in &obligations {
        if !lean_order.iter().any(|x| x.id == o.id) {
            lean_order.insert(0, o);
        }
    }

    let mut lean_src = String::new();
    for module in &import_manifest {
        lean_src.push_str(&format!("import {}\n", module));
    }
    lean_src.push('\n');
    for o in &lean_order {
        if o.status != "proved" {
            continue;
        }
        let proof = winning_proof.get(&o.id).cloned()
            .unwrap_or_else(|| "  sorry -- proof term not recorded in trajectory".to_string());
        lean_src.push_str(&format!("theorem {} : {} := by\n{}\n\n", o.theorem_name, o.lean_statement, proof.trim_end()));
    }

    if format == "lean" {
        // A verified module is the exact, replayable artifact — prefer it over the
        // theorem-by-theorem reconstruction when one exists.
        if !rendered_modules.is_empty() {
            return Ok(rendered_modules.iter().map(|m| m.source.clone()).collect::<Vec<_>>().join("\n\n"));
        }
        return Ok(lean_src);
    }

    // Markdown dossier. Proof soundness (did Lean verify this exact formal
    // statement?) and statement fidelity (does that formal statement represent
    // the source problem?) are independent claims — a kernel-verified root of a
    // weakened or vacuous formalization must never render as if it certified the
    // source claim. Only outcome == "certified" (which requires BOTH) gets the
    // unqualified CERTIFIED headline.
    let is_certified = outcome.as_deref() == Some("certified");
    let is_kernel_verified_only = outcome.as_deref() == Some("kernel_verified");
    let training_eligible = fidelity_status == "verified";

    let mut md = String::new();
    let headline_marker = match outcome.as_deref() {
        Some("certified") => "✅ CERTIFIED",
        Some("kernel_verified") if fidelity_status == "rejected" => "⚠️ FORMAL PROOF VALID, STATEMENT FIDELITY REJECTED",
        Some("kernel_verified") => "⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED",
        Some("refuted") => "❌ REFUTED",
        Some("gave_up") => "🏳️ GAVE UP",
        Some(other) => other,
        None => "🔄 IN PROGRESS",
    };
    md.push_str(&format!("# {} — {}\n\n", headline_marker, source_text.trim()));

    if is_kernel_verified_only {
        md.push_str(&format!(
            "> This proof establishes:\n>\n> `{}`\n>\n> It does {}certify the source claim above.\n\n",
            root_statement,
            if fidelity_status == "rejected" { "**not** " } else { "**not yet** " },
        ));
    }

    md.push_str(&format!("**Root goal (formal):** `{}`\n\n", root_statement));

    // The three independent claims, always shown together so a reader can never
    // mistake one for the others.
    let proof_soundness = match outcome.as_deref() {
        Some("certified") | Some("kernel_verified") => "VERIFIED",
        Some("refuted") => "REFUTED",
        None => "PENDING",
        Some(_) => "INCOMPLETE",
    };
    let fidelity_display = match fidelity_status.as_str() {
        "verified" => "VERIFIED",
        "rejected" => "REJECTED",
        "revoked" => "REVOKED",
        "attested" => "ATTESTED (unsafe_dev_attestation — not reviewed)",
        _ => "UNVERIFIED",
    };
    let promotion_display = if is_certified { "PROMOTED" } else { "BLOCKED" };
    md.push_str(&format!(
        "| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |\n|---|---|---|---|\n| {} | {} | {} | {} |\n\n",
        proof_soundness, fidelity_display, promotion_display,
        if training_eligible { "eligible" } else { "QUARANTINED" },
    ));

    md.push_str(&format!(
        "| episode | state | steps | budget left (μ$) | started | finished |\n|---|---|---|---|---|---|\n| `{}` | {}{} | {} | {} | {} | {} |\n\n",
        episode_id, state,
        term_reason.map(|r| format!(" ({})", r)).unwrap_or_default(),
        step_count,
        budget_left.map(|b| b.to_string()).unwrap_or_else(|| "—".to_string()),
        &created_at[..created_at.len().min(19)],
        completed_at.map(|c| c[..c.len().min(19)].to_string()).unwrap_or_else(|| "—".to_string()),
    ));

    md.push_str("## Proof tree\n\n");
    fn render_tree(
        o: &ExportObligation,
        obligations: &[ExportObligation],
        edges: &[(String, String)],
        depth: usize,
        md: &mut String,
    ) {
        let indent = "  ".repeat(depth);
        md.push_str(&format!("{}- {} **{}** : `{}`\n", indent, status_marker(&o.status), o.theorem_name, o.lean_statement));
        if let Some(lesson) = &o.failure_lesson {
            if o.status != "proved" {
                md.push_str(&format!("{}  - 💡 last lesson: {}\n", indent, lesson.trim().replace('\n', " ")));
            }
        }
        for c in children_of(&o.id, obligations, edges) {
            render_tree(c, obligations, edges, depth + 1, md);
        }
    }
    match root {
        Some(r) => render_tree(r, &obligations, &edges, 0, &mut md),
        None => md.push_str("*(no obligations seeded yet)*\n"),
    }

    // A verified module is a structured development, not a single proof term —
    // show its declaration manifest and the exact assembled source, so the dossier
    // reflects the module, not only a proof tree.
    if !rendered_modules.is_empty() {
        md.push_str("\n## Verified module\n\n");
        for (mi, m) in rendered_modules.iter().enumerate() {
            if rendered_modules.len() > 1 {
                md.push_str(&format!("### Module {}\n\n", mi + 1));
            }
            md.push_str(&format!("`module_source_hash: {}`\n\n", m.source_hash));
            md.push_str("| # | kind | name |\n|---|---|---|\n");
            for (order, kind, name) in &m.items {
                md.push_str(&format!("| {} | {} | `{}` |\n", order, kind, name));
            }
            md.push_str(&format!("\n```lean\n{}\n```\n", m.source.trim_end()));
        }
    }

    md.push_str("\n## The proof, assembled\n\n");
    if !rendered_modules.is_empty() {
        md.push_str("*(see Verified module above — this episode was proved as a structured module)*\n");
    } else if lean_order.iter().any(|o| o.status == "proved") {
        md.push_str(&format!("```lean\n{}```\n", lean_src));
    } else {
        md.push_str("*(nothing proved yet)*\n");
    }

    md.push_str("\n## How it went — every attempt, in order\n\n");
    if attempts.is_empty() {
        md.push_str("*(no actions taken yet)*\n");
    } else {
        md.push_str("| # | obligation | action | detail | verdict |\n|---|---|---|---|---|\n");
        for a in &attempts {
            md.push_str(&format!("| {} | `{}` | {} | {} | {} |\n", a.seq, a.obligation_name, a.action_type, a.detail.replace('|', "\\|"), a.verdict));
        }
    }

    // Verification context: the export is a receipt, so it must state exactly
    // which pinned environment and import manifest the kernel checked this proof
    // under. These are the problem_version's immutable values — the same ones the
    // gateway used — not a reconstruction. A reader can pin a third-party
    // toolchain to `environment_hash` and re-derive `import_manifest_hash` from
    // the listed manifest to confirm they are re-verifying the same artifact.
    md.push_str("\n## Verification context\n\n");
    md.push_str(&format!("- **Environment hash:** `{}`\n", env_hash));
    md.push_str(&format!("- **Import manifest hash:** `{}`\n", manifest_hash));
    md.push_str(&format!("- **Import manifest:** `{}`\n", manifest_json));

    md.push_str(&format!(
        "\n## Integrity\n\n{} hash-chained trajectory events, `{}…` → `{}…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.\n",
        event_count,
        &first_hash[..first_hash.len().min(12)],
        &last_hash[..last_hash.len().min(12)],
    ));

    Ok(md)
}

// ---------------------------------------------------------------------------
// Server
// ---------------------------------------------------------------------------

pub struct ChatDbMcp {
    pub conn: Arc<Mutex<Connection>>,
    pub gateway: Box<dyn LeanGateway + Send + Sync>,
    pub lean_available: bool,
    /// The server's own read of what it actually verifies against — the only
    /// trustworthy source for this, since a client can't see the installed
    /// toolchain. `None` when lean-checker isn't set up (`lean_available == false`
    /// implies this is `None`, but the manifest can also be absent independently).
    pub lean_environment: Option<chatdb_proof_core::lean::LeanEnvironmentInfo>,
}

impl ChatDbMcp {
    pub fn new(conn: Arc<Mutex<Connection>>, lean_project_path: PathBuf, elan_bin_path: PathBuf) -> Self {
        let lean_available = elan_bin_path.join("lake.exe").exists()
            && (lean_project_path.join("lakefile.toml").exists() || lean_project_path.join("lakefile.lean").exists());
        let lean_environment = chatdb_proof_core::lean::detect_environment(&lean_project_path);
        let gateway = Box::new(RealLeanGateway::new(lean_project_path, elan_bin_path));
        Self { conn, gateway, lean_available, lean_environment }
    }
}

pub fn init_db(conn: &Connection) -> rusqlite::Result<()> {
    schema_v1::initialize_v1_db(conn)
}

impl ServerHandler for ChatDbMcp {
    fn get_info(&self) -> ServerInfo {
        ServerInfo::new(ServerCapabilities::default())
            .with_server_info(Implementation::new("chatdb-mcp", "0.2.5"))
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, McpError> {
        let tools = vec![
            make_tool::<EnvironmentDescribeArgs>("environment_describe", "Return environment version, supported protocol, tool schemas, capabilities"),
            make_tool::<ProblemCreateArgs>("problem_create", "Register a new problem version (source text + root formal statement). fidelity_status starts 'unreviewed' — proving requires either a real problem_submit_fidelity_review or the honestly-named unsafe_dev_attestation=true (which can reach outcome=kernel_verified but never 'certified')"),
            make_tool::<ProblemSubmitFidelityReviewArgs>("problem_submit_fidelity_review", "Record an evidence-backed determination of whether a problem's formal statement represents its source text. Requires the CURRENT source/statement/rendering hashes (recomputed server-side; mismatches are rejected as stale). decision='verified' is the ONLY path to outcome='certified' and problem state COMPLETE; 'rejected' blocks it. This is a review record, not a flag flip — proof soundness (Lean kernel) and statement fidelity (this tool) are independent claims"),
            make_tool::<ProblemListArgs>("problem_list", "List known problem versions (id, state, fidelity_status, root statement)"),
            make_tool::<EpisodeCreateArgs>("episode_create", "Initialize an episode from a problem version whose fidelity_status is 'verified' or 'attested' + config. Returns first observation"),
            make_tool::<EpisodeResetArgs>("episode_reset", "Nondestructive: creates new episode from existing config, sets parent_episode_id"),
            make_tool::<EpisodeObserveArgs>("episode_observe", "Get the active observation and pending action request"),
            make_tool::<AttemptClaimArgs>("attempt_claim", "Claim a pending action request to obtain the action_attempt_id + claim_token required by episode_step. Idempotent on idempotency_key"),
            make_tool::<EpisodeStepArgs>("episode_step", "Submit a typed action against a claimed attempt. `action` is internally tagged — exactly one of: {\"type\":\"solve\",\"proof_term\":\"  norm_num\"} (Lean tactic block proving the target obligation), {\"type\":\"decompose\",\"sub_lemmas\":[\"<lean statement>\", ...]} (split the obligation into child lemmas), {\"type\":\"give_up\"} (terminate the episode). `expected_revision` must equal the episode_revision advertised on the action_request. Settles any lease attached to the attempt atomically"),
            make_tool::<EpisodeStatusArgs>("episode_status", "Retrieve current episode state, revision, budget, step count"),
            make_tool::<EpisodeCloseArgs>("episode_close", "Gracefully truncate an episode"),
            make_tool::<ModelCallReserveArgs>("model_call_reserve", "Reserve a budget lease for a model call"),
            make_tool::<ModelCallSettleArgs>("model_call_settle", "Settle or release a lease without submitting an action (provider failure, cancellation)"),
            make_tool::<TrajectoryExportArgs>("trajectory_export", "Export trajectory with pagination (cursor + page_size)"),
            make_tool::<EpisodeReplayArgs>("episode_replay", "Re-execute typed actions through canonical reducer with Lean re-verification"),
            make_tool::<ProofExportArgs>("proof_export", "Render an episode as a human-readable proof dossier: proof tree with statuses, assembled Lean source (dependencies before root), full attempt history including failures, and the hash-chain integrity line. format: \"markdown\" (default) | \"lean\" (bare assembled source)"),
            make_tool::<LeanDeclarationLookupArgs>("lean_declaration_lookup", "Check whether declaration names resolve — WITHOUT changing proof strategy first. An 'unknown identifier' error from episode_step only ever proves a name didn't resolve under the exact import manifest that attempt used; it never proves the name is absent from the pinned Mathlib. By default this only checks under the problem's own manifest (fast, a few seconds) and returns 'not_available_under_current_manifest' if it fails to resolve — that result alone does NOT mean the name is absent from the library, only that it needs an import. Pass deep_check=true to additionally check under the full Mathlib umbrella and distinguish 'not_in_current_import_scope' (add an import to problem_imports, see problem_create) from genuinely 'unknown_declaration' (misspelled, wrong namespace, or absent); deep_check loads all of Mathlib and reliably takes 15-40+ seconds. Epistemic rule: before concluding an API is unavailable, call this tool with deep_check=true — do not infer library capability from one elaboration failure or from a fast-path result alone"),
        ];
        Ok(ListToolsResult::with_all_items(tools))
    }

    async fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CallToolResult, McpError> {
        let args_map = request.arguments.unwrap_or_default();
        let args_val = serde_json::Value::Object(args_map);

        match request.name.as_ref() {
            "environment_describe" => {
                let action_schema = schemars::schema_for!(TypedAction);
                let res = serde_json::json!({
                    "environment_version": "0.2.5",
                    "protocol_version": "2025-11-25",
                    "supported_roles": ["prover"],
                    "schema_versions": {
                        "observation_schema_version": "1.0",
                        "action_schema_version": "1.0",
                        "reward_policy_version": "1.0"
                    },
                    "lean_gateway": if self.lean_available { "ready" } else { "unavailable" },
                    "lean_environment": self.lean_environment.as_ref().map(|e| serde_json::json!({
                        "descriptor": e.descriptor, "hash": e.hash
                    })),
                    "action_schema": action_schema,
                    "action_examples": [
                        {"type": "solve", "proof_term": "  norm_num"},
                        {"type": "decompose", "sub_lemmas": ["n + 0 = n", "0 + n = n"]},
                        {"type": "submit_module", "module_items": [
                            {"item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n"}
                        ], "root_theorem": {"name": "root", "statement": "double 2 = 4", "proof_term": "  rfl"}},
                        {"type": "give_up"}
                    ],
                    "submit_module_boundary": "The server assembles the Lean file: it owns imports, the ChatDB.P_<problem> namespace, and server set_options. Clients send structured items only — never raw import/namespace/end/set_option lines, and never axiom/opaque/unsafe/instance declarations. Every name is sanitized to a single namespace-local identifier. The root_theorem.statement must canonical-hash to the problem's registered root_statement_hash. Either the whole module passes the kernel and is recorded, or nothing enters the trusted namespace.",
                    "prover_loop": "problem_create -> problem_submit_fidelity_review (or unsafe_dev_attestation=true for dev use) -> episode_create -> episode_observe -> attempt_claim -> episode_step(action, expected_revision = action_request.episode_revision) -> repeat observe/claim/step until outcome is set",
                    "epistemic_rules": [
                        "An 'unknown_declaration'/'unknown identifier' result under the active import manifest establishes ONLY that the name didn't resolve under that exact import closure. It does NOT establish that the declaration is absent from the pinned library. Before concluding an API is unavailable, call lean_declaration_lookup — do not infer a global capability limit from one local elaboration failure.",
                        "lean_declaration_lookup defaults to a fast (few-second) check against only the problem's own import manifest, returning 'not_available_under_current_manifest' on failure — that status by itself does not prove absence from the library. Pass deep_check=true (15-40+ seconds, loads the full Mathlib umbrella) to get a conclusive 'not_in_current_import_scope' vs 'unknown_declaration' verdict before concluding a declaration is genuinely unavailable.",
                        "A prior model's proof (from another session, another model, a paper, etc.) is a candidate artifact, not evidence of correctness, until it passes THIS pinned verifier. Do not skip verification because a candidate 'looks complete'."
                    ]
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_create" => {
                let args: ProblemCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.source_problem_text.trim().is_empty() || args.root_formal_statement.trim().is_empty() {
                    return Err(mcp_invalid_params("source_problem_text and root_formal_statement must be non-empty"));
                }

                // The gateway wraps the root statement as `theorem <name> : <statement> := by ...`.
                // A declaration-shaped input would nest to `theorem root_theorem : theorem foo : ...`,
                // which can never elaborate — reject it at the source instead of at solve time.
                let first_word = args.root_formal_statement.trim().split_whitespace().next().unwrap_or("");
                if matches!(first_word, "theorem" | "lemma" | "example" | "def" | "abbrev" | "instance") {
                    return Err(mcp_invalid_params(format!(
                        "root_formal_statement must be a bare proposition (what goes AFTER the ':' in a theorem), not a '{}' declaration — e.g. \"∀ a b : ℕ, Even a → Even b → Even (a + b)\" or \"1 + 1 = 2\"",
                        first_word
                    )));
                }

                let extra_imports = args.problem_imports.unwrap_or_default();
                if extra_imports.len() > 50 {
                    return Err(mcp_invalid_params("problem_imports: at most 50 modules per problem"));
                }
                for m in &extra_imports {
                    if !valid_lean_module_path(m) {
                        return Err(mcp_invalid_params(format!(
                            "problem_imports entry {:?} is not a valid Lean module path — must be dot-separated identifier segments only (letters, digits, underscore), no whitespace, comments, or command syntax",
                            m
                        )));
                    }
                }
                if !extra_imports.is_empty() {
                    self.gateway.validate_import_manifest(&extra_imports)
                        .map_err(|e| mcp_invalid_params(format!("problem_imports rejected — {}", e)))?;
                }
                let mut import_manifest: Vec<String> = BASE_IMPORT_MANIFEST.iter().map(|s| s.to_string()).collect();
                import_manifest.extend(extra_imports);
                let import_manifest_json = serde_json::to_string(&import_manifest).unwrap();
                let import_manifest_hash = canonical_hash(&import_manifest).map_err(mcp_internal_error)?;

                let pv_id = Uuid::new_v4();
                let source_hash = canonical_hash(&args.source_problem_text).map_err(mcp_internal_error)?;
                let root_hash = canonical_hash(&args.root_formal_statement).map_err(mcp_internal_error)?;
                let rendering = args.normalized_root_rendering.unwrap_or_else(|| args.root_formal_statement.clone());
                // The server, not the client, is the source of truth for what Lean
                // environment actually verifies proofs — a client-supplied hash was
                // almost always omitted and silently defaulted to a meaningless
                // placeholder, which made `replay`'s determinism claim untraceable
                // to any specific toolchain/Mathlib pin. Auto-detect; still allow an
                // explicit override for advanced/cross-environment bookkeeping.
                let env_hash = args.environment_hash
                    .or_else(|| self.lean_environment.as_ref().map(|e| e.hash.clone()))
                    .unwrap_or_else(|| "lean-gateway-unavailable".to_string());
                let metadata = args.metadata_json.unwrap_or_else(|| "{}".to_string());
                serde_json::from_str::<serde_json::Value>(&metadata)
                    .map_err(|e| mcp_invalid_params(format!("metadata_json is not valid JSON: {}", e)))?;

                // 'attested' permits proving (episode_create checks for this) but can
                // NEVER reach 'verified' by itself — only problem_submit_fidelity_review
                // can do that, and the DB CHECK on state='COMPLETE' enforces it even if
                // application logic has a bug. No path here ever writes 'verified'.
                let (fidelity_status, state) = if args.unsafe_dev_attestation {
                    ("attested", "PROVING")
                } else {
                    ("unreviewed", "CREATED")
                };
                let fidelity_approval_id = if args.unsafe_dev_attestation { Some(Uuid::new_v4().to_string()) } else { None };

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                tx.execute(
                    "INSERT INTO problem_versions (
                        id, source_problem_text, source_problem_hash, source_metadata_json,
                        root_formal_statement, root_statement_hash, normalized_root_rendering,
                        environment_hash, import_manifest_json, import_manifest_hash,
                        fidelity_status, fidelity_method, fidelity_approval_id,
                        state, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, 'manual', ?12, ?13, ?14)",
                    (
                        pv_id.to_string(), &args.source_problem_text, &source_hash, &metadata,
                        &args.root_formal_statement, &root_hash, &rendering,
                        &env_hash, &import_manifest_json, &import_manifest_hash,
                        fidelity_status, &fidelity_approval_id, state,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "problem_version_id": pv_id.to_string(),
                    "fidelity_status": fidelity_status,
                    "state": state,
                    "environment_hash": env_hash,
                    "import_manifest": import_manifest,
                    "import_manifest_hash": import_manifest_hash,
                    // A fidelity reviewer must submit these back unchanged in
                    // problem_submit_fidelity_review — the server recomputes and
                    // compares them independently, so a client can copy these values
                    // rather than needing to reimplement the canonical hash algorithm.
                    "source_problem_hash": source_hash,
                    "root_statement_hash": root_hash,
                    "rendering_hash": canonical_hash(&rendering).map_err(mcp_internal_error)?,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_submit_fidelity_review" => {
                let args: ProblemSubmitFidelityReviewArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let current: Option<(String, String, String)> = tx.query_row(
                    "SELECT source_problem_hash, root_statement_hash, normalized_root_rendering FROM problem_versions WHERE id = ?1",
                    [&args.problem_version_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                ).optional().map_err(rs)?;
                let Some((cur_source_hash, cur_root_hash, cur_rendering)) = current else {
                    return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id)));
                };
                let cur_rendering_hash = canonical_hash(&cur_rendering).map_err(mcp_internal_error)?;

                // A review can only authorize the EXACT text it reviewed. Recompute
                // independently — never trust the submitted hashes — and reject if
                // the problem has changed (or the review targeted a different one)
                // since the evidence was gathered. This is the anti-staleness check
                // the fix plan calls "hash invalidation."
                if args.source_problem_hash != cur_source_hash
                    || args.root_statement_hash != cur_root_hash
                    || args.rendering_hash != cur_rendering_hash
                {
                    return Err(mcp_invalid_params(
                        "submitted hashes do not match the problem_version's CURRENT source/statement/rendering — \
                         the problem changed since this review's evidence was gathered, or the review targeted a \
                         different problem_version_id. Re-review the current text and resubmit."
                    ));
                }

                let (decision_str, new_status) = match args.decision {
                    FidelityDecision::Verified => ("verified", "verified"),
                    FidelityDecision::Rejected => ("rejected", "rejected"),
                };

                serde_json::from_str::<serde_json::Value>(&args.evidence_json)
                    .map_err(|e| mcp_invalid_params(format!("evidence_json is not valid JSON: {}", e)))?;

                let review_id = Uuid::new_v4().to_string();
                tx.execute(
                    "INSERT INTO problem_fidelity_reviews (
                        id, problem_version_id, source_problem_hash, root_statement_hash, normalized_rendering_hash,
                        decision, method, approver_id, rubric_version, evidence_json, notes, signature, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13)",
                    (
                        &review_id, &args.problem_version_id, &cur_source_hash, &cur_root_hash, &cur_rendering_hash,
                        decision_str, &args.method, &args.approver_id, &args.rubric_version, &args.evidence_json,
                        &args.notes, &args.signature, Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;

                tx.execute(
                    "UPDATE problem_versions SET fidelity_status = ?1, fidelity_method = ?2, fidelity_approval_id = ?3 WHERE id = ?4",
                    (new_status, &args.method, &review_id, &args.problem_version_id),
                ).map_err(rs)?;

                // A verified review is what actually unlocks proving for a problem
                // that was never touched by the dev-bypass path (still 'CREATED').
                if new_status == "verified" {
                    tx.execute(
                        "UPDATE problem_versions SET state = 'PROVING' WHERE id = ?1 AND state = 'CREATED'",
                        [&args.problem_version_id],
                    ).map_err(rs)?;
                }

                // A review landing 'verified' after the root was already
                // kernel-verified (episode outcome kernel_verified, problem state
                // FIDELITY_REVIEW) completes the promotion retroactively — this is
                // the only place 'COMPLETE' / 'certified' get assigned after the fact.
                if new_status == "verified" {
                    let pending_episodes: Vec<String> = {
                        let mut s = tx.prepare(
                            "SELECT id FROM episodes WHERE problem_version_id = ?1 AND outcome = 'kernel_verified'"
                        ).map_err(rs)?;
                        s.query_map([&args.problem_version_id], |row| row.get::<_, String>(0)).map_err(rs)?
                            .collect::<Result<Vec<_>, _>>().map_err(rs)?
                    };
                    for ep_id in &pending_episodes {
                        tx.execute(
                            "UPDATE episodes SET outcome = 'certified' WHERE id = ?1",
                            [ep_id],
                        ).map_err(rs)?;
                    }
                    if !pending_episodes.is_empty() {
                        tx.execute(
                            "UPDATE problem_versions SET state = 'COMPLETE' WHERE id = ?1",
                            [&args.problem_version_id],
                        ).map_err(rs)?;
                    }
                }

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "problem_version_id": args.problem_version_id,
                    "fidelity_review_id": review_id,
                    "decision": decision_str,
                    "fidelity_status": new_status,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_list" => {
                let args: ProblemListArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let limit = args.limit.unwrap_or(50).clamp(1, 500);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, state, fidelity_status, root_formal_statement, created_at,
                            source_problem_hash, root_statement_hash, normalized_root_rendering
                     FROM problem_versions ORDER BY created_at DESC LIMIT ?1"
                ).map_err(rs)?;
                let rows = stmt.query_map([limit], |row| {
                    let rendering: String = row.get(7)?;
                    Ok((serde_json::json!({
                        "problem_version_id": row.get::<_, String>(0)?,
                        "state": row.get::<_, String>(1)?,
                        "fidelity_status": row.get::<_, String>(2)?,
                        "root_formal_statement": row.get::<_, String>(3)?,
                        "created_at": row.get::<_, String>(4)?,
                        "source_problem_hash": row.get::<_, String>(5)?,
                        "root_statement_hash": row.get::<_, String>(6)?,
                    }), rendering))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let rows: Vec<serde_json::Value> = rows.into_iter().map(|(mut v, rendering): (serde_json::Value, String)| {
                    let rendering_hash = canonical_hash(&rendering).unwrap_or_default();
                    v.as_object_mut().unwrap().insert("rendering_hash".to_string(), serde_json::Value::String(rendering_hash));
                    v
                }).collect();

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&rows).unwrap())]))
            }
            "episode_create" => {
                let args: EpisodeCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let problem_uuid = Uuid::parse_str(&args.problem_version_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid problem Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let fidelity_status: Option<String> = tx.query_row(
                    "SELECT fidelity_status FROM problem_versions WHERE id = ?1",
                    [problem_uuid.to_string()],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                match fidelity_status.as_deref() {
                    None => return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id))),
                    Some("verified") | Some("attested") => {}
                    Some(other) => return Err(mcp_invalid_params(format!(
                        "problem_version {} has fidelity_status={}; proving requires 'verified' (call problem_submit_fidelity_review) \
                         or 'attested' (problem_create's unsafe_dev_attestation=true — training-quarantined)",
                        args.problem_version_id, other
                    ))),
                }

                let episode_uuid = lifecycle::episode_create(&tx, problem_uuid).map_err(rs)?;

                if let Some(ms) = args.max_steps {
                    tx.execute("UPDATE episodes SET max_steps = ?1 WHERE id = ?2", (ms, episode_uuid.to_string())).map_err(rs)?;
                }
                if let Some(cb) = args.cost_budget_micros {
                    tx.execute("UPDATE episodes SET cost_budget_micros = ?1 WHERE id = ?2", (cb, episode_uuid.to_string())).map_err(rs)?;
                }

                let next_req_id = lifecycle::advance(&tx, episode_uuid).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &episode_uuid.to_string())?;
                let env_hash = episode_env_hash(&tx, &episode_uuid.to_string()).map_err(rs)?;
                trajectories::record_event(
                    &tx, episode_uuid, "episode_created", "GENESIS", &progress_hash, &env_hash,
                    &serde_json::json!({"problem_version_id": args.problem_version_id, "max_steps": args.max_steps, "cost_budget_micros": args.cost_budget_micros}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [episode_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(rs)?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": episode_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_reset" => {
                let args: EpisodeResetArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let old_ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let exists: Option<i64> = tx.query_row(
                    "SELECT 1 FROM episodes WHERE id = ?1", [old_ep_uuid.to_string()], |row| row.get(0)
                ).optional().map_err(rs)?;
                if exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                }

                let new_ep_uuid = lifecycle::episode_reset(&tx, old_ep_uuid).map_err(rs)?;

                let next_req_id = lifecycle::advance(&tx, new_ep_uuid).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &new_ep_uuid.to_string())?;
                let env_hash = episode_env_hash(&tx, &new_ep_uuid.to_string()).map_err(rs)?;
                trajectories::record_event(
                    &tx, new_ep_uuid, "episode_created", "GENESIS", &progress_hash, &env_hash,
                    &serde_json::json!({"reset_from": args.episode_id}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [new_ep_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(rs)?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": new_ep_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_observe" => {
                let args: EpisodeObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                attempts::attempt_recover_expired(&tx).map_err(rs)?;
                attempts::request_recover_expired(&tx, ep_uuid).map_err(rs)?;
                // If the only pending request just lapsed, advance() notices there's
                // no live one and mints a fresh one against the same target obligation.
                lifecycle::advance(&tx, ep_uuid).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let active_req_id_str: Option<String> = conn.query_row(
                    "SELECT id FROM action_requests WHERE episode_id = ?1 AND status IN ('pending', 'claimed') ORDER BY created_at DESC LIMIT 1",
                    [args.episode_id.clone()],
                    |row| row.get(0),
                ).optional().map_err(rs)?;

                if let Some(req_id_str) = active_req_id_str {
                    let req_id = Uuid::parse_str(&req_id_str).unwrap();
                    let action_request = query_action_request(&conn, req_id).map_err(rs)?;

                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req_id_str],
                        |row| row.get(0),
                    ).map_err(rs)?;

                    let observation = obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null);

                    let res = serde_json::json!({
                        "action_request": action_request,
                        "observation": observation
                    });
                    Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
                } else {
                    let episode_exists: Option<String> = conn.query_row(
                        "SELECT state FROM episodes WHERE id = ?1", [args.episode_id.clone()], |row| row.get(0)
                    ).optional().map_err(rs)?;
                    match episode_exists {
                        None => Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                        Some(state) => Err(mcp_invalid_params(format!("No active request (episode state = {})", state))),
                    }
                }
            }
            "attempt_claim" => {
                let args: AttemptClaimArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;
                let req_uuid = Uuid::parse_str(&args.action_request_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid action_request Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                attempts::attempt_recover_expired(&tx).map_err(rs)?;
                attempts::request_recover_expired(&tx, ep_uuid).map_err(rs)?;

                let ep_state: Option<String> = tx.query_row(
                    "SELECT state FROM episodes WHERE id = ?1", [&args.episode_id], |row| row.get(0)
                ).optional().map_err(rs)?;
                match ep_state.as_deref() {
                    None => return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                    Some("terminated") | Some("truncated") => return Err(mcp_invalid_params(format!(
                        "episode {} is {} — create a new episode (episode_create) or fork it (episode_reset)",
                        args.episode_id, ep_state.as_deref().unwrap()
                    ))),
                    _ => {}
                }

                let claim = attempts::attempt_claim(&tx, ep_uuid, req_uuid, &args.idempotency_key, args.expected_revision)
                    .map_err(rs)?;

                match claim {
                    Some(c) => {
                        tx.commit().map_err(rs)?;
                        let res = serde_json::json!({
                            "action_attempt_id": c.attempt_id.to_string(),
                            "claim_token": c.claim_token,
                        });
                        Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
                    }
                    None => {
                        // Diagnose exactly why the claim was refused instead of a bare error.
                        let req_info: Option<(String, Option<String>)> = tx.query_row(
                            "SELECT status, expiration_at FROM action_requests WHERE id = ?1 AND episode_id = ?2",
                            (&args.action_request_id, &args.episode_id),
                            |row| Ok((row.get(0)?, row.get(1)?)),
                        ).optional().map_err(rs)?;

                        let key_used: Option<String> = tx.query_row(
                            "SELECT status FROM action_attempts WHERE episode_id = ?1 AND idempotency_key = ?2",
                            (&args.episode_id, &args.idempotency_key),
                            |row| row.get(0),
                        ).optional().map_err(rs)?;

                        let msg = if let Some(attempt_status) = key_used {
                            format!(
                                "idempotency_key '{}' was already used by an attempt now in state '{}' — retry with a fresh idempotency_key",
                                args.idempotency_key, attempt_status
                            )
                        } else {
                            match req_info {
                                None => format!("unknown action_request_id {} for episode {} — call episode_observe for the current request", args.action_request_id, args.episode_id),
                                Some((status, exp)) => match status.as_str() {
                                    "claimed" => "request is currently claimed by another attempt (claims auto-expire ~5 min after issue and are recovered on the next observe/claim) — call episode_observe and retry".to_string(),
                                    "fulfilled" => "request was already fulfilled by a committed step — call episode_observe for the next request".to_string(),
                                    "expired" | "cancelled" => format!(
                                        "action request {}{} — call episode_observe for the current request",
                                        status,
                                        exp.map(|e| format!(" (expired at {})", e)).unwrap_or_default()
                                    ),
                                    other => format!("request is in state '{}' and not claimable — call episode_observe", other),
                                },
                            }
                        };
                        Err(mcp_invalid_params(msg))
                    }
                }
            }
            "episode_step" => {
                let args: EpisodeStepArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!(
                        "Invalid params: {}. `action` must be one of: {{\"type\":\"solve\",\"proof_term\":\"  norm_num\"}} | {{\"type\":\"decompose\",\"sub_lemmas\":[\"...\"]}} | {{\"type\":\"submit_module\",\"module_items\":[{{\"item_kind\":\"def\",\"name\":\"f\",\"type_signature\":\"Nat → Nat\",\"body\":\"fun n => n\"}}],\"root_theorem\":{{\"name\":\"root\",\"statement\":\"<must hash-match registered root>\",\"proof_term\":\"  rfl\"}}}} | {{\"type\":\"give_up\"}} (see environment_describe.action_schema)", e
                    )))?;

                if args.cost_micros < 0 {
                    return Err(mcp_invalid_params("cost_micros must be >= 0"));
                }

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let attempt_uuid = Uuid::parse_str(&args.action_attempt_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid attempt Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                attempts::attempt_recover_expired(&tx).map_err(rs)?;

                // Capture what this attempt targets before attempt_commit mutates state,
                // so the trajectory payload reflects what was actually acted on.
                let action_request_id: Option<String> = tx.query_row(
                    "SELECT action_request_id FROM action_attempts WHERE id = ?1",
                    [args.action_attempt_id.clone()],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let target_obligation_id: Option<String> = match &action_request_id {
                    Some(rid) => tx.query_row(
                        "SELECT target_obligation_id FROM action_requests WHERE id = ?1",
                        [rid], |row| row.get::<_, Option<String>>(0),
                    ).optional().map_err(rs)?.flatten(),
                    None => None,
                };
                let state_hash_before: String = match &action_request_id {
                    Some(rid) => tx.query_row(
                        "SELECT state_hash_before FROM action_requests WHERE id = ?1",
                        [rid], |row| row.get::<_, Option<String>>(0),
                    ).optional().map_err(rs)?.flatten().unwrap_or_else(|| "GENESIS".to_string()),
                    None => "GENESIS".to_string(),
                };

                // Deduct or settle leases if any exist
                tx.execute(
                    "UPDATE model_call_leases SET status = 'settled', actual_cost_micros = ?1, settled_at = ?2
                     WHERE episode_id = ?3 AND action_attempt_id = ?4 AND status = 'reserved'",
                    (args.cost_micros, Utc::now().to_rfc3339(), args.episode_id.clone(), args.action_attempt_id.clone()),
                ).map_err(rs)?;

                let outcome_res = step::attempt_commit(
                    &tx,
                    attempt_uuid,
                    args.expected_revision,
                    &args.claim_token,
                    &args.action,
                    &*self.gateway,
                    args.cost_micros as i128,
                );

                let (disposition, accepted, error_msg) = match &outcome_res {
                    Ok(chatdb_proof_core::models::LeanVerificationOutcome::KernelPass) => {
                        (StepDisposition::Accepted, true, None)
                    }
                    Ok(_) => (StepDisposition::Accepted, false, None),
                    Err(step::StepError::Conflict) => (
                        StepDisposition::StaleRevision, false,
                        Some("Revision conflict — retry episode_step with the episode's current revision (see episode_status); the claim is still valid".to_string()),
                    ),
                    Err(step::StepError::InvalidAttempt) => (
                        StepDisposition::InvalidResponse, false,
                        Some("Invalid attempt claim or status".to_string()),
                    ),
                    Err(e) => (StepDisposition::Error, false, Some(format!("{:?}", e))),
                };

                // Recovery: a Conflict means the client should retry with a corrected
                // revision using the SAME claim (nothing to reset). InvalidAttempt means
                // there was never a real, matching attempt row to reset. Everything past
                // that point (attempt already marked 'executing') failed structurally and
                // must be freed so the request doesn't wedge until the 5-minute expiry.
                if let Err(e) = &outcome_res {
                    if matches!(e, step::StepError::LeanGatewayError(_) | step::StepError::ActionSchemaInvalid(_) | step::StepError::DatabaseError(_) | step::StepError::Internal(_)) {
                        let new_status = if matches!(e, step::StepError::LeanGatewayError(_)) { "infrastructure_failed" } else { "abandoned" };
                        attempts::attempt_abandon(&tx, attempt_uuid, new_status).map_err(rs)?;
                    }
                }

                let mut is_terminated = false;
                let mut is_truncated = false;
                let mut term_reason = None;
                let mut trunc_reason = None;
                let mut outcome_enum: Option<EpisodeOutcome> = None;

                if disposition == StepDisposition::Accepted {
                    let is_give_up = matches!(args.action, TypedAction::GiveUp);

                    if is_give_up {
                        tx.execute(
                            "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                            (EpisodeOutcome::GaveUp.to_string(), TerminationReason::ModelGaveUp.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                        ).map_err(rs)?;
                        is_terminated = true;
                        term_reason = Some(TerminationReason::ModelGaveUp);
                        outcome_enum = Some(EpisodeOutcome::GaveUp);
                    } else {
                        let root_proved: bool = tx.query_row(
                            "SELECT status FROM episode_obligations WHERE episode_id = ?1 AND kind = 'root'",
                            [args.episode_id.clone()],
                            |row| row.get::<_, String>(0),
                        ).optional().map_err(rs)?.map(|s| s == "proved").unwrap_or(false);

                        if root_proved {
                            // PROOF SOUNDNESS ("Lean proved this exact formal statement")
                            // and STATEMENT FIDELITY ("this formal statement represents the
                            // source problem") are independent claims. A kernel-verified root
                            // is only 'certified' — and only promotes the problem to COMPLETE
                            // — when the problem's fidelity_status is ALSO 'verified'. This is
                            // the fix for the weakened-root exploit: proving a trivially-true
                            // relaxation of the source statement must never present as
                            // certifying the source claim.
                            let fidelity_status: String = tx.query_row(
                                "SELECT pv.fidelity_status FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id WHERE e.id = ?1",
                                [args.episode_id.clone()],
                                |row| row.get(0),
                            ).map_err(rs)?;
                            let fidelity_verified = fidelity_status == "verified";

                            let final_outcome = if fidelity_verified { EpisodeOutcome::Certified } else { EpisodeOutcome::KernelVerified };
                            tx.execute(
                                "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                                (final_outcome.to_string(), TerminationReason::RootProved.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                            ).map_err(rs)?;

                            if fidelity_verified {
                                // Advance the problem lifecycle too, so problem_list is a
                                // status board rather than a stale cache of PROVING rows.
                                tx.execute(
                                    "UPDATE problem_versions SET state = 'COMPLETE'
                                     WHERE id = (SELECT problem_version_id FROM episodes WHERE id = ?1)
                                     AND state = 'PROVING'",
                                    [args.episode_id.clone()],
                                ).map_err(rs)?;
                            } else {
                                // Root is proved but fidelity isn't — park the problem in
                                // FIDELITY_REVIEW rather than PROVING (proof search is done)
                                // or COMPLETE (nothing has been certified). A later
                                // problem_submit_fidelity_review(decision=verified) promotes
                                // this episode's outcome to 'certified' retroactively.
                                tx.execute(
                                    "UPDATE problem_versions SET state = 'FIDELITY_REVIEW'
                                     WHERE id = (SELECT problem_version_id FROM episodes WHERE id = ?1)
                                     AND state = 'PROVING'",
                                    [args.episode_id.clone()],
                                ).map_err(rs)?;
                            }
                            is_terminated = true;
                            term_reason = Some(TerminationReason::RootProved);
                            outcome_enum = Some(final_outcome);
                        } else {
                            let (steps, max_steps, budget): (i64, Option<i64>, Option<i64>) = tx.query_row(
                                "SELECT step_count, max_steps, cost_budget_micros FROM episodes WHERE id = ?1",
                                [args.episode_id.clone()],
                                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                            ).map_err(rs)?;

                            let steps_exhausted = max_steps.map(|m| steps >= m).unwrap_or(false);
                            let budget_exhausted = budget.map(|b| b <= 0).unwrap_or(false);

                            if steps_exhausted || budget_exhausted {
                                tx.execute(
                                    "UPDATE episodes SET state = 'truncated', outcome = ?1, truncation_reason = ?2, completed_at = ?3 WHERE id = ?4",
                                    (EpisodeOutcome::BudgetExhausted.to_string(), TruncationReason::BudgetExhausted.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                                ).map_err(rs)?;
                                is_truncated = true;
                                trunc_reason = Some(TruncationReason::BudgetExhausted);
                                outcome_enum = Some(EpisodeOutcome::BudgetExhausted);
                            }
                        }
                    }
                }

                // If not ended, call advance to prepare the next request
                let next_req_id = if !is_terminated && !is_truncated && disposition == StepDisposition::Accepted {
                    lifecycle::advance(&tx, ep_uuid).map_err(rs)?
                } else {
                    None
                };

                // Trajectory: always record what was attempted (append-only truth,
                // including rejected/conflicted/errored attempts), then terminal markers.
                let env_hash = episode_env_hash(&tx, &args.episode_id).map_err(rs)?;
                let obligation_info: Option<(String, String, String)> = match &target_obligation_id {
                    Some(oid) => tx.query_row(
                        "SELECT problem_version_id, lean_statement, statement_hash FROM episode_obligations WHERE id = ?1",
                        [oid],
                        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                    ).optional().map_err(rs)?,
                    None => None,
                };
                let dependency_obligation_ids: Vec<String> = match &target_obligation_id {
                    Some(oid) => {
                        let mut s = tx.prepare(
                            "SELECT dependency_obligation_id FROM episode_obligation_edges e
                             JOIN episode_obligations dep ON dep.id = e.dependency_obligation_id
                             WHERE e.parent_obligation_id = ?1 AND dep.status = 'proved'",
                        ).map_err(rs)?;
                        s.query_map([oid], |row| row.get::<_, String>(0)).map_err(rs)?
                            .collect::<Result<Vec<_>, _>>().map_err(rs)?
                    }
                    None => vec![],
                };
                let lean_outcome_str = outcome_res.as_ref().ok().map(|o| o.to_string());
                let state_hash_after = episode_progress_hash(&tx, &args.episode_id)?;

                // For an accepted SubmitModule, record the verified module's
                // source + declaration-manifest hashes in the trajectory payload so
                // replay can confirm the exact artifact re-derives (issue #4). Read
                // back from the just-inserted row inside the same transaction.
                let module_artifact: Option<(String, String)> = match (&args.action, &target_obligation_id, accepted) {
                    (TypedAction::SubmitModule { .. }, Some(oid), true) => tx.query_row(
                        "SELECT module_source_hash, declaration_manifest_hash FROM episode_verified_modules
                         WHERE root_obligation_id = ?1 ORDER BY verified_at DESC LIMIT 1",
                        [oid],
                        |row| Ok((row.get(0)?, row.get(1)?)),
                    ).optional().map_err(rs)?,
                    _ => None,
                };

                let payload = serde_json::json!({
                    "obligation_id": target_obligation_id,
                    "problem_version_id": obligation_info.as_ref().map(|(pv, _, _)| pv),
                    "lean_statement": obligation_info.as_ref().map(|(_, s, _)| s),
                    "statement_hash": obligation_info.as_ref().map(|(_, _, h)| h),
                    "dependency_obligation_ids": dependency_obligation_ids,
                    "action": &args.action,
                    "outcome": lean_outcome_str,
                    "disposition": disposition,
                    "accepted": accepted,
                    "diagnostics": error_msg,
                    "module_source_hash": module_artifact.as_ref().map(|(s, _)| s),
                    "declaration_manifest_hash": module_artifact.as_ref().map(|(_, d)| d),
                });
                trajectories::record_event(
                    &tx, ep_uuid, "action_committed", &state_hash_before, &state_hash_after, &env_hash,
                    &payload.to_string(),
                ).map_err(mcp_internal_error)?;

                if is_terminated {
                    trajectories::record_event(
                        &tx, ep_uuid, "episode_terminated", &state_hash_after, &state_hash_after, &env_hash,
                        &serde_json::json!({"outcome": outcome_enum, "termination_reason": term_reason}).to_string(),
                    ).map_err(mcp_internal_error)?;
                } else if is_truncated {
                    trajectories::record_event(
                        &tx, ep_uuid, "episode_truncated", &state_hash_after, &state_hash_after, &env_hash,
                        &serde_json::json!({"outcome": outcome_enum, "truncation_reason": trunc_reason}).to_string(),
                    ).map_err(mcp_internal_error)?;
                }

                tx.commit().map_err(rs)?;

                // Calculate reward. `accepted` doubles as "not a Lean kernel_fail" for
                // Solve and as a generic accept/reject signal for Decompose/GiveUp — only
                // treat it as a proof-verification result (kernel_pass/kernel_fail reward)
                // for an actual Solve action.
                // Both Solve and SubmitModule are kernel-verification actions: each
                // produces a real KernelPass/KernelFail that earns the corresponding
                // reward. Decompose/GiveUp are structural and earn neither.
                let is_verification_action = matches!(args.action, TypedAction::Solve { .. } | TypedAction::SubmitModule { .. });
                let mut reward_components = Vec::new();
                let policy = RewardPolicy::default_policy();
                if disposition == StepDisposition::Accepted {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::StepPenalty,
                        value_scaled: policy.step_penalty,
                    });
                    if is_verification_action && accepted {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelPass,
                            value_scaled: policy.kernel_pass,
                        });
                    } else if is_verification_action && !is_terminated {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelFail,
                            value_scaled: policy.kernel_fail,
                        });
                    }
                }
                if outcome_enum == Some(EpisodeOutcome::Certified) || outcome_enum == Some(EpisodeOutcome::KernelVerified) {
                    // Real work either way: the prover proved exactly the formal
                    // statement it was given. Composite success (TerminalSuccess) is
                    // reserved for when fidelity is ALSO verified — never award it for
                    // a kernel_verified-but-not-certified outcome, or a prover that
                    // faithfully proved a bad formalization looks identical to one
                    // that solved the real problem.
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::RootKernelVerified,
                        value_scaled: policy.root_kernel_verified,
                    });
                    if outcome_enum == Some(EpisodeOutcome::Certified) {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::TerminalSuccess,
                            value_scaled: policy.terminal_success,
                        });
                    }
                } else if is_truncated {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::TruncationPenalty,
                        value_scaled: policy.truncation_penalty,
                    });
                }

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let observation = if let Some(ref req) = next_action_request {
                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req.id.to_string()],
                        |row| row.get(0),
                    ).optional().map_err(rs)?.flatten();
                    obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null)
                } else {
                    serde_json::Value::Null
                };

                // A rejected verification action (a kernel-failed Solve, or a
                // module refused by policy or the staged kernel) preserves its
                // reason as the obligation's failure_lesson. Surface it directly on
                // the step response so a client gets structured feedback about WHY
                // the draft was rejected without a second observe round-trip — the
                // module trust boundary demands the rejection be legible, not silent.
                let rejection_diagnostic: Option<String> = if is_verification_action
                    && disposition == StepDisposition::Accepted && !accepted {
                    match &target_obligation_id {
                        Some(oid) => conn.query_row(
                            "SELECT failure_lesson FROM episode_obligations WHERE id = ?1",
                            [oid], |row| row.get::<_, Option<String>>(0),
                        ).optional().map_err(rs)?.flatten(),
                        None => None,
                    }
                } else {
                    None
                };

                let res = serde_json::json!({
                    "accepted": accepted,
                    "disposition": disposition,
                    "counts_as_environment_step": disposition == StepDisposition::Accepted,
                    "reward": reward_components,
                    "outcome": outcome_enum,
                    "termination_reason": term_reason,
                    "truncation_reason": trunc_reason,
                    "diagnostics": error_msg,
                    "rejection_diagnostic": rejection_diagnostic,
                    "next_action_request": next_action_request,
                    "observation": observation
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_status" => {
                let args: EpisodeStatusArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let status = conn.query_row(
                    "SELECT state, current_revision, step_count, cost_budget_micros, invalid_action_count, outcome, termination_reason, truncation_reason
                     FROM episodes WHERE id = ?1",
                    [args.episode_id.clone()],
                    |row| {
                        Ok(serde_json::json!({
                            "state": row.get::<_, String>(0)?,
                            "current_revision": row.get::<_, i64>(1)?,
                            "step_count": row.get::<_, i64>(2)?,
                            "cost_budget_micros": row.get::<_, Option<i64>>(3)?,
                            "invalid_action_count": row.get::<_, i64>(4)?,
                            "outcome": row.get::<_, Option<String>>(5)?,
                            "termination_reason": row.get::<_, Option<String>>(6)?,
                            "truncation_reason": row.get::<_, Option<String>>(7)?,
                        }))
                    }
                ).optional().map_err(rs)?;

                match status {
                    Some(s) => Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&s).unwrap())])),
                    None => Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                }
            }
            "episode_close" => {
                let args: EpisodeCloseArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let current_state: Option<String> = tx.query_row(
                    "SELECT state FROM episodes WHERE id = ?1", [args.episode_id.clone()], |row| row.get(0)
                ).optional().map_err(rs)?;

                let Some(current_state) = current_state else {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                };

                if current_state == "terminated" || current_state == "truncated" {
                    tx.commit().map_err(rs)?;
                    let res = serde_json::json!({ "status": "already_closed", "state": current_state });
                    return Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]));
                }

                tx.execute(
                    "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                    (EpisodeOutcome::GaveUp.to_string(), TerminationReason::HumanCancelled.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                ).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &args.episode_id)?;
                let env_hash = episode_env_hash(&tx, &args.episode_id).map_err(rs)?;
                trajectories::record_event(
                    &tx, ep_uuid, "episode_terminated", &progress_hash, &progress_hash, &env_hash,
                    &serde_json::json!({"outcome": "gave_up", "termination_reason": "human_cancelled", "reason": args.reason}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "status": "closed" });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_reserve" => {
                let args: ModelCallReserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.reserved_cost_micros < 0 {
                    return Err(mcp_invalid_params("reserved_cost_micros must be >= 0"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let attempt_exists: Option<i64> = tx.query_row(
                    "SELECT 1 FROM action_attempts WHERE id = ?1 AND episode_id = ?2",
                    (&args.action_attempt_id, &args.episode_id),
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                if attempt_exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown action_attempt_id {} for episode {}", args.action_attempt_id, args.episode_id)));
                }

                let remaining: Option<i64> = tx.query_row(
                    "SELECT cost_budget_micros FROM episodes WHERE id = ?1", [&args.episode_id], |row| row.get(0)
                ).optional().map_err(rs)?.flatten();
                if let Some(remaining) = remaining {
                    if args.reserved_cost_micros > remaining {
                        return Err(mcp_invalid_params(format!(
                            "budget_denied: reserved_cost_micros {} exceeds remaining budget {}",
                            args.reserved_cost_micros, remaining
                        )));
                    }
                }

                let lease_id = Uuid::new_v4();
                let descriptor = serde_json::json!({
                    "runner_id": args.runner_id,
                    "declared_model": args.declared_model,
                    "max_input_tokens": args.max_input_tokens,
                    "max_output_tokens": args.max_output_tokens,
                });
                let descriptor_json = serde_json::to_string(&descriptor).unwrap();

                tx.execute(
                    "INSERT INTO model_call_leases (
                        id, episode_id, action_attempt_id, model_descriptor_json, reserved_cost_micros, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, 'reserved', ?6)",
                    (
                        lease_id.to_string(),
                        args.episode_id.clone(),
                        args.action_attempt_id.clone(),
                        descriptor_json,
                        args.reserved_cost_micros,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "lease_id": lease_id.to_string() });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_settle" => {
                let args: ModelCallSettleArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.actual_cost_micros < 0 {
                    return Err(mcp_invalid_params("actual_cost_micros must be >= 0"));
                }
                if !matches!(args.status.as_str(), "settled" | "voided") {
                    return Err(mcp_invalid_params("status must be 'settled' or 'voided'"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let lease: Option<(String, String)> = tx.query_row(
                    "SELECT episode_id, status FROM model_call_leases WHERE id = ?1",
                    [args.lease_id.clone()],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;

                let Some((episode_id, lease_status)) = lease else {
                    return Err(mcp_invalid_params(format!("unknown lease_id: {}", args.lease_id)));
                };
                if lease_status != "reserved" {
                    return Err(mcp_invalid_params(format!("lease {} is already {}", args.lease_id, lease_status)));
                }

                tx.execute(
                    "UPDATE model_call_leases SET status = ?1, actual_cost_micros = ?2, settled_at = ?3 WHERE id = ?4",
                    (args.status.clone(), args.actual_cost_micros, Utc::now().to_rfc3339(), args.lease_id.clone()),
                ).map_err(rs)?;

                if args.status == "settled" {
                    tx.execute(
                        "UPDATE episodes SET cost_budget_micros = cost_budget_micros - ?1 WHERE id = ?2",
                        (args.actual_cost_micros, &episode_id),
                    ).map_err(rs)?;
                }

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "status": args.status });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "trajectory_export" => {
                let args: TrajectoryExportArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let page_size = args.page_size.unwrap_or(50);
                let cursor = args.cursor.unwrap_or(0);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, event_sequence_number, event_type, event_hash, previous_event_hash,
                            state_hash_before, state_hash_after, lean_environment_hash, payload_json, created_at
                     FROM trajectory_events
                     WHERE episode_id = ?1 AND event_sequence_number >= ?2
                     ORDER BY event_sequence_number ASC LIMIT ?3"
                ).map_err(rs)?;

                let rows = stmt.query_map((args.episode_id.clone(), cursor, page_size), |row| {
                    Ok(serde_json::json!({
                        "id": row.get::<_, i64>(0)?,
                        "event_sequence_number": row.get::<_, i64>(1)?,
                        "event_type": row.get::<_, String>(2)?,
                        "event_hash": row.get::<_, String>(3)?,
                        "previous_event_hash": row.get::<_, String>(4)?,
                        "state_hash_before": row.get::<_, String>(5)?,
                        "state_hash_after": row.get::<_, String>(6)?,
                        "lean_environment_hash": row.get::<_, String>(7)?,
                        "payload": serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(8)?).unwrap_or(serde_json::Value::Null),
                        "created_at": row.get::<_, String>(9)?,
                    }))
                }).map_err(rs)?
                .collect::<Result<Vec<_>, _>>()
                .map_err(rs)?;

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&rows).unwrap())]))
            }
            "episode_replay" => {
                let args: EpisodeReplayArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let conn = self.conn.lock().await;
                let audit_ok = trajectories::audit_trajectory(&conn, ep_uuid).map_err(mcp_internal_error)?;

                let replay_status = trajectories::replay_trajectory(&conn, ep_uuid, &*self.gateway)
                    .map_err(mcp_internal_error)?;

                let events_replayed = match &replay_status {
                    trajectories::ReplayStatus::Empty => 0,
                    trajectories::ReplayStatus::Matched(n) => *n,
                };

                let res = serde_json::json!({
                    "audit_passed": audit_ok,
                    "events_replayed": events_replayed,
                    "replay_status": replay_status.to_string(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "proof_export" => {
                let args: ProofExportArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let format = args.format.as_deref().unwrap_or("markdown");
                if !matches!(format, "markdown" | "lean") {
                    return Err(mcp_invalid_params("format must be \"markdown\" or \"lean\""));
                }
                let conn = self.conn.lock().await;
                let doc = render_proof_export(&conn, &args.episode_id, format)?;
                Ok(CallToolResult::success(vec![Content::text(doc)]))
            }
            "lean_declaration_lookup" => {
                let args: LeanDeclarationLookupArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.names.is_empty() {
                    return Err(mcp_invalid_params("names must be non-empty"));
                }
                if args.names.len() > 50 {
                    return Err(mcp_invalid_params("names: at most 50 declarations per call"));
                }
                for n in &args.names {
                    if !valid_lean_declaration_name(n) {
                        return Err(mcp_invalid_params(format!(
                            "name {:?} is not a valid Lean declaration name — no whitespace, comments, or command syntax",
                            n
                        )));
                    }
                }

                let (import_manifest_json, import_manifest_hash, env_hash): (String, String, String) = {
                    // Scoped so the DB mutex is released BEFORE the potentially
                    // 15-40+ second blocking Lean invocation below — holding it
                    // that long would stall every other concurrent tool call
                    // (episode_observe, episode_status, ...) on the same session.
                    let conn = self.conn.lock().await;
                    conn.query_row(
                        "SELECT import_manifest_json, import_manifest_hash, environment_hash FROM problem_versions WHERE id = ?1",
                        [&args.problem_version_id],
                        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                    ).map_err(|e| if matches!(e, rusqlite::Error::QueryReturnedNoRows) {
                        mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id))
                    } else {
                        rs(e)
                    })?
                };
                let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

                let results = self.gateway.lookup_declarations(&args.names, &import_manifest, args.deep_check)
                    .map_err(mcp_internal_error)?;

                let res = serde_json::json!({
                    "environment_hash": env_hash,
                    "import_manifest_hash": import_manifest_hash,
                    "results": results.into_iter().map(|r| serde_json::json!({
                        "query": r.query,
                        "status": r.status.to_string(),
                        "diagnostics": r.diagnostics,
                    })).collect::<Vec<_>>(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            _ => Err(McpError::new(ErrorCode::METHOD_NOT_FOUND, format!("Method not found: {}", request.name), None)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rmcp::service::{serve_client, serve_server};
    use rmcp::model::CallToolRequestParams;
    use rmcp::transport::async_rw::AsyncRwTransport;
    use chatdb_proof_core::lean::LeanGateway;
    use chatdb_proof_core::lean::module::AssembledModule;
    use chatdb_proof_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult, LeanModuleVerificationResult, LeanDiagnostic, LeanDiagnosticCategory};

    struct MockGateway;
    impl LeanGateway for MockGateway {
        fn verify_exact(
            &self,
            obligation: &Obligation,
            candidate_source: &str,
            _approved_dependency_ids: &[Uuid],
            environment: &str,
            _import_manifest: &[String],
        ) -> Result<LeanVerificationResult, String> {
            let outcome = if candidate_source.contains("sorry") {
                LeanVerificationOutcome::KernelFail
            } else {
                LeanVerificationOutcome::KernelPass
            };
            Ok(LeanVerificationResult {
                outcome,
                attempt_id: Uuid::new_v4(),
                obligation_id: obligation.id,
                theorem_name: obligation.theorem_name.clone(),
                expected_statement_hash: obligation.statement_hash.clone(),
                elaborated_statement_hash: None,
                environment_hash: environment.to_string(),
                proof_source_hash: "".to_string(),
                compiled_artifact_hash: None,
                proof_term_hash: None,
                diagnostic: None,
                all_diagnostics: vec![],
                dependency_use_report: None,
                wall_time_ms: 1,
                lean_cpu_time_ms: 1,
            })
        }

        // The trait default now fails closed (see lean/mod.rs) — MockGateway
        // deliberately vouches for any import so tests can isolate
        // manifest-extension bookkeeping from real Lean validation, which is
        // covered live separately (see test_problem_create_extends_import_manifest).
        fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> {
            Ok(())
        }

        // Mock module verification: a module "passes" the kernel unless its
        // assembled source carries the explicit MOCK_KERNEL_FAIL marker, so tests
        // can drive both the pass and kernel-fail commit paths without a real Lean
        // toolchain. Policy rejections (bad names, prohibited constructs, root hash
        // mismatch) happen in chatdb-core BEFORE this is ever reached.
        fn verify_module(&self, assembled: &AssembledModule, environment: &str) -> Result<LeanModuleVerificationResult, String> {
            let fail = assembled.source.contains("MOCK_KERNEL_FAIL");
            let outcome = if fail { LeanVerificationOutcome::KernelFail } else { LeanVerificationOutcome::KernelPass };
            Ok(LeanModuleVerificationResult {
                outcome,
                problem_namespace: assembled.namespace.clone(),
                root_lean_name: assembled.root_lean_name.clone(),
                module_source_hash: assembled.module_source_hash.clone(),
                declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
                environment_hash: environment.to_string(),
                kernel_result_hash: format!("mock-kernel-{}", &assembled.module_source_hash[..8.min(assembled.module_source_hash.len())]),
                diagnostic: if fail {
                    Some(LeanDiagnostic {
                        category: LeanDiagnosticCategory::TacticFailure,
                        primary_message: "mock kernel failure".to_string(),
                        source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                        used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                    })
                } else { None },
                all_diagnostics: vec![],
                wall_time_ms: 1,
            })
        }
    }

    fn test_handler() -> ChatDbMcp {
        test_handler_with_gateway(RealLeanGateway::new(PathBuf::from("dummy"), PathBuf::from("dummy")))
    }

    fn test_handler_with_gateway(gateway: impl LeanGateway + Send + Sync + 'static) -> ChatDbMcp {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(gateway),
            lean_available: false,
            lean_environment: None,
        }
    }

    async fn connected_client(handler: ChatDbMcp) -> rmcp::service::RunningService<rmcp::RoleClient, InitializeRequestParams> {
        let (client_stream, server_stream) = tokio::io::duplex(1 << 20);
        let (client_read, client_write) = tokio::io::split(client_stream);
        let (server_read, server_write) = tokio::io::split(server_stream);

        let server_transport = AsyncRwTransport::new(server_read, server_write);
        let client_transport = AsyncRwTransport::new(client_read, client_write);

        tokio::spawn(async move {
            if let Ok(service) = serve_server(handler, server_transport).await {
                let _ = service.waiting().await;
            }
        });

        let client_info = Implementation::new("test-client", "1.0.0");
        let capabilities = ClientCapabilities::default();
        let init = InitializeRequestParams::new(capabilities, client_info);
        serve_client(init, client_transport).await.unwrap()
    }

    fn tool_json(res: &CallToolResult) -> serde_json::Value {
        assert!(!res.is_error.unwrap_or(false), "tool call returned isError: {:?}", res.content);
        serde_json::from_str(res.content[0].as_text().unwrap().text.as_str()).unwrap()
    }

    #[tokio::test]
    async fn test_mcp_list_tools_and_describe() {
        let client = connected_client(test_handler()).await;

        let list_res = client.peer().list_tools(None).await.unwrap();
        assert_eq!(list_res.tools.len(), 17);

        // The episode_step schema must be fully INLINE at the parameter site: no
        // $ref for the client to chase, and an explicit `type: "object"` on the
        // action node so coercion-by-declared-type harnesses treat it as an object
        // (found live: a client shipped the action as a string because the param
        // node only carried a $ref).
        let step_tool = list_res.tools.iter().find(|t| t.name == "episode_step").unwrap();
        let step_schema_val = serde_json::to_value(&step_tool.input_schema).unwrap();
        let step_schema = step_schema_val.to_string();
        assert!(!step_schema.contains("$ref"), "episode_step schema must not contain dangling refs: {step_schema}");
        assert!(step_schema.contains("proof_term"), "TypedAction variants must be visible in the schema: {step_schema}");
        assert!(step_schema.contains("give_up"), "internally-tagged variant names must be visible: {step_schema}");
        let action_node = &step_schema_val["properties"]["action"];
        assert_eq!(action_node["type"], "object", "action param must declare objecthood inline: {action_node}");
        assert!(action_node["oneOf"].is_array(), "action param must carry the oneOf variants inline: {action_node}");

        let call_params = CallToolRequestParams::new("environment_describe");
        let call_res = client.peer().call_tool(call_params).await.unwrap();
        let json = tool_json(&call_res);
        assert_eq!(json["protocol_version"], "2025-11-25");
        assert_eq!(json["lean_gateway"], "unavailable");
        assert!(json["lean_environment"].is_null(), "no lean-checker at the dummy test path -> no environment to report");
        assert!(json["action_schema"].is_object(), "environment_describe must expose the TypedAction schema");
        assert_eq!(json["action_examples"][0]["type"], "solve");
    }

    /// Full MCP-level playthrough: this is the scenario the live playtest against
    /// the release binary could never complete (attempt_claim missing, revision
    /// hardcoded to 1, outcome vocabulary violating the CHECK constraint). It must
    /// stay green — it's the regression guard for all of that.
    #[tokio::test]
    async fn test_decompose_and_giveup_playthrough() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "1 + 1 = 2",
            "root_formal_statement": "1 + 1 = 2",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 10, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        assert_eq!(ep["state"], "awaiting_external_action");
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let advertised_revision = req["episode_revision"].as_i64().unwrap();
        assert_eq!(advertised_revision, 0, "advance() must advertise the episode's ACTUAL current_revision, not a hardcoded value");

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "k1", "expected_revision": advertised_revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        // Decompose using the exact advertised revision (proves the revision fix).
        let step1 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": advertised_revision, "claim_token": claim_token,
            "action": {"type": "decompose", "sub_lemmas": ["helper lemma"]},
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step1["disposition"], "accepted", "{:?}", step1);
        assert_eq!(step1["accepted"], true);
        let next_req = &step1["next_action_request"];
        assert!(!next_req.is_null(), "advance() must produce a next request without a UNIQUE(episode_id, episode_revision) collision");
        let next_revision = next_req["episode_revision"].as_i64().unwrap();
        assert_eq!(next_revision, 1, "revision must have incremented by exactly one");

        // GiveUp on the child obligation should terminate the episode.
        let request_id_2 = next_req["id"].as_str().unwrap().to_string();
        let claim2 = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id_2,
            "idempotency_key": "k2", "expected_revision": next_revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id_2 = claim2["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token_2 = claim2["claim_token"].as_str().unwrap().to_string();

        let step2 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id_2,
            "expected_revision": next_revision, "claim_token": claim_token_2,
            "action": {"type": "give_up"}, "cost_micros": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step2["disposition"], "accepted", "{:?}", step2);
        assert_eq!(step2["outcome"], "gave_up");
        assert_eq!(step2["termination_reason"], "model_gave_up");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "gave_up");

        // episode_close on an already-terminal episode must not hit the CHECK
        // constraint that killed it live (`outcome IN (...)` mismatch).
        let close = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_close").with_arguments(serde_json::json!({
            "episode_id": episode_id, "reason": "test",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(close["status"], "already_closed");

        let traj = tool_json(&peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(traj.as_array().unwrap().len() >= 3, "expected episode_created + 2 action_committed + episode_terminated events, got {:?}", traj);

        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true);
    }

    #[tokio::test]
    async fn test_fabricated_claim_and_stale_revision_still_rejected() {
        let handler = test_handler();
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let fabricated = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": Uuid::new_v4().to_string(),
            "expected_revision": 0, "claim_token": "made-up",
            "action": {"type": "give_up"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(fabricated["disposition"], "invalid_response");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["current_revision"], 0, "a rejected fabricated claim must not mutate episode state");
    }

    /// The scenario the fix plan calls the definition of done: create → observe →
    /// claim → solve → certified, with a non-empty audited trajectory. This never
    /// passed against the release binary (attempt_claim didn't exist, and even
    /// with SQL-claimed attempts the revision bug rolled back every accepted step).
    #[tokio::test]
    async fn test_solve_to_certified_playthrough() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Prove that 1 + 1 = 2 in the natural numbers.",
            "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": create["source_problem_hash"], "root_statement_hash": create["root_statement_hash"],
            "rendering_hash": create["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["observation"]["root_theorem_signature"], "1 + 1 = 2");

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "solve-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "norm_num"},
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "{:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "certified", "{:?}", step);
        assert_eq!(step["termination_reason"], "root_proved", "{:?}", step);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "certified");
        assert_eq!(status["step_count"], 1);
        assert_eq!(status["cost_budget_micros"], 999_900);

        let traj = tool_json(&peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let events = traj.as_array().unwrap();
        assert!(events.len() >= 3, "expected episode_created + action_committed + episode_terminated, got {:?}", events);

        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true, "{:?}", replay);
        assert_eq!(replay["events_replayed"], 1, "the one solve event must be re-verified through the gateway, not vacuously passed");
        assert_eq!(replay["replay_status"], "matched(1)");

        // proof_export: markdown dossier carries the verdict, the goal, the tree,
        // the winning proof term, and the attempt table; lean format is bare source.
        let export_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        assert!(!export_res.is_error.unwrap_or(false));
        let md = export_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("CERTIFIED"), "{md}");
        assert!(md.contains("1 + 1 = 2"), "{md}");
        assert!(md.contains("## Proof tree"), "{md}");
        assert!(md.contains("norm_num"), "the winning proof term must appear: {md}");
        assert!(md.contains("kernel_pass"), "{md}");

        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("theorem root_theorem : 1 + 1 = 2 := by"), "{lean}");
        assert!(!lean.contains("## "), "lean format must be bare source, not markdown: {lean}");
        // The assembled source must carry the problem's REAL import manifest, not
        // a hardcoded Ring/NormNum stub. This problem used the default manifest.
        assert!(lean.contains("import Mathlib.Tactic.Ring"), "real manifest must be rendered: {lean}");
        assert!(lean.contains("import Mathlib.Tactic.NormNum"), "real manifest must be rendered: {lean}");
        // The dossier must state the pinned verification context as a receipt.
        assert!(md.contains("## Verification context"), "dossier must carry verification context: {md}");
        assert!(md.contains("Import manifest hash:"), "dossier must carry manifest hash: {md}");
        assert!(md.contains("Environment hash:"), "dossier must carry environment hash: {md}");
    }

    /// Drives an episode through observe → claim → submit_module. A helper `def`
    /// plus a root theorem whose statement hash-matches the registered root must
    /// verify as one module and prove the root obligation. Under an attested (not
    /// fidelity-verified) problem the terminal outcome is `kernel_verified`.
    #[tokio::test]
    async fn test_submit_module_def_and_root_passes() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Define double and show double 2 = 4.",
            "root_formal_statement": "double 2 = 4",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "mod-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [
                    {"item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n"}
                ],
                "root_theorem": {"name": "double_two", "statement": "double 2 = 4", "proof_term": "rfl"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "{:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "attested problem: module root proof reaches kernel_verified, not certified: {:?}", step);
        assert_eq!(step["termination_reason"], "root_proved", "{:?}", step);
        // Kernel pass reward earned by the module verification action.
        let reward = step["reward"].as_array().unwrap();
        assert!(reward.iter().any(|r| r["id"] == "kernel_pass"), "module verification must earn kernel_pass: {:?}", reward);
        assert!(reward.iter().any(|r| r["id"] == "root_kernel_verified"), "{:?}", reward);
        assert!(!reward.iter().any(|r| r["id"] == "terminal_success"), "attested-only must NOT earn terminal_success: {:?}", reward);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "kernel_verified");
    }

    /// A module whose root theorem statement does NOT hash-match the registered
    /// root is rejected by policy (before Lean), the obligation stays open, and the
    /// episode does not terminate. This is the "cannot silently prove a different
    /// goal" guard.
    #[tokio::test]
    async fn test_submit_module_root_statement_mismatch_rejected() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Show 2 + 2 = 4.",
            "root_formal_statement": "2 + 2 = 4",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "mod-bad", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [],
                // A trivially-true DIFFERENT statement — must be refused, not accepted.
                "root_theorem": {"name": "sneaky", "statement": "True", "proof_term": "trivial"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "the step itself commits (as a rejected attempt): {:?}", step);
        assert_eq!(step["accepted"], false, "a root-hash mismatch must not be accepted: {:?}", step);
        assert!(step["outcome"] != "kernel_verified" && step["outcome"] != "certified", "{:?}", step);
        assert!(step["termination_reason"].is_null(), "a rejected module must not terminate the episode: {:?}", step);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_ne!(status["state"], "terminated", "{:?}", status);
        assert_eq!(status["invalid_action_count"], 1, "{:?}", status);
    }

    /// Drives one attested-problem episode all the way to a single submit_module
    /// step and returns the step-result JSON. Keeps the rejection-matrix tests to
    /// the essential difference — the module payload — instead of repeating the
    /// whole observe/claim/step dance.
    async fn attested_module_step(root_statement: &str, action: serde_json::Value) -> serde_json::Value {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": format!("staging test for: {}", root_statement),
            "root_formal_statement": root_statement,
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "stage-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": action, "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap())
    }

    /// Required test #12: under a fidelity-VERIFIED problem, a module root proof
    /// reaches `certified` (both proof soundness AND statement fidelity), promoting
    /// the problem to COMPLETE — the module analogue of the certified Solve path.
    #[tokio::test]
    async fn test_submit_module_with_verified_fidelity_reaches_certified() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Show 1 + 1 = 2.",
            "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": create["source_problem_hash"], "root_statement_hash": create["root_statement_hash"],
            "rendering_hash": create["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "cert-mod", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [],
                "root_theorem": {"name": "one_one", "statement": "1 + 1 = 2", "proof_term": "norm_num"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "certified", "verified fidelity + module root proof must certify: {:?}", step);
        let reward = step["reward"].as_array().unwrap();
        assert!(reward.iter().any(|r| r["id"] == "terminal_success"), "certified module must earn terminal_success: {:?}", reward);

        // Problem promoted to COMPLETE.
        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv_id || p["id"] == pv_id);
        if let Some(p) = mine {
            assert_eq!(p["state"], "COMPLETE", "certified module must promote the problem to COMPLETE: {:?}", p);
        }
    }

    /// Issue #4: a verified module round-trips through replay and proof_export.
    /// Replay re-assembles from structured JSON and re-verifies (matched(1)); the
    /// lean export IS the exact module source; the markdown dossier shows the
    /// module's declaration manifest, not only a proof tree.
    #[tokio::test]
    async fn test_submit_module_persist_export_and_replay_roundtrip() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Define quad and show quad 2 = 8.",
            "root_formal_statement": "quad 2 = 8",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "rt-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [
                    {"item_kind": "def", "name": "quad", "type_signature": "Nat → Nat", "body": "fun n => 4 * n"}
                ],
                "root_theorem": {"name": "quad_two", "statement": "quad 2 = 8", "proof_term": "rfl"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);

        // Replay: the module re-assembles from structured JSON and re-verifies.
        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true, "{:?}", replay);
        assert_eq!(replay["events_replayed"], 1, "the module verification event must be re-verified, not vacuously passed: {:?}", replay);
        assert_eq!(replay["replay_status"], "matched(1)");

        // Lean export IS the exact module source, under the problem namespace.
        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("namespace ChatDB.P_"), "module export must carry the namespace: {lean}");
        assert!(lean.contains("def quad : Nat → Nat :="), "{lean}");
        assert!(lean.contains("theorem quad_two : quad 2 = 8 := by"), "{lean}");
        assert!(lean.trim_end().ends_with("end ChatDB.P_") || lean.contains("\nend ChatDB.P_"), "{lean}");

        // Markdown dossier shows the module's declaration manifest.
        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("## Verified module"), "{md}");
        assert!(md.contains("module_source_hash:"), "{md}");
        assert!(md.contains("root_theorem"), "the manifest must mark the root theorem item: {md}");
        assert!(md.contains("`quad`"), "the manifest must list the helper def: {md}");
    }

    /// Issue #3 acceptance: a helper def passes and the root theorem uses it — the
    /// whole module verifies together and the root obligation is proved.
    #[tokio::test]
    async fn test_submit_module_helper_def_used_by_root() {
        let step = attested_module_step("triple 3 = 9", serde_json::json!({
            "type": "submit_module",
            "module_items": [
                {"item_kind": "def", "name": "triple", "type_signature": "Nat → Nat", "body": "fun n => 3 * n"}
            ],
            "root_theorem": {"name": "triple_three", "statement": "triple 3 = 9", "proof_term": "rfl"}
        })).await;
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);
    }

    /// Issue #3 acceptance: the root theorem is fine, but a NON-root helper carries
    /// a prohibited construct — the WHOLE module is rejected, atomically. Nothing is
    /// committed, the episode does not terminate, and the rejection is legible.
    #[tokio::test]
    async fn test_submit_module_prohibited_construct_matrix() {
        // Each case: a valid root theorem (`True`/`trivial`) plus one helper whose
        // content smuggles a prohibited construct. The token the client tried to
        // inject must appear in the surfaced rejection diagnostic.
        let cases: Vec<(&str, serde_json::Value)> = vec![
            ("import",     serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nimport Mathlib"})),
            ("namespace",  serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nnamespace Evil"})),
            ("end",        serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nend"})),
            ("set_option", serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nset_option maxHeartbeats 0"})),
            ("axiom",      serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\n\naxiom cheat : False"})),
            ("opaque",     serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"opaque trivial"})),
            ("unsafe",     serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"unsafe trivial"})),
            ("sorry",      serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"sorry"})),
        ];

        for (token, bad_item) in cases {
            let step = attested_module_step("True", serde_json::json!({
                "type": "submit_module",
                "module_items": [bad_item],
                "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial"}
            })).await;
            assert_eq!(step["accepted"], false, "module smuggling `{}` must be rejected: {:?}", token, step);
            assert!(step["termination_reason"].is_null(), "rejected `{}` module must not terminate the episode: {:?}", token, step);
            let diag = step["rejection_diagnostic"].as_str().unwrap_or("");
            assert!(diag.contains(token) || diag.contains("prohibited"),
                "rejection for `{}` must be legible (got {:?})", token, step["rejection_diagnostic"]);
        }
    }

    /// Issue #3 acceptance: a raw `import` (a helper theorem proof carrying its own
    /// import line) is rejected — the client never writes import lines; the server
    /// owns them. Also confirms the episode stays re-attemptable after rejection.
    #[tokio::test]
    async fn test_submit_module_raw_import_rejected_and_reattemptable() {
        let step = attested_module_step("True", serde_json::json!({
            "type": "submit_module",
            "module_items": [],
            "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial\nimport Mathlib.Tactic"}
        })).await;
        assert_eq!(step["accepted"], false, "{:?}", step);
        assert!(step["rejection_diagnostic"].as_str().unwrap_or("").contains("import"), "{:?}", step);
        // The obligation is still open: the step handed back a next_action_request
        // targeting the same (still-unproved) root, so the prover can try again.
        assert!(!step["next_action_request"].is_null(), "a rejected module must leave the obligation open for another attempt: {:?}", step);
    }

    /// `proof_export` must render the problem's actual (custom) import manifest,
    /// not a hardcoded Ring/NormNum stub. Regression guard for the bug that made
    /// the dossier export a non-replayable approximation.
    #[tokio::test]
    async fn test_proof_export_renders_custom_import_manifest() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "custom manifest export check",
            "root_formal_statement": "True",
            "problem_imports": ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum",
                                "Mathlib.Data.Real.Basic", "Mathlib.Tactic.LinearCombination"],
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let manifest_hash = create["import_manifest_hash"].as_str().unwrap().to_string();
        assert!(!manifest_hash.is_empty(), "custom manifest must have a real hash");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        // Even with nothing proved yet, the lean-format export must already reflect
        // the real manifest (imports are rendered before the obligation body).
        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("import Mathlib.Data.Real.Basic"), "custom manifest module missing from export: {lean}");
        assert!(lean.contains("import Mathlib.Tactic.LinearCombination"), "custom manifest module missing from export: {lean}");

        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains(&manifest_hash), "dossier must carry the problem's manifest hash: {md}");
        assert!(md.contains("Mathlib.Data.Real.Basic"), "dossier must list the manifest modules: {md}");
    }

    /// A solve that fails Lean verification must NOT terminate the episode, must
    /// count as a step, and must leave the obligation open (re-attemptable).
    #[tokio::test]
    async fn test_solve_kernel_fail_does_not_terminate() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "fail-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "sorry"},
            "cost_micros": 50,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted");
        assert_eq!(step["accepted"], false);
        assert!(step["outcome"].is_null());
        assert!(!step["next_action_request"].is_null(), "a kernel-fail must re-offer the same (still open) obligation, not dead-end the episode");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "awaiting_external_action");
        assert_eq!(status["step_count"], 1);
    }

    /// The idempotency key on attempt_claim must be safe to retry: same key while
    /// still claimed returns the SAME attempt instead of erroring on the unique index.
    #[tokio::test]
    async fn test_attempt_claim_idempotent_retry() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let request_id = ep["next_action_request"]["id"].as_str().unwrap().to_string();

        let claim_args = serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "retry-key", "expected_revision": 0,
        }).as_object().unwrap().clone();

        let first = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(claim_args.clone())).await.unwrap());
        let second = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(claim_args)).await.unwrap());

        assert_eq!(first["action_attempt_id"], second["action_attempt_id"], "retried claim with same idempotency_key must return the same attempt");
        assert_eq!(first["claim_token"], second["claim_token"]);
    }

    /// A problem_create with no lean-checker configured (test_handler's gateway
    /// points at a dummy path) must not silently write a meaningless placeholder
    /// like "unspecified-env" — that made replay's determinism claim untraceable
    /// to any actual toolchain/Mathlib pin. It should say plainly that the
    /// gateway was unavailable.
    #[tokio::test]
    async fn test_problem_create_env_hash_is_not_a_silent_placeholder() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(pv["environment_hash"], "lean-gateway-unavailable", "{:?}", pv);
    }

    /// A request nobody ever claimed still carries its own `expiration_at` timer,
    /// separate from an attempt's claim_expiration. Nothing previously checked it,
    /// so a lapsed unclaimed request displayed `status: pending` forever instead of
    /// being retired and replaced.
    #[tokio::test]
    async fn test_unclaimed_request_expiry_is_recovered() {
        let handler = test_handler();
        let conn_handle = handler.conn.clone();
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let stale_request_id = ep["next_action_request"]["id"].as_str().unwrap().to_string();

        {
            let conn = conn_handle.lock().await;
            conn.execute(
                "UPDATE action_requests SET expiration_at = '2000-01-01T00:00:00Z' WHERE id = ?1",
                [&stale_request_id],
            ).unwrap();
        }

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let fresh_request_id = observed["action_request"]["id"].as_str().unwrap().to_string();
        assert_ne!(fresh_request_id, stale_request_id, "episode_observe must retire a lapsed request and mint a fresh one, not keep serving the stale one");
        assert_eq!(observed["action_request"]["status"], "pending");

        let conn = conn_handle.lock().await;
        let stale_status: String = conn.query_row(
            "SELECT status FROM action_requests WHERE id = ?1", [&stale_request_id], |row| row.get(0),
        ).unwrap();
        assert_eq!(stale_status, "expired", "the lapsed request must be marked expired, not left as pending");
    }

    async fn claim_and_solve(peer: &rmcp::service::Peer<rmcp::RoleClient>, episode_id: &str, proof_term: &str, idem: &str) -> serde_json::Value {
        let obs = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let req = &obs["action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": idem, "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"], "expected_revision": req["episode_revision"],
            "claim_token": claim["claim_token"], "action": {"type": "solve", "proof_term": proof_term}, "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap())
    }

    /// THE EXPLOIT REGRESSION: a kernel-verified root of a weakened/vacuous
    /// formalization must reach `kernel_verified`, never `certified` — proof
    /// soundness and statement fidelity are independent claims. Uses
    /// unsafe_dev_attestation (the only way to prove without a real review),
    /// which itself must never be enough to reach `certified`.
    #[tokio::test]
    async fn test_weakened_root_reaches_kernel_verified_not_certified() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Every even natural is divisible by two.",
            "root_formal_statement": "∀ n : ℕ, Even n → True", // weakened: conclusion is trivially true
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(pv["fidelity_status"], "attested");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "trivial", "weakened-root").await;
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "a weakened root must NOT present as certified: {:?}", step);
        assert_eq!(step["termination_reason"], "root_proved");
        let reward_ids: Vec<&str> = step["reward"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(reward_ids.contains(&"root_kernel_verified"), "{:?}", reward_ids);
        assert!(!reward_ids.contains(&"terminal_success"), "TerminalSuccess must never be paid without fidelity verification: {:?}", reward_ids);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["outcome"], "kernel_verified");

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "FIDELITY_REVIEW", "root-proved-but-unverified must park in FIDELITY_REVIEW, never COMPLETE: {:?}", mine);
        assert_eq!(mine["fidelity_status"], "attested", "finalization must not silently upgrade fidelity_status");

        // And the dossier must never render this as CERTIFIED.
        let export_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = export_res.content[0].as_text().unwrap().text.clone();
        assert!(!md.contains("✅ CERTIFIED"), "dossier must not overclaim: {md}");
        assert!(md.contains("QUARANTINED"), "{md}");
    }

    /// A review can only authorize the exact text it reviewed — submitted hashes
    /// that don't match the problem's CURRENT source/statement/rendering must be
    /// rejected, not silently accepted as if they matched.
    #[tokio::test]
    async fn test_fidelity_review_wrong_hashes_rejected() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "y",
        }).as_object().unwrap().clone())).await.unwrap());

        // mcp_invalid_params surfaces as a JSON-RPC-level error (Err from call_tool),
        // not a CallToolResult with isError=true — this handler rejects the request
        // outright rather than returning a "soft" failure result.
        let res = peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": "0000000000000000000000000000000000000000000000000000000000000000",
            "root_statement_hash": pv["root_statement_hash"], "rendering_hash": pv["rendering_hash"],
            "evidence_json": "{}",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "a hash mismatch must be rejected, not silently accepted");

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["fidelity_status"], "unreviewed", "a rejected submission must not mutate fidelity_status");
    }

    /// POSITIVE CONTROL: a real review verifying a faithful formalization, done
    /// BEFORE proving, reaches `certified` / COMPLETE directly on root proof —
    /// the split must not penalize the case where fidelity was already settled.
    #[tokio::test]
    async fn test_fidelity_verified_before_proving_reaches_certified_directly() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Every even natural is divisible by two.",
            "root_formal_statement": "∀ n : ℕ, Even n → ∃ k : ℕ, n = 2 * k",
        }).as_object().unwrap().clone())).await.unwrap());

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": pv["source_problem_hash"], "root_statement_hash": pv["root_statement_hash"],
            "rendering_hash": pv["rendering_hash"], "evidence_json": "{\"note\":\"faithful\"}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "exact ⟨n, by ring⟩", "positive-control").await;
        assert_eq!(step["outcome"], "certified", "{:?}", step);
        let reward_ids: Vec<&str> = step["reward"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(reward_ids.contains(&"terminal_success"), "{:?}", reward_ids);

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "COMPLETE");
    }

    /// A fidelity review landing 'verified' AFTER an episode already reached
    /// `kernel_verified` must promote that episode's outcome to `certified`
    /// retroactively — the review need not precede the proof.
    #[tokio::test]
    async fn test_fidelity_review_promotes_kernel_verified_episode_retroactively() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "y", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "trivial", "retro-1").await;
        assert_eq!(step["outcome"], "kernel_verified");

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": pv["source_problem_hash"], "root_statement_hash": pv["root_statement_hash"],
            "rendering_hash": pv["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["outcome"], "certified", "retroactive promotion must flip the episode's outcome: {:?}", status);

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "COMPLETE");
    }

    /// problem_create with problem_imports must extend the base manifest (never
    /// replace it), validate each new import through the gateway, and return a
    /// manifest hash a client can copy into lean_declaration_lookup/replay checks.
    #[tokio::test]
    async fn test_problem_create_extends_import_manifest() {
        // MockGateway explicitly overrides validate_import_manifest to Ok(())
        // (the trait default now fails closed) — this isolates "does the
        // manifest extend/return correctly" from "does the real Lean validation
        // work" (covered live separately). The module path still has to pass
        // the syntax-level valid_lean_module_path check, which runs before any
        // gateway is invoked regardless of which gateway is configured.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
            "problem_imports": ["Mathlib.NumberTheory.Padics.PadicVal.Basic"],
        }).as_object().unwrap().clone())).await.unwrap());

        let manifest = pv["import_manifest"].as_array().unwrap();
        let manifest_strs: Vec<&str> = manifest.iter().map(|v| v.as_str().unwrap()).collect();
        assert!(manifest_strs.contains(&"Mathlib.Tactic.Ring"), "{:?}", manifest_strs);
        assert!(manifest_strs.contains(&"Mathlib.Tactic.NormNum"), "{:?}", manifest_strs);
        assert!(manifest_strs.contains(&"Mathlib.NumberTheory.Padics.PadicVal.Basic"), "{:?}", manifest_strs);
        assert!(pv["import_manifest_hash"].as_str().unwrap().len() > 0);

        // A bad module path must be rejected at creation, not discovered later at
        // solve time. Syntax-level rejection is covered by
        // test_problem_create_rejects_malformed_import_syntax below; rejection
        // by real Lean (a syntactically-valid but nonexistent module) is
        // exercised live against the real lean-checker rather than here, since
        // test_handler's RealLeanGateway points at a dummy, nonexistent path.
    }

    /// lean_declaration_lookup must return an honest per-name status even when
    /// the gateway can't check (default trait impl) — never silently fabricate
    /// availability or unavailability.
    #[tokio::test]
    async fn test_lean_declaration_lookup_reports_environment_error_honestly() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
        }).as_object().unwrap().clone())).await.unwrap());

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "names": ["Nat.factorization"],
        }).as_object().unwrap().clone())).await.unwrap());

        assert_eq!(res["import_manifest_hash"], pv["import_manifest_hash"]);
        let results = res["results"].as_array().unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0]["query"], "Nat.factorization");
        // test_handler's gateway doesn't override lookup_declarations, so the
        // honest default (environment_error) applies — this proves the tool
        // never guesses when it can't actually check.
        assert_eq!(results[0]["status"], "environment_error");
    }

    /// SOUNDNESS: `problem_imports` entries are written verbatim into
    /// `import {module}\n` Lean source (see build_import_block). Without
    /// syntax validation, a string containing a newline could append arbitrary
    /// Lean commands (e.g. `axiom cheat : False`) to every proof file checked
    /// against that problem's manifest — a full soundness bypass through a
    /// different door than the one the fidelity-review split closed. Every
    /// one of these must be rejected at problem_create, before it ever reaches
    /// the gateway or gets stored.
    #[tokio::test]
    async fn test_problem_create_rejects_malformed_import_syntax() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let malicious = [
            "Mathlib\naxiom cheat : False",
            "Mathlib\nset_option maxHeartbeats 0",
            "Mathlib -- comment",
            "Mathlib; axiom cheat : False",
            "Mathlib.Tactic (foo)",
            "",
            "   ",
            "Mathlib.\u{0}Tactic",
        ];
        for m in malicious {
            let res = peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
                "source_problem_text": "x", "root_formal_statement": "x",
                "problem_imports": [m],
            }).as_object().unwrap().clone())).await;
            assert!(res.is_err(), "malformed import {:?} must be rejected, not compiled", m);
        }

        // A well-formed module path must still be accepted (this isn't just
        // rejecting everything).
        let ok = peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
            "problem_imports": ["Mathlib.NumberTheory.Padics.PadicVal.Basic"],
        }).as_object().unwrap().clone())).await;
        assert!(ok.is_ok(), "a syntactically valid module path must not be rejected: {:?}", ok);
    }

    /// SOUNDNESS: `lean_declaration_lookup`'s `names` are written verbatim into
    /// `#check {name}\n` Lean source. Same injection surface as
    /// problem_imports, one door earlier — a name containing a newline could
    /// append arbitrary Lean commands that execute inside the verifier process
    /// during the lookup itself.
    #[tokio::test]
    async fn test_lean_declaration_lookup_rejects_malformed_names() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
        }).as_object().unwrap().clone())).await.unwrap());

        let malicious = [
            "Nat.factorization\naxiom cheat : False",
            "Nat.factorization -- comment",
            "Nat.factorization; #exit",
            "",
            "   ",
        ];
        for n in malicious {
            let res = peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
                "problem_version_id": pv["problem_version_id"], "names": [n],
            }).as_object().unwrap().clone())).await;
            assert!(res.is_err(), "malformed declaration name {:?} must be rejected", n);
        }

        let too_many: Vec<String> = (0..51).map(|i| format!("Nat.foo{}", i)).collect();
        let res = peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "names": too_many,
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "more than 50 names must be rejected");
    }
}
