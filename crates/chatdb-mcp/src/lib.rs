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
use chatdb_proof_core::models::action::{TypedAction, ActionRequest, ActionRole, StepDisposition};
use chatdb_proof_core::models::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use chatdb_proof_core::models::reward::{RewardComponent, RewardComponentId, RewardPolicy};
use chatdb_proof_core::hashing::canonical_hash;

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
    /// Dev convenience: also mark fidelity_status='approved' so episodes can start
    /// immediately, skipping the separate problem_approve_fidelity call.
    #[serde(default)]
    pub approve: bool,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemApproveFidelityArgs {
    pub problem_version_id: String,
    #[serde(default)]
    pub approver_id: Option<String>,
    #[serde(default)]
    pub notes: Option<String>,
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

    let (source_text, root_statement): (String, String) = conn.query_row(
        "SELECT source_problem_text, root_formal_statement FROM problem_versions WHERE id = ?1",
        [&pv_id],
        |row| Ok((row.get(0)?, row.get(1)?)),
    ).map_err(rs)?;

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
    lean_src.push_str("import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.NormNum\n\n");
    for o in &lean_order {
        if o.status != "proved" {
            continue;
        }
        let proof = winning_proof.get(&o.id).cloned()
            .unwrap_or_else(|| "  sorry -- proof term not recorded in trajectory".to_string());
        lean_src.push_str(&format!("theorem {} : {} := by\n{}\n\n", o.theorem_name, o.lean_statement, proof.trim_end()));
    }

    if format == "lean" {
        return Ok(lean_src);
    }

    // Markdown dossier.
    let mut md = String::new();
    let headline_marker = match outcome.as_deref() {
        Some("certified") => "✅ CERTIFIED",
        Some("refuted") => "❌ REFUTED",
        Some("gave_up") => "🏳️ GAVE UP",
        Some(other) => other,
        None => "🔄 IN PROGRESS",
    };
    md.push_str(&format!("# {} — {}\n\n", headline_marker, source_text.trim()));
    md.push_str(&format!("**Root goal:** `{}`\n\n", root_statement));
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

    md.push_str("\n## The proof, assembled\n\n");
    if lean_order.iter().any(|o| o.status == "proved") {
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
            .with_server_info(Implementation::new("chatdb-mcp", "0.2.0"))
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, McpError> {
        let tools = vec![
            make_tool::<EnvironmentDescribeArgs>("environment_describe", "Return environment version, supported protocol, tool schemas, capabilities"),
            make_tool::<ProblemCreateArgs>("problem_create", "Register a new problem version (source text + root formal statement). Set approve=true to skip a separate fidelity approval for dev use"),
            make_tool::<ProblemApproveFidelityArgs>("problem_approve_fidelity", "Mark a problem version's fidelity_status as approved so episodes can be created against it"),
            make_tool::<ProblemListArgs>("problem_list", "List known problem versions (id, state, fidelity_status, root statement)"),
            make_tool::<EpisodeCreateArgs>("episode_create", "Initialize an episode from an approved problem version + config. Returns first observation"),
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
                    "environment_version": "0.2.0",
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
                        {"type": "give_up"}
                    ],
                    "prover_loop": "problem_create(approve=true) -> episode_create -> episode_observe -> attempt_claim -> episode_step(action, expected_revision = action_request.episode_revision) -> repeat observe/claim/step until outcome is set"
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

                let (fidelity_status, state) = if args.approve {
                    ("approved", "PROVING")
                } else {
                    ("pending", "CREATED")
                };
                let fidelity_approval_id = if args.approve { Some(Uuid::new_v4().to_string()) } else { None };

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                tx.execute(
                    "INSERT INTO problem_versions (
                        id, source_problem_text, source_problem_hash, source_metadata_json,
                        root_formal_statement, root_statement_hash, normalized_root_rendering,
                        environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
                        state, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, 'manual', ?10, ?11, ?12)",
                    (
                        pv_id.to_string(), &args.source_problem_text, &source_hash, &metadata,
                        &args.root_formal_statement, &root_hash, &rendering,
                        &env_hash, fidelity_status, &fidelity_approval_id, state,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "problem_version_id": pv_id.to_string(),
                    "fidelity_status": fidelity_status,
                    "state": state,
                    "environment_hash": env_hash,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_approve_fidelity" => {
                let args: ProblemApproveFidelityArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let exists: Option<String> = tx.query_row(
                    "SELECT id FROM problem_versions WHERE id = ?1",
                    [&args.problem_version_id],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                if exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id)));
                }

                let approval_id = Uuid::new_v4().to_string();
                tx.execute(
                    "UPDATE problem_versions SET fidelity_status = 'approved', fidelity_method = 'manual', fidelity_approval_id = ?1 WHERE id = ?2",
                    (&approval_id, &args.problem_version_id),
                ).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let _ = (args.approver_id, args.notes); // reserved for episode_fidelity_reviews once episode-scoped review lands
                let res = serde_json::json!({ "problem_version_id": args.problem_version_id, "fidelity_status": "approved", "fidelity_approval_id": approval_id });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_list" => {
                let args: ProblemListArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let limit = args.limit.unwrap_or(50).clamp(1, 500);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, state, fidelity_status, root_formal_statement, created_at
                     FROM problem_versions ORDER BY created_at DESC LIMIT ?1"
                ).map_err(rs)?;
                let rows = stmt.query_map([limit], |row| {
                    Ok(serde_json::json!({
                        "problem_version_id": row.get::<_, String>(0)?,
                        "state": row.get::<_, String>(1)?,
                        "fidelity_status": row.get::<_, String>(2)?,
                        "root_formal_statement": row.get::<_, String>(3)?,
                        "created_at": row.get::<_, String>(4)?,
                    }))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;

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
                    Some("approved") => {}
                    Some(other) => return Err(mcp_invalid_params(format!(
                        "problem_version {} is not fidelity-approved (status={}); call problem_approve_fidelity first",
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
                        "Invalid params: {}. `action` must be one of: {{\"type\":\"solve\",\"proof_term\":\"  norm_num\"}} | {{\"type\":\"decompose\",\"sub_lemmas\":[\"...\"]}} | {{\"type\":\"give_up\"}} (see environment_describe.action_schema)", e
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
                            tx.execute(
                                "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                                (EpisodeOutcome::Certified.to_string(), TerminationReason::RootProved.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                            ).map_err(rs)?;
                            // Advance the problem lifecycle too, so problem_list is a
                            // status board rather than a stale cache of PROVING rows.
                            tx.execute(
                                "UPDATE problem_versions SET state = 'COMPLETE'
                                 WHERE id = (SELECT problem_version_id FROM episodes WHERE id = ?1)
                                 AND state = 'PROVING'",
                                [args.episode_id.clone()],
                            ).map_err(rs)?;
                            is_terminated = true;
                            term_reason = Some(TerminationReason::RootProved);
                            outcome_enum = Some(EpisodeOutcome::Certified);
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
                let is_solve = matches!(args.action, TypedAction::Solve { .. });
                let mut reward_components = Vec::new();
                let policy = RewardPolicy::default_policy();
                if disposition == StepDisposition::Accepted {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::StepPenalty,
                        value_scaled: policy.step_penalty,
                    });
                    if is_solve && accepted {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelPass,
                            value_scaled: policy.kernel_pass,
                        });
                    } else if is_solve && !is_terminated {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelFail,
                            value_scaled: policy.kernel_fail,
                        });
                    }
                }
                if outcome_enum == Some(EpisodeOutcome::Certified) {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::TerminalSuccess,
                        value_scaled: policy.terminal_success,
                    });
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

                let res = serde_json::json!({
                    "accepted": accepted,
                    "disposition": disposition,
                    "counts_as_environment_step": disposition == StepDisposition::Accepted,
                    "reward": reward_components,
                    "outcome": outcome_enum,
                    "termination_reason": term_reason,
                    "truncation_reason": trunc_reason,
                    "diagnostics": error_msg,
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
    use chatdb_proof_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult};

    struct MockGateway;
    impl LeanGateway for MockGateway {
        fn verify_exact(
            &self,
            obligation: &Obligation,
            candidate_source: &str,
            _approved_dependency_ids: &[Uuid],
            environment: &str,
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
                dependency_use_report: None,
                wall_time_ms: 1,
                lean_cpu_time_ms: 1,
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
        assert_eq!(list_res.tools.len(), 16);

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
            "approve": true,
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
            "source_problem_text": "x", "root_formal_statement": "x", "approve": true,
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
            "approve": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

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
    }

    /// A solve that fails Lean verification must NOT terminate the episode, must
    /// count as a step, and must leave the obligation open (re-attemptable).
    #[tokio::test]
    async fn test_solve_kernel_fail_does_not_terminate() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "approve": true,
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
            "source_problem_text": "x", "root_formal_statement": "x", "approve": true,
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
            "source_problem_text": "x", "root_formal_statement": "x", "approve": true,
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
            "source_problem_text": "x", "root_formal_statement": "x", "approve": true,
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
}
