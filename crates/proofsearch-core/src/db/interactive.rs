//! Persistence CRUD for the `interactive_proof_*` tables (issue #160's schema,
//! issue #161's first Rust callers). Follows the same convention as
//! `crate::db::{insert_problem_version, insert_obligation, ...}` in
//! `db/mod.rs`: plain functions over a `&Connection`/`&Transaction`-like
//! parameter, hand-rolled row (de)serialization (no ORM), UUIDs/timestamps
//! stored as TEXT (RFC3339), matching the rest of this schema.
//!
//! TRUST BOUNDARY (restated once more, see `schema_v1.rs`'s doc comment above
//! `interactive_proof_sessions` and `crate::lean::interactive`/
//! `crate::lean::observation`'s module docs for the full statement): nothing
//! in this file can mark an `episode_obligations` row proved. The only
//! mutating function here that touches verification status at all is
//! [`update_reconstructed_script_verification`], and even that only records
//! the outcome of a resubmission that went through the EXISTING
//! `attempt_claim`/`episode_step` path — it does not itself decide, compute,
//! or influence that outcome.

use chrono::{DateTime, Utc};
use rusqlite::{Connection, OptionalExtension};
use uuid::Uuid;

fn parse_uuid(s: &str) -> Result<Uuid, rusqlite::Error> {
    Uuid::parse_str(s).map_err(|e| {
        rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e))
    })
}

fn parse_datetime(s: &str) -> Result<DateTime<Utc>, rusqlite::Error> {
    DateTime::parse_from_rfc3339(s)
        .map(|dt| dt.with_timezone(&Utc))
        .map_err(|e| rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e)))
}

// --- Sessions --------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct SessionRow {
    pub id: Uuid,
    pub episode_id: Uuid,
    pub problem_version_id: Uuid,
    pub obligation_id: Uuid,
    pub backend_kind: String,
    pub backend_version: Option<String>,
    pub import_manifest_hash: Option<String>,
    pub environment_hash: Option<String>,
    pub state: String,
    pub root_node_id: Option<Uuid>,
    pub selected_final_node_id: Option<Uuid>,
    pub reconstructed_script_hash: Option<String>,
    pub created_at: DateTime<Utc>,
    pub closed_at: Option<DateTime<Utc>>,
    pub close_reason: Option<String>,
}

/// Inputs for [`insert_session`] — a session always starts `state = 'open'`,
/// `root_node_id = NULL` (the "create now, link later" shape #160's own
/// tests use — the root node references this session's id via its own
/// `session_id` column, so it can only be inserted after this row exists;
/// [`set_session_root_node`] links it back once inserted).
pub struct NewSession {
    pub id: Uuid,
    pub episode_id: Uuid,
    pub problem_version_id: Uuid,
    pub obligation_id: Uuid,
    pub backend_kind: String,
    pub backend_version: Option<String>,
    pub import_manifest_hash: Option<String>,
    pub environment_hash: Option<String>,
    pub created_at: DateTime<Utc>,
}

pub fn insert_session(conn: &Connection, s: &NewSession) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO interactive_proof_sessions (
            id, episode_id, problem_version_id, obligation_id, backend_kind, backend_version,
            import_manifest_hash, environment_hash, state, created_at
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, 'open', ?9)",
        rusqlite::params![
            s.id.to_string(),
            s.episode_id.to_string(),
            s.problem_version_id.to_string(),
            s.obligation_id.to_string(),
            s.backend_kind,
            s.backend_version,
            s.import_manifest_hash,
            s.environment_hash,
            s.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

pub fn get_session(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<SessionRow>> {
    conn.query_row(
        "SELECT id, episode_id, problem_version_id, obligation_id, backend_kind, backend_version,
                import_manifest_hash, environment_hash, state, root_node_id, selected_final_node_id,
                reconstructed_script_hash, created_at, closed_at, close_reason
         FROM interactive_proof_sessions WHERE id = ?1",
        [id.to_string()],
        row_to_session,
    )
    .optional()
}

fn row_to_session(row: &rusqlite::Row) -> rusqlite::Result<SessionRow> {
    let root_node_id: Option<String> = row.get(9)?;
    let selected_final_node_id: Option<String> = row.get(10)?;
    let closed_at: Option<String> = row.get(13)?;
    Ok(SessionRow {
        id: parse_uuid(&row.get::<_, String>(0)?)?,
        episode_id: parse_uuid(&row.get::<_, String>(1)?)?,
        problem_version_id: parse_uuid(&row.get::<_, String>(2)?)?,
        obligation_id: parse_uuid(&row.get::<_, String>(3)?)?,
        backend_kind: row.get(4)?,
        backend_version: row.get(5)?,
        import_manifest_hash: row.get(6)?,
        environment_hash: row.get(7)?,
        state: row.get(8)?,
        root_node_id: root_node_id.map(|s| parse_uuid(&s)).transpose()?,
        selected_final_node_id: selected_final_node_id.map(|s| parse_uuid(&s)).transpose()?,
        reconstructed_script_hash: row.get(11)?,
        created_at: parse_datetime(&row.get::<_, String>(12)?)?,
        closed_at: closed_at.map(|s| parse_datetime(&s)).transpose()?,
        close_reason: row.get(14)?,
    })
}

pub fn set_session_root_node(conn: &Connection, session_id: Uuid, node_id: Uuid) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE interactive_proof_sessions SET root_node_id = ?1 WHERE id = ?2",
        (node_id.to_string(), session_id.to_string()),
    )?;
    Ok(())
}

pub fn set_session_selected_node(conn: &Connection, session_id: Uuid, node_id: Uuid) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE interactive_proof_sessions SET selected_final_node_id = ?1 WHERE id = ?2",
        (node_id.to_string(), session_id.to_string()),
    )?;
    Ok(())
}

pub fn set_session_reconstructed_script_hash(conn: &Connection, session_id: Uuid, hash: &str) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE interactive_proof_sessions SET reconstructed_script_hash = ?1 WHERE id = ?2",
        (hash, session_id.to_string()),
    )?;
    Ok(())
}

/// Marks a session closed with one of the three reasons #161's
/// `proof_session_close` exposes. `state` always becomes `'closed'` (the only
/// terminal value #160's schema models); `close_reason` preserves which of
/// the three the caller actually meant, so the trace stays legible without
/// widening `state` itself. See the CHECK constraint on
/// `interactive_proof_sessions` in `schema_v1.rs`.
pub fn close_session(
    conn: &Connection,
    session_id: Uuid,
    closed_at: DateTime<Utc>,
    close_reason: &str,
) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE interactive_proof_sessions SET state = 'closed', closed_at = ?1, close_reason = ?2 WHERE id = ?3",
        (closed_at.to_rfc3339(), close_reason, session_id.to_string()),
    )?;
    Ok(())
}

// --- Nodes -------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct NodeRow {
    pub id: Uuid,
    pub session_id: Uuid,
    pub parent_node_id: Option<Uuid>,
    pub depth: i64,
    pub node_kind: String,
    pub proof_state_hash: String,
    pub goals_json: String,
    pub selected_goal_index: Option<i64>,
    pub status: String,
    pub created_at: DateTime<Utc>,
}

pub struct NewNode {
    pub id: Uuid,
    pub session_id: Uuid,
    pub parent_node_id: Option<Uuid>,
    pub depth: i64,
    pub node_kind: String,
    pub proof_state_hash: String,
    pub goals_json: String,
    pub selected_goal_index: Option<i64>,
    pub status: String,
    pub created_at: DateTime<Utc>,
}

pub fn insert_node(conn: &Connection, n: &NewNode) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO interactive_proof_nodes (
            id, session_id, parent_node_id, depth, node_kind, proof_state_hash, goals_json,
            selected_goal_index, status, created_at
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
        rusqlite::params![
            n.id.to_string(),
            n.session_id.to_string(),
            n.parent_node_id.map(|u| u.to_string()),
            n.depth,
            n.node_kind,
            n.proof_state_hash,
            n.goals_json,
            n.selected_goal_index,
            n.status,
            n.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

fn row_to_node(row: &rusqlite::Row) -> rusqlite::Result<NodeRow> {
    let parent_node_id: Option<String> = row.get(2)?;
    Ok(NodeRow {
        id: parse_uuid(&row.get::<_, String>(0)?)?,
        session_id: parse_uuid(&row.get::<_, String>(1)?)?,
        parent_node_id: parent_node_id.map(|s| parse_uuid(&s)).transpose()?,
        depth: row.get(3)?,
        node_kind: row.get(4)?,
        proof_state_hash: row.get(5)?,
        goals_json: row.get(6)?,
        selected_goal_index: row.get(7)?,
        status: row.get(8)?,
        created_at: parse_datetime(&row.get::<_, String>(9)?)?,
    })
}

const NODE_COLUMNS: &str = "id, session_id, parent_node_id, depth, node_kind, proof_state_hash, goals_json, \
     selected_goal_index, status, created_at";

pub fn get_node(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<NodeRow>> {
    conn.query_row(
        &format!("SELECT {NODE_COLUMNS} FROM interactive_proof_nodes WHERE id = ?1"),
        [id.to_string()],
        row_to_node,
    )
    .optional()
}

/// Every node belonging to a session, oldest first — used by
/// `proof_session_observe`'s branch summary and `proof_session_reconstruct`'s
/// root-to-selected-node walk.
pub fn list_nodes_for_session(conn: &Connection, session_id: Uuid) -> rusqlite::Result<Vec<NodeRow>> {
    let mut stmt = conn.prepare(&format!(
        "SELECT {NODE_COLUMNS} FROM interactive_proof_nodes WHERE session_id = ?1 ORDER BY created_at ASC"
    ))?;
    let rows = stmt.query_map([session_id.to_string()], row_to_node)?;
    rows.collect()
}

/// Direct children of `parent_node_id` within `session_id` — the sibling set
/// a branch summary / `proof_session_branch` cares about.
pub fn list_child_nodes(conn: &Connection, session_id: Uuid, parent_node_id: Uuid) -> rusqlite::Result<Vec<NodeRow>> {
    let mut stmt = conn.prepare(&format!(
        "SELECT {NODE_COLUMNS} FROM interactive_proof_nodes WHERE session_id = ?1 AND parent_node_id = ?2 ORDER BY created_at ASC"
    ))?;
    let rows = stmt.query_map([session_id.to_string(), parent_node_id.to_string()], row_to_node)?;
    rows.collect()
}

// --- Steps ---------------------------------------------------------------

pub struct NewStep {
    pub id: Uuid,
    pub session_id: Uuid,
    pub parent_node_id: Uuid,
    pub child_node_id: Option<Uuid>,
    pub tactic_text_hash: String,
    pub tactic_text_artifact_hash: Option<String>,
    pub redacted_text: bool,
    pub outcome: String,
    pub diagnostic_json: Option<String>,
    pub diagnostics_hash: Option<String>,
    pub wall_time_ms: Option<i64>,
    pub created_at: DateTime<Utc>,
}

pub fn insert_step(conn: &Connection, s: &NewStep) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO interactive_proof_steps (
            id, session_id, parent_node_id, child_node_id, tactic_text_hash, tactic_text_artifact_hash,
            redacted_text, outcome, diagnostic_json, diagnostics_hash, wall_time_ms, created_at
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
        rusqlite::params![
            s.id.to_string(),
            s.session_id.to_string(),
            s.parent_node_id.to_string(),
            s.child_node_id.map(|u| u.to_string()),
            s.tactic_text_hash,
            s.tactic_text_artifact_hash,
            s.redacted_text as i64,
            s.outcome,
            s.diagnostic_json,
            s.diagnostics_hash,
            s.wall_time_ms,
            s.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

/// Count of steps recorded for a session (applied + failed) — cheap summary
/// data for `proof_session_observe` without materializing every row.
pub fn count_steps_for_session(conn: &Connection, session_id: Uuid) -> rusqlite::Result<i64> {
    conn.query_row(
        "SELECT COUNT(*) FROM interactive_proof_steps WHERE session_id = ?1",
        [session_id.to_string()],
        |row| row.get(0),
    )
}

// --- Reconstructed scripts --------------------------------------------------

#[derive(Debug, Clone)]
pub struct ReconstructedScriptRow {
    pub id: Uuid,
    pub session_id: Uuid,
    pub final_node_id: Uuid,
    pub proof_format: String,
    pub proof_source_hash: String,
    pub proof_source_artifact_hash: Option<String>,
    pub reports_complete: bool,
    pub verified_attempt_id: Option<Uuid>,
    pub verification_outcome: Option<String>,
    pub created_at: DateTime<Utc>,
}

pub struct NewReconstructedScript {
    pub id: Uuid,
    pub session_id: Uuid,
    pub final_node_id: Uuid,
    pub proof_format: String,
    pub proof_source_hash: String,
    pub proof_source_artifact_hash: Option<String>,
    pub reports_complete: bool,
    pub created_at: DateTime<Utc>,
}

pub fn insert_reconstructed_script(conn: &Connection, r: &NewReconstructedScript) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO interactive_proof_reconstructed_scripts (
            id, session_id, final_node_id, proof_format, proof_source_hash, proof_source_artifact_hash,
            reports_complete, created_at
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
        rusqlite::params![
            r.id.to_string(),
            r.session_id.to_string(),
            r.final_node_id.to_string(),
            r.proof_format,
            r.proof_source_hash,
            r.proof_source_artifact_hash,
            r.reports_complete as i64,
            r.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

const RECONSTRUCTED_SCRIPT_COLUMNS: &str = "id, session_id, final_node_id, proof_format, proof_source_hash, \
     proof_source_artifact_hash, reports_complete, verified_attempt_id, verification_outcome, created_at";

fn row_to_reconstructed_script(row: &rusqlite::Row) -> rusqlite::Result<ReconstructedScriptRow> {
    let verified_attempt_id: Option<String> = row.get(7)?;
    Ok(ReconstructedScriptRow {
        id: parse_uuid(&row.get::<_, String>(0)?)?,
        session_id: parse_uuid(&row.get::<_, String>(1)?)?,
        final_node_id: parse_uuid(&row.get::<_, String>(2)?)?,
        proof_format: row.get(3)?,
        proof_source_hash: row.get(4)?,
        proof_source_artifact_hash: row.get(5)?,
        reports_complete: row.get::<_, i64>(6)? != 0,
        verified_attempt_id: verified_attempt_id.map(|s| parse_uuid(&s)).transpose()?,
        verification_outcome: row.get(8)?,
        created_at: parse_datetime(&row.get::<_, String>(9)?)?,
    })
}

/// Every reconstructed script for a session, newest first — used by
/// `proof_session_observe`'s "available reconstructions" summary so a caller
/// can see prior reconstruction/promotion attempts without a second lookup.
pub fn list_reconstructed_scripts_for_session(conn: &Connection, session_id: Uuid) -> rusqlite::Result<Vec<ReconstructedScriptRow>> {
    let mut stmt = conn.prepare(&format!(
        "SELECT {RECONSTRUCTED_SCRIPT_COLUMNS} FROM interactive_proof_reconstructed_scripts WHERE session_id = ?1 ORDER BY created_at DESC"
    ))?;
    let rows = stmt.query_map([session_id.to_string()], row_to_reconstructed_script)?;
    rows.collect()
}

pub fn get_reconstructed_script(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<ReconstructedScriptRow>> {
    conn.query_row(
        &format!("SELECT {RECONSTRUCTED_SCRIPT_COLUMNS} FROM interactive_proof_reconstructed_scripts WHERE id = ?1"),
        [id.to_string()],
        row_to_reconstructed_script,
    )
    .optional()
}

/// Links a reconstructed script to the real `action_attempts` row a
/// resubmission through the EXISTING `attempt_claim`/`episode_step` path
/// produced, and records that attempt's resulting status as
/// `verification_outcome`. This is the ONLY function in this module that
/// touches verification status, and it never decides that status itself —
/// see the module doc.
pub fn update_reconstructed_script_verification(
    conn: &Connection,
    id: Uuid,
    verified_attempt_id: Uuid,
    verification_outcome: &str,
) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE interactive_proof_reconstructed_scripts SET verified_attempt_id = ?1, verification_outcome = ?2 WHERE id = ?3",
        (verified_attempt_id.to_string(), verification_outcome, id.to_string()),
    )?;
    Ok(())
}
