use chrono::{DateTime, Utc};
use rusqlite::Connection;
use uuid::Uuid;

use crate::models::{
    AttemptDiagnostic, AttemptOutcome, EdgeKind, FidelityStatus, Obligation, ObligationCreator,
    ObligationEdge, ObligationKind, ObligationStatus, Polarity, ProblemState, ProblemVersion,
    VerifiedLemma,
};

fn parse_uuid(s: &str) -> Result<Uuid, rusqlite::Error> {
    Uuid::parse_str(s).map_err(|e| {
        rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e))
    })
}

fn parse_datetime(s: &str) -> Result<DateTime<Utc>, rusqlite::Error> {
    DateTime::parse_from_rfc3339(s)
        .map(|dt| dt.with_timezone(&Utc))
        .map_err(|e| {
            rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e))
        })
}

pub mod schema_v1;
pub mod migrations;

/// Initialize all schemas, tables, and indexes for v1 (Episode-Local isolation).
pub fn initialize_db(conn: &Connection) -> rusqlite::Result<()> {
    schema_v1::initialize_v1_db(conn)
}

// --- CRUD Operations for ProblemVersion ---

pub fn insert_problem_version(conn: &Connection, pv: &ProblemVersion) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14)",
        rusqlite::params![
            pv.id.to_string(),
            pv.source_problem_text,
            pv.source_problem_hash,
            pv.source_metadata_json,
            pv.root_formal_statement,
            pv.root_statement_hash,
            pv.normalized_root_rendering,
            pv.environment_hash,
            pv.fidelity_status.to_string(),
            pv.fidelity_method,
            pv.fidelity_approval_id.map(|u| u.to_string()),
            pv.root_obligation_id.map(|u| u.to_string()),
            pv.state.to_string(),
            pv.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

pub fn get_problem_version(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<ProblemVersion>> {
    let mut stmt = conn.prepare(
        "SELECT id, source_problem_text, source_problem_hash, source_metadata_json,
                root_formal_statement, root_statement_hash, normalized_root_rendering,
                environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
                root_obligation_id, state, created_at
         FROM problem_versions WHERE id = ?1",
    )?;
    let mut rows = stmt.query([id.to_string()])?;
    if let Some(row) = rows.next()? {
        let id_str: String = row.get(0)?;
        let parsed_id = parse_uuid(&id_str)?;
        let fidelity_approval_id_str: Option<String> = row.get(10)?;
        let fidelity_approval_id = fidelity_approval_id_str.map(|s| parse_uuid(&s)).transpose()?;
        let root_obligation_id_str: Option<String> = row.get(11)?;
        let root_obligation_id = root_obligation_id_str.map(|s| parse_uuid(&s)).transpose()?;
        let created_at_str: String = row.get(13)?;
        let created_at = parse_datetime(&created_at_str)?;

        let fidelity_status_str: String = row.get(8)?;
        let fidelity_status = FidelityStatus::try_from(fidelity_status_str.as_str())
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(8, rusqlite::types::Type::Text, e.into()))?;

        let state_str: String = row.get(12)?;
        let state = ProblemState::try_from(state_str.as_str())
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(12, rusqlite::types::Type::Text, e.into()))?;

        Ok(Some(ProblemVersion {
            id: parsed_id,
            source_problem_text: row.get(1)?,
            source_problem_hash: row.get(2)?,
            source_metadata_json: row.get(3)?,
            root_formal_statement: row.get(4)?,
            root_statement_hash: row.get(5)?,
            normalized_root_rendering: row.get(6)?,
            environment_hash: row.get(7)?,
            fidelity_status,
            fidelity_method: row.get(9)?,
            fidelity_approval_id,
            root_obligation_id,
            state,
            created_at,
        }))
    } else {
        Ok(None)
    }
}

pub fn update_problem_version_state(
    conn: &Connection,
    id: Uuid,
    state: ProblemState,
) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE problem_versions SET state = ?1 WHERE id = ?2",
        rusqlite::params![state.to_string(), id.to_string()],
    )?;
    Ok(())
}

pub fn approve_fidelity(
    conn: &Connection,
    id: Uuid,
    approval_id: Uuid,
    root_obligation_id: Uuid,
) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE problem_versions
         SET fidelity_status = 'approved', fidelity_approval_id = ?1, root_obligation_id = ?2
         WHERE id = ?3",
        rusqlite::params![approval_id.to_string(), root_obligation_id.to_string(), id.to_string()],
    )?;
    Ok(())
}

// --- CRUD Operations for Obligation ---

pub fn insert_obligation(conn: &Connection, o: &Obligation) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO obligations (
            id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
            natural_description, status, depth_from_root, created_by, created_by_epoch_id,
            superseded_by_id, proved_lemma_id, refutation_lemma_id, failure_lesson,
            attempt_count, created_at, closed_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18)",
        rusqlite::params![
            o.id.to_string(),
            o.problem_version_id.to_string(),
            o.kind.to_string(),
            o.theorem_name,
            o.lean_statement,
            o.statement_hash,
            o.natural_description,
            o.status.to_string(),
            o.depth_from_root,
            o.created_by.to_string(),
            o.created_by_epoch_id.map(|u| u.to_string()),
            o.superseded_by_id.map(|u| u.to_string()),
            o.proved_lemma_id.map(|u| u.to_string()),
            o.refutation_lemma_id.map(|u| u.to_string()),
            o.failure_lesson,
            o.attempt_count,
            o.created_at.to_rfc3339(),
            o.closed_at.map(|dt| dt.to_rfc3339()),
        ],
    )?;
    Ok(())
}

fn map_obligation_row(row: &rusqlite::Row) -> rusqlite::Result<Obligation> {
    let id_str: String = row.get(0)?;
    let id = parse_uuid(&id_str)?;
    let problem_version_id_str: String = row.get(1)?;
    let problem_version_id = parse_uuid(&problem_version_id_str)?;

    let kind_str: String = row.get(2)?;
    let kind = ObligationKind::try_from(kind_str.as_str())
        .map_err(|e| rusqlite::Error::FromSqlConversionFailure(2, rusqlite::types::Type::Text, e.into()))?;

    let status_str: String = row.get(7)?;
    let status = ObligationStatus::try_from(status_str.as_str())
        .map_err(|e| rusqlite::Error::FromSqlConversionFailure(7, rusqlite::types::Type::Text, e.into()))?;

    let created_by_str: String = row.get(9)?;
    let created_by = ObligationCreator::try_from(created_by_str.as_str())
        .map_err(|e| rusqlite::Error::FromSqlConversionFailure(9, rusqlite::types::Type::Text, e.into()))?;

    let created_by_epoch_id_str: Option<String> = row.get(10)?;
    let created_by_epoch_id = created_by_epoch_id_str.map(|s| parse_uuid(&s)).transpose()?;

    let superseded_by_id_str: Option<String> = row.get(11)?;
    let superseded_by_id = superseded_by_id_str.map(|s| parse_uuid(&s)).transpose()?;

    let proved_lemma_id_str: Option<String> = row.get(12)?;
    let proved_lemma_id = proved_lemma_id_str.map(|s| parse_uuid(&s)).transpose()?;

    let refutation_lemma_id_str: Option<String> = row.get(13)?;
    let refutation_lemma_id = refutation_lemma_id_str.map(|s| parse_uuid(&s)).transpose()?;

    let created_at_str: String = row.get(16)?;
    let created_at = parse_datetime(&created_at_str)?;

    let closed_at_str: Option<String> = row.get(17)?;
    let closed_at = closed_at_str.map(|s| parse_datetime(&s)).transpose()?;

    Ok(Obligation {
        id,
        problem_version_id,
        kind,
        theorem_name: row.get(3)?,
        lean_statement: row.get(4)?,
        statement_hash: row.get(5)?,
        natural_description: row.get(6)?,
        status,
        depth_from_root: row.get(8)?,
        created_by,
        created_by_epoch_id,
        superseded_by_id,
        proved_lemma_id,
        refutation_lemma_id,
        failure_lesson: row.get(14)?,
        attempt_count: row.get(15)?,
        created_at,
        closed_at,
    })
}

pub fn get_obligation(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<Obligation>> {
    let mut stmt = conn.prepare(
        "SELECT id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
                natural_description, status, depth_from_root, created_by, created_by_epoch_id,
                superseded_by_id, proved_lemma_id, refutation_lemma_id, failure_lesson,
                attempt_count, created_at, closed_at
         FROM obligations WHERE id = ?1",
    )?;
    let mut rows = stmt.query([id.to_string()])?;
    if let Some(row) = rows.next()? {
        Ok(Some(map_obligation_row(row)?))
    } else {
        Ok(None)
    }
}

pub fn get_obligations_for_problem(
    conn: &Connection,
    problem_id: Uuid,
) -> rusqlite::Result<Vec<Obligation>> {
    let mut stmt = conn.prepare(
        "SELECT id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
                natural_description, status, depth_from_root, created_by, created_by_epoch_id,
                superseded_by_id, proved_lemma_id, refutation_lemma_id, failure_lesson,
                attempt_count, created_at, closed_at
         FROM obligations WHERE problem_version_id = ?1",
    )?;
    let rows = stmt.query_map([problem_id.to_string()], map_obligation_row)?;
    let mut vec = Vec::new();
    for r in rows {
        vec.push(r?);
    }
    Ok(vec)
}

pub fn update_obligation_status(
    conn: &Connection,
    id: Uuid,
    status: ObligationStatus,
) -> rusqlite::Result<()> {
    conn.execute(
        "UPDATE obligations SET status = ?1 WHERE id = ?2",
        rusqlite::params![status.to_string(), id.to_string()],
    )?;
    Ok(())
}

// --- CRUD Operations for ObligationEdge ---

pub fn insert_edge(conn: &Connection, edge: &ObligationEdge) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO obligation_edges (
            parent_obligation_id, dependency_obligation_id, edge_kind, case_group, created_at
         ) VALUES (?1, ?2, ?3, ?4, ?5)",
        rusqlite::params![
            edge.parent_obligation_id.to_string(),
            edge.dependency_obligation_id.to_string(),
            edge.edge_kind.to_string(),
            edge.case_group,
            edge.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

pub fn get_edges_for_parent(
    conn: &Connection,
    parent_id: Uuid,
) -> rusqlite::Result<Vec<ObligationEdge>> {
    let mut stmt = conn.prepare(
        "SELECT parent_obligation_id, dependency_obligation_id, edge_kind, case_group, created_at
         FROM obligation_edges WHERE parent_obligation_id = ?1",
    )?;
    let rows = stmt.query_map([parent_id.to_string()], |row| {
        let parent_str: String = row.get(0)?;
        let parent_obligation_id = parse_uuid(&parent_str)?;
        let dep_str: String = row.get(1)?;
        let dependency_obligation_id = parse_uuid(&dep_str)?;
        let edge_kind_str: String = row.get(2)?;
        let edge_kind = EdgeKind::try_from(edge_kind_str.as_str())
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(2, rusqlite::types::Type::Text, e.into()))?;
        let created_at_str: String = row.get(4)?;
        let created_at = parse_datetime(&created_at_str)?;

        Ok(ObligationEdge {
            parent_obligation_id,
            dependency_obligation_id,
            edge_kind,
            case_group: row.get(3)?,
            created_at,
        })
    })?;
    let mut vec = Vec::new();
    for r in rows {
        vec.push(r?);
    }
    Ok(vec)
}

// --- CRUD Operations for AttemptDiagnostic (proposal_attempts) ---

pub fn insert_attempt(conn: &Connection, attempt: &AttemptDiagnostic) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO proposal_attempts (
            id, obligation_id, role, model_config_hash, prompt_hash, context_manifest_hash,
            candidate_source_artifact_hash, diagnostic_json, outcome, input_tokens, output_tokens,
            cost_usd_micros, wall_time_ms, lean_cpu_time_ms, created_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15)",
        rusqlite::params![
            attempt.id.to_string(),
            attempt.obligation_id.to_string(),
            attempt.role,
            attempt.model_config_hash,
            attempt.prompt_hash,
            attempt.context_manifest_hash,
            attempt.candidate_source_artifact_hash,
            attempt.diagnostic_json,
            attempt.outcome.to_string(),
            attempt.input_tokens,
            attempt.output_tokens,
            attempt.cost_usd_micros,
            attempt.wall_time_ms,
            attempt.lean_cpu_time_ms,
            attempt.created_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

pub fn get_attempts_for_obligation(
    conn: &Connection,
    obligation_id: Uuid,
) -> rusqlite::Result<Vec<AttemptDiagnostic>> {
    let mut stmt = conn.prepare(
        "SELECT id, obligation_id, role, model_config_hash, prompt_hash, context_manifest_hash,
                candidate_source_artifact_hash, diagnostic_json, outcome, input_tokens, output_tokens,
                cost_usd_micros, wall_time_ms, lean_cpu_time_ms, created_at
         FROM proposal_attempts WHERE obligation_id = ?1",
    )?;
    let rows = stmt.query_map([obligation_id.to_string()], |row| {
        let id_str: String = row.get(0)?;
        let id = parse_uuid(&id_str)?;
        let obl_id_str: String = row.get(1)?;
        let o_id = parse_uuid(&obl_id_str)?;
        let outcome_str: String = row.get(8)?;
        let outcome = AttemptOutcome::try_from(outcome_str.as_str())
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(8, rusqlite::types::Type::Text, e.into()))?;
        let created_at_str: String = row.get(14)?;
        let created_at = parse_datetime(&created_at_str)?;

        Ok(AttemptDiagnostic {
            id,
            obligation_id: o_id,
            role: row.get(2)?,
            model_config_hash: row.get(3)?,
            prompt_hash: row.get(4)?,
            context_manifest_hash: row.get(5)?,
            candidate_source_artifact_hash: row.get(6)?,
            diagnostic_json: row.get(7)?,
            outcome,
            input_tokens: row.get(9)?,
            output_tokens: row.get(10)?,
            cost_usd_micros: row.get(11)?,
            wall_time_ms: row.get(12)?,
            lean_cpu_time_ms: row.get(13)?,
            created_at,
        })
    })?;
    let mut vec = Vec::new();
    for r in rows {
        vec.push(r?);
    }
    Ok(vec)
}

// --- CRUD Operations for VerifiedLemma ---

pub fn insert_verified_lemma(conn: &Connection, lemma: &VerifiedLemma) -> rusqlite::Result<()> {
    conn.execute(
        "INSERT INTO verified_lemmas (
            id, obligation_id, polarity, theorem_name, statement_hash, proof_source_artifact_hash,
            compiled_artifact_hash, proof_term_hash, environment_hash, actual_dependency_ids_json,
            kernel_result_hash, verified_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
        rusqlite::params![
            lemma.id.to_string(),
            lemma.obligation_id.to_string(),
            lemma.polarity.to_string(),
            lemma.theorem_name,
            lemma.statement_hash,
            lemma.proof_source_artifact_hash,
            lemma.compiled_artifact_hash,
            lemma.proof_term_hash,
            lemma.environment_hash,
            lemma.actual_dependency_ids_json,
            lemma.kernel_result_hash,
            lemma.verified_at.to_rfc3339(),
        ],
    )?;
    Ok(())
}

pub fn get_verified_lemma(conn: &Connection, id: Uuid) -> rusqlite::Result<Option<VerifiedLemma>> {
    let mut stmt = conn.prepare(
        "SELECT id, obligation_id, polarity, theorem_name, statement_hash, proof_source_artifact_hash,
                compiled_artifact_hash, proof_term_hash, environment_hash, actual_dependency_ids_json,
                kernel_result_hash, verified_at
         FROM verified_lemmas WHERE id = ?1",
    )?;
    let mut rows = stmt.query([id.to_string()])?;
    if let Some(row) = rows.next()? {
        let id_str: String = row.get(0)?;
        let parsed_id = parse_uuid(&id_str)?;
        let obl_id_str: String = row.get(1)?;
        let obligation_id = parse_uuid(&obl_id_str)?;
        let polarity_str: String = row.get(2)?;
        let polarity = Polarity::try_from(polarity_str.as_str())
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(2, rusqlite::types::Type::Text, e.into()))?;
        let verified_at_str: String = row.get(11)?;
        let verified_at = parse_datetime(&verified_at_str)?;

        Ok(Some(VerifiedLemma {
            id: parsed_id,
            obligation_id,
            polarity,
            theorem_name: row.get(3)?,
            statement_hash: row.get(4)?,
            proof_source_artifact_hash: row.get(5)?,
            compiled_artifact_hash: row.get(6)?,
            proof_term_hash: row.get(7)?,
            environment_hash: row.get(8)?,
            actual_dependency_ids_json: row.get(9)?,
            kernel_result_hash: row.get(10)?,
            verified_at,
        }))
    } else {
        Ok(None)
    }
}

// --- Invariant 1: Transactional Updates ---

/// Invariant 1: Mark obligation as proved in the same transaction that inserts verified lemma.
pub fn commit_kernel_pass(
    conn: &mut Connection,
    obligation_id: Uuid,
    lemma: &VerifiedLemma,
) -> rusqlite::Result<()> {
    let tx = conn.transaction()?;

    // Insert verified lemma
    tx.execute(
        "INSERT INTO verified_lemmas (
            id, obligation_id, polarity, theorem_name, statement_hash, proof_source_artifact_hash,
            compiled_artifact_hash, proof_term_hash, environment_hash, actual_dependency_ids_json,
            kernel_result_hash, verified_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
        rusqlite::params![
            lemma.id.to_string(),
            lemma.obligation_id.to_string(),
            lemma.polarity.to_string(),
            lemma.theorem_name,
            lemma.statement_hash,
            lemma.proof_source_artifact_hash,
            lemma.compiled_artifact_hash,
            lemma.proof_term_hash,
            lemma.environment_hash,
            lemma.actual_dependency_ids_json,
            lemma.kernel_result_hash,
            lemma.verified_at.to_rfc3339(),
        ],
    )?;

    // Update obligation
    let closed_at = Utc::now().to_rfc3339();
    tx.execute(
        "UPDATE obligations
         SET status = 'proved', proved_lemma_id = ?1, attempt_count = attempt_count + 1, closed_at = ?2
         WHERE id = ?3",
        rusqlite::params![lemma.id.to_string(), closed_at, obligation_id.to_string()],
    )?;

    tx.commit()?;
    Ok(())
}

/// Invariant 1: Mark obligation as refuted in the same transaction that inserts verified lemma.
pub fn commit_kernel_refutation(
    conn: &mut Connection,
    obligation_id: Uuid,
    lemma: &VerifiedLemma,
) -> rusqlite::Result<()> {
    let tx = conn.transaction()?;

    // Insert verified lemma
    tx.execute(
        "INSERT INTO verified_lemmas (
            id, obligation_id, polarity, theorem_name, statement_hash, proof_source_artifact_hash,
            compiled_artifact_hash, proof_term_hash, environment_hash, actual_dependency_ids_json,
            kernel_result_hash, verified_at
         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
        rusqlite::params![
            lemma.id.to_string(),
            lemma.obligation_id.to_string(),
            lemma.polarity.to_string(),
            lemma.theorem_name,
            lemma.statement_hash,
            lemma.proof_source_artifact_hash,
            lemma.compiled_artifact_hash,
            lemma.proof_term_hash,
            lemma.environment_hash,
            lemma.actual_dependency_ids_json,
            lemma.kernel_result_hash,
            lemma.verified_at.to_rfc3339(),
        ],
    )?;

    // Update obligation
    let closed_at = Utc::now().to_rfc3339();
    tx.execute(
        "UPDATE obligations
         SET status = 'refuted', refutation_lemma_id = ?1, attempt_count = attempt_count + 1, closed_at = ?2
         WHERE id = ?3",
        rusqlite::params![lemma.id.to_string(), closed_at, obligation_id.to_string()],
    )?;

    tx.commit()?;
    Ok(())
}

#[cfg(all(test, feature = "legacy_tests"))]
mod tests {
    use super::*;

    fn setup_test_db() -> Connection {
        let conn = Connection::open_in_memory().unwrap();
        initialize_db(&conn).unwrap();
        conn
    }

    fn create_test_problem_version(id: Uuid, fidelity_status: FidelityStatus) -> ProblemVersion {
        ProblemVersion {
            id,
            source_problem_text: "Let n be an integer...".to_string(),
            source_problem_hash: "hash_problem".to_string(),
            source_metadata_json: "{}".to_string(),
            root_formal_statement: "theorem root ...".to_string(),
            root_statement_hash: "hash_root".to_string(),
            normalized_root_rendering: "root".to_string(),
            environment_hash: "env_hash".to_string(),
            fidelity_status,
            fidelity_method: "human".to_string(),
            fidelity_approval_id: None,
            root_obligation_id: None,
            state: ProblemState::Created,
            created_at: Utc::now(),
        }
    }

    fn create_test_obligation(id: Uuid, problem_id: Uuid, theorem_name: &str) -> Obligation {
        Obligation {
            id,
            problem_version_id: problem_id,
            kind: ObligationKind::Proof,
            theorem_name: theorem_name.to_string(),
            lean_statement: "theorem test_thm ...".to_string(),
            statement_hash: "hash_stmt".to_string(),
            natural_description: "A test obligation".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 1,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now(),
            closed_at: None,
        }
    }

    #[test]
    fn test_initialize_and_crud() {
        let conn = setup_test_db();
        let p_id = Uuid::new_v4();
        let pv = create_test_problem_version(p_id, FidelityStatus::Pending);

        insert_problem_version(&conn, &pv).unwrap();
        let retrieved_pv = get_problem_version(&conn, p_id).unwrap().unwrap();
        assert_eq!(retrieved_pv.source_problem_text, pv.source_problem_text);

        // Update state to Sketching (which doesn't require approved fidelity)
        update_problem_version_state(&conn, p_id, ProblemState::Sketching).unwrap();
        let updated_pv = get_problem_version(&conn, p_id).unwrap().unwrap();
        assert_eq!(updated_pv.state, ProblemState::Sketching);

        // Insert obligation
        let o_id = Uuid::new_v4();
        let o = create_test_obligation(o_id, p_id, "test_thm");
        insert_obligation(&conn, &o).unwrap();

        let retrieved_o = get_obligation(&conn, o_id).unwrap().unwrap();
        assert_eq!(retrieved_o.theorem_name, "test_thm");
        assert_eq!(retrieved_o.status, ObligationStatus::Open);
    }

    #[test]
    fn test_invariant_6_fidelity_approval_check_constraint() {
        let conn = setup_test_db();
        let p_id = Uuid::new_v4();
        let pv = create_test_problem_version(p_id, FidelityStatus::Pending);
        insert_problem_version(&conn, &pv).unwrap();

        // Attempting to change state to PROVING when fidelity is pending must fail check constraint
        let res = update_problem_version_state(&conn, p_id, ProblemState::Proving);
        assert!(res.is_err());
        if let Err(rusqlite::Error::SqliteFailure(err, _)) = res {
            assert_eq!(err.code, rusqlite::ffi::ErrorCode::ConstraintViolation);
        } else {
            panic!("Expected SQLite check constraint violation error");
        }

        // Now approve fidelity status
        approve_fidelity(&conn, p_id, Uuid::new_v4(), Uuid::new_v4()).unwrap();

        // Now changing state to PROVING must succeed
        update_problem_version_state(&conn, p_id, ProblemState::Proving).unwrap();
        let updated_pv = get_problem_version(&conn, p_id).unwrap().unwrap();
        assert_eq!(updated_pv.state, ProblemState::Proving);
    }

    #[test]
    fn test_obligation_status_lemma_check_constraints() {
        let conn = setup_test_db();
        let p_id = Uuid::new_v4();
        // Approve fidelity status first so state constraint is happy
        let pv = create_test_problem_version(p_id, FidelityStatus::Approved);
        insert_problem_version(&conn, &pv).unwrap();

        let o_id = Uuid::new_v4();
        let mut o = create_test_obligation(o_id, p_id, "test_thm");

        // Attempting to insert an obligation marked as 'proved' without a proved_lemma_id must fail check constraint
        o.status = ObligationStatus::Proved;
        let res = insert_obligation(&conn, &o);
        assert!(res.is_err());

        // Attempting to insert an obligation marked as 'refuted' without a refutation_lemma_id must fail check constraint
        o.status = ObligationStatus::Refuted;
        let res2 = insert_obligation(&conn, &o);
        assert!(res2.is_err());

        // Standard insertion of open obligation works
        o.status = ObligationStatus::Open;
        insert_obligation(&conn, &o).unwrap();

        // Directly updating status to proved without proved_lemma_id must fail
        let res3 = update_obligation_status(&conn, o_id, ObligationStatus::Proved);
        assert!(res3.is_err());
    }

    #[test]
    fn test_invariant_1_commit_kernel_pass_transactional() {
        let mut conn = setup_test_db();
        let p_id = Uuid::new_v4();
        let pv = create_test_problem_version(p_id, FidelityStatus::Approved);
        insert_problem_version(&conn, &pv).unwrap();

        let o_id = Uuid::new_v4();
        let o = create_test_obligation(o_id, p_id, "test_thm");
        insert_obligation(&conn, &o).unwrap();

        let l_id = Uuid::new_v4();
        let lemma = VerifiedLemma {
            id: l_id,
            obligation_id: o_id,
            polarity: Polarity::Positive,
            theorem_name: "test_thm".to_string(),
            statement_hash: "hash_stmt".to_string(),
            proof_source_artifact_hash: "proof_src_hash".to_string(),
            compiled_artifact_hash: "compiled_hash".to_string(),
            proof_term_hash: "proof_term_hash".to_string(),
            environment_hash: "env_hash".to_string(),
            actual_dependency_ids_json: "[]".to_string(),
            kernel_result_hash: "result_hash".to_string(),
            verified_at: Utc::now(),
        };

        // Transition through commit_kernel_pass transaction
        commit_kernel_pass(&mut conn, o_id, &lemma).unwrap();

        // Verify status and lemma
        let updated_o = get_obligation(&conn, o_id).unwrap().unwrap();
        assert_eq!(updated_o.status, ObligationStatus::Proved);
        assert_eq!(updated_o.proved_lemma_id, Some(l_id));
        assert_eq!(updated_o.attempt_count, 1);

        let saved_lemma = get_verified_lemma(&conn, l_id).unwrap().unwrap();
        assert_eq!(saved_lemma.theorem_name, "test_thm");
    }

    #[test]
    fn test_obligation_edge_self_loop_check_constraint() {
        let conn = setup_test_db();
        let p_id = Uuid::new_v4();
        let pv = create_test_problem_version(p_id, FidelityStatus::Approved);
        insert_problem_version(&conn, &pv).unwrap();

        let o1_id = Uuid::new_v4();
        let o1 = create_test_obligation(o1_id, p_id, "thm1");
        insert_obligation(&conn, &o1).unwrap();

        // Attempting to add an edge from an obligation to itself must violate CHECK(parent_obligation_id <> dependency_obligation_id)
        let edge = ObligationEdge {
            parent_obligation_id: o1_id,
            dependency_obligation_id: o1_id,
            edge_kind: EdgeKind::Lemma,
            case_group: None,
            created_at: Utc::now(),
        };

        let res = insert_edge(&conn, &edge);
        assert!(res.is_err());
    }
}
