use rusqlite::{Connection, Result, Transaction, OptionalExtension};
use uuid::Uuid;
use chrono::Utc;
use crate::models::episode::EpisodeState;

/// Create a new episode for the given problem_version_id
pub fn episode_create(
    tx: &Transaction,
    problem_version_id: Uuid,
) -> Result<Uuid> {
    let episode_id = Uuid::new_v4();
    let now = Utc::now().to_rfc3339();

    tx.execute(
        "INSERT INTO episodes (
            id, problem_version_id, state, created_at, completed_at
        ) VALUES (
            ?1, ?2, ?3, ?4, NULL
        )",
        (
            episode_id.to_string(),
            problem_version_id.to_string(),
            "awaiting_external_action", // state
            now
        ),
    )?;

    // We should copy the root obligation from canonical problem_versions?
    // Actually, when an episode starts, it will have an empty episode_obligations set, 
    // and we will seed it with the root obligation from problem_versions during the first advance().
    
    Ok(episode_id)
}

/// Nondestructively reset an episode
pub fn episode_reset(tx: &Transaction, episode_id: Uuid) -> Result<Uuid> {
    let now = Utc::now().to_rfc3339();
    let new_episode_id = Uuid::new_v4();

    // 1. Copy config from old episode and create new episode
    tx.execute(
        "INSERT INTO episodes (
            id, problem_version_id, task_id, task_revision, environment_version, protocol_version,
            observation_schema_version, action_schema_version, reward_policy_version,
            verifier_version, lean_toolchain_version, seed, state, current_revision,
            step_count, max_steps, token_budget, cost_budget_micros, wall_clock_deadline,
            invalid_action_count, invalid_action_limit, parent_episode_id, created_at, updated_at
        )
        SELECT 
            ?1, problem_version_id, task_id, task_revision, environment_version, protocol_version,
            observation_schema_version, action_schema_version, reward_policy_version,
            verifier_version, lean_toolchain_version, seed, 'awaiting_external_action', 0,
            0, max_steps, token_budget, cost_budget_micros, wall_clock_deadline,
            0, invalid_action_limit, ?2, ?3, ?3
        FROM episodes WHERE id = ?2",
        (new_episode_id.to_string(), episode_id.to_string(), now),
    )?;

    // Trajectory append with EpisodeCreated event would go here (Phase 9)

    Ok(new_episode_id)
}

/// Advances the episode by creating or returning a pending ActionRequest
pub fn advance(tx: &Transaction, episode_id: Uuid) -> Result<Option<Uuid>> {
    let now = Utc::now().to_rfc3339();

    // 1. Check for existing pending request (Idempotency)
    let pending_req: Option<String> = tx.query_row(
        "SELECT id FROM action_requests 
         WHERE episode_id = ?1 AND status = 'pending' 
         ORDER BY created_at DESC LIMIT 1",
        [episode_id.to_string()],
        |row| row.get(0),
    ).optional()?;

    if let Some(req_id_str) = pending_req {
        return Ok(Some(Uuid::parse_str(&req_id_str).unwrap()));
    }

    // 2. We need to find the next target obligation.
    // First, check if there are any episode_obligations at all.
    let obligation_count: i64 = tx.query_row(
        "SELECT count(*) FROM episode_obligations WHERE episode_id = ?1",
        [episode_id.to_string()],
        |row| row.get(0),
    )?;

    if obligation_count == 0 {
        // Seed the root obligation from canonical problem_versions
        let root_info: Option<(String, String, String, String, String)> = tx.query_row(
            "SELECT pv.id, pv.root_formal_statement, pv.root_statement_hash, pv.normalized_root_rendering
             FROM episodes e
             JOIN problem_versions pv ON e.problem_version_id = pv.id
             WHERE e.id = ?1",
            [episode_id.to_string()],
            |row| Ok((
                row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, Uuid::new_v4().to_string()
            )),
        ).optional()?;

        if let Some((pv_id, statement, hash, natural_desc, root_obl_id)) = root_info {
            tx.execute(
                "INSERT INTO episode_obligations (
                    id, episode_id, problem_version_id, kind, theorem_name,
                    lean_statement, statement_hash, natural_description, status,
                    depth_from_root, created_by, created_at
                ) VALUES (?1, ?2, ?3, 'root', 'root_theorem', ?4, ?5, ?6, 'open', 0, 'initial_sketch', ?7)",
                (
                    root_obl_id,
                    episode_id.to_string(),
                    pv_id,
                    statement,
                    hash,
                    natural_desc,
                    now.clone(),
                ),
            )?;
        } else {
            // Can't advance if there is no root obligation to seed
            return Ok(None);
        }
    }

    // 3. Find the next open obligation to work on
    let next_obligation_id: Option<String> = tx.query_row(
        "SELECT id FROM episode_obligations 
         WHERE episode_id = ?1 AND status IN ('open', 'in_progress')
         ORDER BY created_at ASC LIMIT 1",
        [episode_id.to_string()],
        |row| row.get(0),
    ).optional()?;

    if let Some(_target_obl_id) = next_obligation_id {
        let req_id = Uuid::new_v4();
        
        let pv_id: String = tx.query_row(
            "SELECT problem_version_id FROM episodes WHERE id = ?1",
            [episode_id.to_string()],
            |row| row.get(0),
        )?;
        
        let seq: i64 = tx.query_row(
            "SELECT COALESCE(MAX(request_sequence_number), 0) + 1 FROM action_requests WHERE episode_id = ?1",
            [episode_id.to_string()],
            |row| row.get(0),
        )?;

        tx.execute(
            "INSERT INTO action_requests (
                id, episode_id, problem_version_id, episode_revision, request_sequence_number, role, 
                state_hash_before, status, expiration_at, created_at
            ) VALUES (?1, ?2, ?3, ?4, ?5, 'prover', 'dummy_hash', 'pending', ?6, ?7)",
            (
                req_id.to_string(),
                episode_id.to_string(),
                pv_id,
                1_i64, // revision
                seq,
                Utc::now().to_rfc3339(), // expires_at
                now, // created_at
            ),
        )?;
        Ok(Some(req_id))
    } else {
        // No open obligations remain. The episode might be ready to terminate.
        Ok(None)
    }
}
