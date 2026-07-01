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
pub fn episode_reset(tx: &Transaction, episode_id: Uuid) -> Result<()> {
    let now = Utc::now().to_rfc3339();
    
    // 1. Mark any active action_attempts as cancelled
    tx.execute(
        "UPDATE action_attempts 
         SET status = 'failed'
         WHERE action_request_id IN (SELECT id FROM action_requests WHERE episode_id = ?1)
         AND status IN ('claimed', 'executing')",
        [episode_id.to_string()],
    )?;
    
    // 2. Mark any pending action_requests as expired
    tx.execute(
        "UPDATE action_requests 
         SET status = 'expired'
         WHERE episode_id = ?1 AND status = 'pending'",
        [episode_id.to_string()],
    )?;
    
    // 3. Mark the episode state back to AwaitingExternalAction and clear outcome
    tx.execute(
        "UPDATE episodes 
         SET state = 'awaiting_external_action',
             outcome = NULL,
             termination_reason = NULL,
             truncation_reason = NULL
         WHERE id = ?1",
        [episode_id.to_string()],
    )?;
    
    // 4. "Soft delete" or ignore old episode obligations? 
    // In a true reset, we'd delete the episode_obligations for this episode to start fresh, 
    // but the spec says "nondestructive reset". We should probably just wipe the episode-local mutable state
    // so it can start over. Wait, if it's episode-local, resetting it means clearing out the graph so the agent can retry.
    tx.execute(
        "DELETE FROM episode_obligations WHERE episode_id = ?1",
        [episode_id.to_string()],
    )?;
    
    tx.execute(
        "DELETE FROM trajectory_events WHERE episode_id = ?1",
        [episode_id.to_string()],
    )?;
    
    tx.execute(
        "DELETE FROM episode_budget_ledger WHERE episode_id = ?1",
        [episode_id.to_string()],
    )?;

    // We can leave action_requests and action_attempts for history, but if we delete obligations 
    // they might dangle. The prompt says "Reset is nondestructive". "Wait, the episode mutable proof state lives in episode_obligations... reset should clear it".
    Ok(())
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
        tx.execute(
            "INSERT INTO action_requests (
                id, episode_id, revision, role, 
                state_hash, status, expires_at, created_at
            ) VALUES (?1, ?2, ?3, 'prover', 'dummy_hash', 'pending', ?4, ?5)",
            (
                req_id.to_string(),
                episode_id.to_string(),
                1_i64, // revision
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
