use rusqlite::{Result, Transaction, OptionalExtension};
use uuid::Uuid;
use chrono::Utc;

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

    // 3. Find the next ready obligation to work on: open/in_progress AND every direct
    // dependency (episode_obligation_edges) is already proved. This keeps advance()
    // from ever handing out a target whose dependencies aren't proved yet, which
    // would make CompactContextBuilder::build_episode fail with "Invariant violation".
    // Leaves (no children) are always ready. Deepest-first so decomposition children
    // are worked before the obligation that spawned them.
    let next_obligation_id: Option<String> = tx.query_row(
        "SELECT eo.id FROM episode_obligations eo
         WHERE eo.episode_id = ?1 AND eo.status IN ('open', 'in_progress')
         AND NOT EXISTS (
             SELECT 1 FROM episode_obligation_edges e
             JOIN episode_obligations dep ON dep.id = e.dependency_obligation_id
             WHERE e.parent_obligation_id = eo.id AND dep.status <> 'proved'
         )
         ORDER BY eo.depth_from_root DESC, eo.created_at ASC LIMIT 1",
        [episode_id.to_string()],
        |row| row.get(0),
    ).optional()?;

    if let Some(target_obl_id) = next_obligation_id {
        let req_id = Uuid::new_v4();

        // The revision a client must present as `expected_revision` when stepping
        // against the request we're about to insert is the episode's CURRENT
        // revision — not a hardcoded value. Getting this wrong either collides with
        // idx_active_request_per_revision (if it happens to match another live
        // request) or advertises a revision the episode has already moved past
        // (guaranteed stale_revision).
        let current_revision: i64 = tx.query_row(
            "SELECT current_revision FROM episodes WHERE id = ?1",
            [episode_id.to_string()],
            |row| row.get(0),
        )?;

        let (pv_id, env_hash, import_manifest_hash, root_stmt): (String, String, String, String) = tx.query_row(
            "SELECT pv.id, pv.environment_hash, pv.import_manifest_hash, pv.root_formal_statement
             FROM episodes e
             JOIN problem_versions pv ON e.problem_version_id = pv.id
             WHERE e.id = ?1",
            [episode_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
        )?;

        let seq: i64 = tx.query_row(
            "SELECT COALESCE(MAX(request_sequence_number), 0) + 1 FROM action_requests WHERE episode_id = ?1",
            [episode_id.to_string()],
            |row| row.get(0),
        )?;

        let builder = crate::orchestrator::context::CompactContextBuilder::new(4000);
        let target_uuid = Uuid::parse_str(&target_obl_id).unwrap();
        let context = builder.build_episode(tx, episode_id, target_uuid, &env_hash, &import_manifest_hash, &root_stmt)
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(std::io::Error::new(std::io::ErrorKind::Other, e))))?;

        let observation_json = serde_json::to_string(&context).unwrap();
        let observation_hash = crate::hashing::canonical_hash(&context)
            .map_err(|e| rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(std::io::Error::new(std::io::ErrorKind::Other, e))))?;

        tx.execute(
            "INSERT INTO action_requests (
                id, episode_id, problem_version_id, episode_revision, request_sequence_number, role,
                target_obligation_id, state_hash_before, status, expiration_at, created_at, observation_json, observation_hash
            ) VALUES (?1, ?2, ?3, ?4, ?5, 'prover', ?6, ?7, 'pending', ?8, ?9, ?10, ?11)",
            (
                req_id.to_string(),
                episode_id.to_string(),
                pv_id,
                current_revision,
                seq,
                target_obl_id,
                observation_hash.clone(), // state_hash_before: the hash of the observation the client is about to see
                (Utc::now() + chrono::Duration::minutes(15)).to_rfc3339(), // expires_at (15 mins)
                now, // created_at
                observation_json,
                observation_hash,
            ),
        )?;
        Ok(Some(req_id))
    } else {
        // No open obligations remain. The episode might be ready to terminate.
        Ok(None)
    }
}
