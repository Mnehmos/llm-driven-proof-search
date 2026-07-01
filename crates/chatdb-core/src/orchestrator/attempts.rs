use chrono::Utc;
use rusqlite::{Connection, Result, Transaction, OptionalExtension};
use uuid::Uuid;

pub struct ClaimResult {
    pub attempt_id: Uuid,
    pub claim_token: String,
}

/// Claim a pending action request to start an attempt
pub fn attempt_claim(
    tx: &Transaction,
    episode_id: Uuid,
    action_request_id: Uuid,
    idempotency_key: &str,
    expected_revision: i64,
) -> Result<Option<ClaimResult>> {
    let now = Utc::now().to_rfc3339();
    
    // Check if the request is still pending
    let status: Option<String> = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1 AND episode_id = ?2",
        [action_request_id.to_string(), episode_id.to_string()],
        |row| row.get(0),
    ).optional()?;

    if status.as_deref() != Some("pending") {
        // Request not pending (already claimed, expired, etc.)
        return Ok(None);
    }

    let attempt_id = Uuid::new_v4();
    let claim_token = Uuid::new_v4().to_string();
    
    // We assume 5 minutes for claim expiration for now
    let expiration = Utc::now() + chrono::Duration::minutes(5);

    tx.execute(
        "INSERT INTO action_attempts (
            id, episode_id, action_request_id, idempotency_key,
            expected_revision, claim_token, status, claimed_at, claim_expiration
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, 'claimed', ?7, ?8)",
        (
            attempt_id.to_string(),
            episode_id.to_string(),
            action_request_id.to_string(),
            idempotency_key,
            expected_revision,
            &claim_token,
            now,
            expiration.to_rfc3339(),
        ),
    )?;

    // Update request status
    tx.execute(
        "UPDATE action_requests SET status = 'claimed' WHERE id = ?1",
        [action_request_id.to_string()],
    )?;

    Ok(Some(ClaimResult { attempt_id, claim_token }))
}

/// Find and recover expired action claims
pub fn attempt_recover_expired(tx: &Transaction) -> Result<usize> {
    let now = Utc::now().to_rfc3339();
    
    // Find all expired attempts
    let mut stmt = tx.prepare(
        "SELECT id, action_request_id FROM action_attempts 
         WHERE status IN ('claimed', 'executing', 'verified') 
         AND claim_expiration < ?1"
    )?;
    
    let expired_attempts: Vec<(String, String)> = stmt.query_map([now], |row| {
        Ok((row.get(0)?, row.get(1)?))
    })?.collect::<Result<Vec<_>, _>>()?;
    
    let count = expired_attempts.len();
    if count == 0 {
        return Ok(0);
    }
    
    // Revert them
    for (attempt_id, request_id) in expired_attempts {
        tx.execute(
            "UPDATE action_attempts SET status = 'expired' WHERE id = ?1",
            [attempt_id],
        )?;
        
        tx.execute(
            "UPDATE action_requests SET status = 'pending' WHERE id = ?1",
            [request_id],
        )?;
    }
    
    Ok(count)
}
