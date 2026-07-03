use chrono::Utc;
use rusqlite::{Result, Transaction, OptionalExtension};
use uuid::Uuid;

pub struct ClaimResult {
    pub attempt_id: Uuid,
    pub claim_token: String,
}

/// Claim a pending action request to start an attempt.
///
/// Idempotent on `(episode_id, idempotency_key)`: a retried claim with the same key
/// returns the existing attempt's claim instead of erroring on the UNIQUE index.
pub fn attempt_claim(
    tx: &Transaction,
    episode_id: Uuid,
    action_request_id: Uuid,
    idempotency_key: &str,
    expected_revision: i64,
) -> Result<Option<ClaimResult>> {
    let now = Utc::now().to_rfc3339();

    let existing: Option<(String, String, String)> = tx.query_row(
        "SELECT id, claim_token, status FROM action_attempts WHERE episode_id = ?1 AND idempotency_key = ?2",
        [episode_id.to_string(), idempotency_key.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).optional()?;

    if let Some((attempt_id_str, claim_token, status)) = existing {
        if status == "claimed" || status == "executing" {
            return Ok(Some(ClaimResult {
                attempt_id: Uuid::parse_str(&attempt_id_str).unwrap(),
                claim_token,
            }));
        }
        // Same idempotency key was already used to a terminal/non-reclaimable state
        // (committed, rejected, abandoned, expired, infrastructure_failed) — refuse
        // to silently mint a second attempt under the same key.
        return Ok(None);
    }

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

/// Requests carry their own `expiration_at` (set by `lifecycle::advance`) separate
/// from an attempt's `claim_expiration` — a request nobody ever claimed still
/// lapses on its own timer. Nothing previously checked this column, so a stale
/// unclaimed request displayed `status: pending` indefinitely. Mark lapsed ones
/// 'expired' so callers know to re-`advance()` for a fresh request.
pub fn request_recover_expired(tx: &Transaction, episode_id: Uuid) -> Result<usize> {
    let now = Utc::now().to_rfc3339();
    let n = tx.execute(
        "UPDATE action_requests SET status = 'expired'
         WHERE episode_id = ?1 AND status = 'pending' AND expiration_at IS NOT NULL AND expiration_at < ?2",
        (episode_id.to_string(), now),
    )?;
    Ok(n)
}

/// Abandon a wedged attempt (e.g. after a Lean gateway error) and free its request
/// back to 'pending' so a client can re-claim without waiting for the 5-minute
/// claim-expiration recovery. No-op if the attempt is already in a terminal state,
/// or if its request has since moved on (superseded by a newer claim).
pub fn attempt_abandon(tx: &Transaction, attempt_id: Uuid, new_status: &str) -> Result<()> {
    let info: Option<(String, String)> = tx.query_row(
        "SELECT status, action_request_id FROM action_attempts WHERE id = ?1",
        [attempt_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?)),
    ).optional()?;

    let Some((status, request_id)) = info else { return Ok(()); };
    if !matches!(status.as_str(), "claimed" | "executing" | "verified") {
        return Ok(());
    }

    tx.execute(
        "UPDATE action_attempts SET status = ?1 WHERE id = ?2",
        (new_status, attempt_id.to_string()),
    )?;

    tx.execute(
        "UPDATE action_requests SET status = 'pending' WHERE id = ?1 AND status = 'claimed'",
        [request_id],
    )?;

    Ok(())
}
