//! Issue #235: group organic attempts into ordered repair chains.
//!
//! An obligation is often solved only after failed attempts. This reconstructs
//! the ordered chain from those real (organic) attempts to a terminus — a
//! verified proof or an explicit final failure — hash-linking each repair step.
//! It is derivative + deterministic: it reads recorded `action_attempts`, never
//! re-runs Lean, and links attempts to the final verified variant when one
//! exists. Maps to MCIP `repair_trajectory`.

use rusqlite::Connection;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

pub const REPAIR_CHAIN_VERSION: &str = "1.0";

/// One recorded attempt, reduced to what a repair chain needs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttemptSummary {
    pub attempt_id: String,
    /// True if this attempt did NOT verify (organic failure).
    pub failed: bool,
    /// Structured diagnostic category of the failure, if any.
    pub diagnostic_category: Option<String>,
    /// A short note on what the following attempt changed (from a reasoning log
    /// when available), else a neutral placeholder.
    pub repair_note: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RepairStep {
    pub step_index: usize,
    pub from_attempt_id: String,
    pub repair_action: String,
    pub diagnostic_category_addressed: Option<String>,
    pub to_ref: String,
    pub step_hash: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RepairChain {
    pub version: String,
    pub steps: Vec<RepairStep>,
    /// "verified_proof" | "explicit_failure".
    pub terminal_outcome: String,
    /// The terminal attempt/variant id.
    pub terminal_ref: String,
}

fn step_hash(from: &str, action: &str, to: &str) -> String {
    let mut h = Sha256::new();
    h.update(from.as_bytes());
    h.update(b"\0");
    h.update(action.as_bytes());
    h.update(b"\0");
    h.update(to.as_bytes());
    format!("{:x}", h.finalize())
}

/// Assemble a repair chain from ordered attempts. Returns `None` when no repair
/// happened (fewer than two attempts, or no failure preceded the terminus) —
/// a single first-try success is not a repair chain.
pub fn assemble_repair_chain(attempts: &[AttemptSummary]) -> Option<RepairChain> {
    if attempts.len() < 2 {
        return None;
    }
    if !attempts[..attempts.len() - 1].iter().any(|a| a.failed) {
        return None;
    }
    let mut steps = Vec::new();
    for (i, pair) in attempts.windows(2).enumerate() {
        let (from, to) = (&pair[0], &pair[1]);
        let action = from
            .repair_note
            .clone()
            .unwrap_or_else(|| "revised_submission".to_string());
        steps.push(RepairStep {
            step_index: i,
            from_attempt_id: from.attempt_id.clone(),
            repair_action: action.clone(),
            diagnostic_category_addressed: from.diagnostic_category.clone(),
            to_ref: to.attempt_id.clone(),
            step_hash: step_hash(&from.attempt_id, &action, &to.attempt_id),
        });
    }
    let last = attempts.last().unwrap();
    let terminal_outcome = if last.failed {
        "explicit_failure"
    } else {
        "verified_proof"
    };
    Some(RepairChain {
        version: REPAIR_CHAIN_VERSION.to_string(),
        steps,
        terminal_outcome: terminal_outcome.to_string(),
        terminal_ref: last.attempt_id.clone(),
    })
}

/// Gather the ordered attempts for an obligation and assemble its repair chain.
pub fn build_repair_chain(
    conn: &Connection,
    obligation_id: Uuid,
) -> Result<Option<RepairChain>, String> {
    Ok(assemble_repair_chain(&attempt_summaries(
        conn,
        obligation_id,
    )?))
}

/// The ordered per-attempt summaries for an obligation (committed/verified =
/// succeeded; anything else that ran = failed; claimed/executing skipped).
pub fn attempt_summaries(
    conn: &Connection,
    obligation_id: Uuid,
) -> Result<Vec<AttemptSummary>, String> {
    let mut stmt = conn
        .prepare(
            "SELECT aa.id, aa.status, aa.lean_result_json
             FROM action_attempts aa
             JOIN action_requests ar ON aa.action_request_id = ar.id
             WHERE ar.target_obligation_id = ?1
             ORDER BY aa.claimed_at ASC, aa.id ASC",
        )
        .map_err(|e| e.to_string())?;
    let rows = stmt
        .query_map([obligation_id.to_string()], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, Option<String>>(2)?,
            ))
        })
        .map_err(|e| e.to_string())?;

    let mut attempts = Vec::new();
    for r in rows {
        let (id, status, lean_json) = r.map_err(|e| e.to_string())?;
        // A committed/verified attempt succeeded; anything else that ran is a
        // failure. Claimed-but-never-executed attempts are skipped.
        let failed = match status.as_str() {
            "committed" | "verified" => false,
            "claimed" | "executing" => continue,
            _ => true,
        };
        let diagnostic_category = lean_json
            .as_deref()
            .and_then(|j| serde_json::from_str::<serde_json::Value>(j).ok())
            .and_then(|v| {
                v.get("diagnostic")
                    .and_then(|d| d.get("category"))
                    .and_then(|c| c.as_str())
                    .map(|s| s.to_string())
            });
        attempts.push(AttemptSummary {
            attempt_id: id,
            failed,
            diagnostic_category,
            repair_note: None,
        });
    }
    Ok(attempts)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(id: &str, failed: bool, diag: Option<&str>) -> AttemptSummary {
        AttemptSummary {
            attempt_id: id.into(),
            failed,
            diagnostic_category: diag.map(|s| s.into()),
            repair_note: None,
        }
    }

    #[test]
    fn single_first_try_success_is_not_a_repair_chain() {
        assert!(assemble_repair_chain(&[a("t1", false, None)]).is_none());
    }

    #[test]
    fn failure_then_success_links_to_the_verified_terminus() {
        let chain = assemble_repair_chain(&[
            a("t1", true, Some("tactic_timeout")),
            a("t2", true, Some("library_missing")),
            a("t3", false, None),
        ])
        .unwrap();
        assert_eq!(chain.steps.len(), 2);
        assert_eq!(chain.steps[0].from_attempt_id, "t1");
        assert_eq!(chain.steps[0].to_ref, "t2");
        assert_eq!(
            chain.steps[0].diagnostic_category_addressed.as_deref(),
            Some("tactic_timeout")
        );
        assert_eq!(chain.terminal_outcome, "verified_proof");
        assert_eq!(chain.terminal_ref, "t3");
        assert!(chain.steps.iter().all(|s| s.step_hash.len() == 64));
    }

    #[test]
    fn all_failures_terminate_in_explicit_failure() {
        let chain = assemble_repair_chain(&[a("t1", true, None), a("t2", true, None)]).unwrap();
        assert_eq!(chain.terminal_outcome, "explicit_failure");
        assert_eq!(chain.terminal_ref, "t2");
    }

    #[test]
    fn assembly_is_deterministic() {
        let attempts = [a("t1", true, Some("x")), a("t2", false, None)];
        assert_eq!(
            assemble_repair_chain(&attempts),
            assemble_repair_chain(&attempts)
        );
    }
}
