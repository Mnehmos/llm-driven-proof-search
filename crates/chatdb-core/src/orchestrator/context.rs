use rusqlite::{Connection, OptionalExtension};
use crate::models::Obligation;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct CompactContext {
    pub env_id: String,
    pub root_theorem_signature: String,
    pub obligation_signature: String,
    pub direct_dependency_signatures: Vec<String>,
    pub latest_diagnostic: Option<String>,
    pub distilled_lesson: Option<String>,
    pub retrieved_hint: Option<String>,
}

pub struct CompactContextBuilder {
    pub max_context_tokens: usize,
}

impl CompactContextBuilder {
    pub fn new(max_context_tokens: usize) -> Self {
        Self { max_context_tokens }
    }

    pub fn build(
        &self,
        conn: &Connection,
        obligation: &Obligation,
        environment_hash: &str,
        root_formal_statement: &str,
    ) -> Result<CompactContext, String> {
        let env_id = environment_hash.to_string();
        let root_theorem_signature = root_formal_statement.to_string();
        let obligation_signature = format!(
            "theorem {} : {}",
            obligation.theorem_name, obligation.lean_statement
        );

        // Fetch direct dependencies
        let mut stmt = conn.prepare(
            "SELECT dependency_obligation_id FROM obligation_edges WHERE parent_obligation_id = ?1"
        ).map_err(|e| e.to_string())?;
        
        let dep_ids = stmt.query_map([obligation.id.to_string()], |row| {
            let id_str: String = row.get(0)?;
            Ok(id_str)
        }).map_err(|e| e.to_string())?;

        let mut direct_dependency_signatures = Vec::new();
        for id_res in dep_ids {
            let id_str = id_res.map_err(|e| e.to_string())?;
            let mut o_stmt = conn.prepare(
                "SELECT theorem_name, lean_statement, status FROM obligations WHERE id = ?1"
            ).map_err(|e| e.to_string())?;
            
            let dep_info = o_stmt.query_row([id_str.clone()], |row| {
                let name: String = row.get(0)?;
                let stmt: String = row.get(1)?;
                let status: String = row.get(2)?;
                Ok((name, stmt, status))
            }).map_err(|e| e.to_string())?;

            if dep_info.2 != "proved" {
                return Err(format!(
                    "Invariant violation: direct dependency {} is not proved (status={})",
                    id_str, dep_info.2
                ));
            }

            direct_dependency_signatures.push(format!("theorem {} : {}", dep_info.0, dep_info.1));
        }

        // Fetch latest diagnostic
        let mut attempt_stmt = conn.prepare(
            "SELECT diagnostic_json FROM proposal_attempts
             WHERE obligation_id = ?1 AND outcome IN ('kernel_fail', 'timeout')
             ORDER BY created_at DESC LIMIT 1"
        ).map_err(|e| e.to_string())?;
        
        let latest_diagnostic: Option<String> = attempt_stmt.query_row([obligation.id.to_string()], |row| {
            row.get(0)
        }).optional().map_err(|e| e.to_string())?.flatten();

        let distilled_lesson = obligation.failure_lesson.clone();
        let retrieved_hint = None;

        // Check token budget
        let total_chars = env_id.len()
            + root_theorem_signature.len()
            + obligation_signature.len()
            + direct_dependency_signatures.iter().map(|s| s.len()).sum::<usize>()
            + latest_diagnostic.as_ref().map(|s| s.len()).unwrap_or(0)
            + distilled_lesson.as_ref().map(|s| s.len()).unwrap_or(0);

        let approx_tokens = total_chars / 4;
        if approx_tokens > self.max_context_tokens {
            return Err("CONTEXT_TOO_LARGE".to_string());
        }

        Ok(CompactContext {
            env_id,
            root_theorem_signature,
            obligation_signature,
            direct_dependency_signatures,
            latest_diagnostic,
            distilled_lesson,
            retrieved_hint,
        })
    }
}

#[cfg(all(test, feature = "legacy_tests"))]
mod tests {
    use super::*;
    use crate::db::{initialize_db, insert_problem_version, insert_obligation};
    use crate::models::{ProblemVersion, ProblemState, FidelityStatus, ObligationKind, ObligationCreator, ObligationStatus};
    use chrono::Utc;

    #[test]
    fn test_context_builder_success() {
        let conn = Connection::open_in_memory().unwrap();
        initialize_db(&conn).unwrap();

        let problem_id = Uuid::new_v4();
        let pv = ProblemVersion {
            id: problem_id,
            source_problem_text: "Prove x + 0 = x".to_string(),
            source_problem_hash: "hash1".to_string(),
            source_metadata_json: "{}".to_string(),
            root_formal_statement: "theorem root (x : Int) : x + 0 = x".to_string(),
            root_statement_hash: "hash2".to_string(),
            normalized_root_rendering: "x + 0 = x".to_string(),
            environment_hash: "envhash".to_string(),
            fidelity_status: FidelityStatus::Approved,
            fidelity_method: "human_authored".to_string(),
            fidelity_approval_id: None,
            root_obligation_id: None,
            state: ProblemState::Proving,
            created_at: Utc::now(),
        };
        insert_problem_version(&conn, &pv).unwrap();

        let root_id = Uuid::new_v4();
        let o_root = Obligation {
            id: root_id,
            problem_version_id: problem_id,
            kind: ObligationKind::Root,
            theorem_name: "O_root".to_string(),
            lean_statement: "x + 0 = x".to_string(),
            statement_hash: "hash2".to_string(),
            natural_description: "root".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now(),
            closed_at: None,
        };
        insert_obligation(&conn, &o_root).unwrap();

        let builder = CompactContextBuilder::new(1000);
        let ctx = builder.build(&conn, &o_root, "envhash", "theorem root (x : Int) : x + 0 = x").unwrap();
        assert_eq!(ctx.env_id, "envhash");
        assert_eq!(ctx.root_theorem_signature, "theorem root (x : Int) : x + 0 = x");
        assert_eq!(ctx.obligation_signature, "theorem O_root : x + 0 = x");
        assert!(ctx.direct_dependency_signatures.is_empty());
    }
}
