use rusqlite::Connection;
use uuid::Uuid;

pub struct BudgetGovernor {
    pub max_total_cost_usd_micros: i64,
}

#[derive(Debug, Clone)]
pub struct BudgetReservation {
    pub reservation_id: String,
    pub reserved_cost_usd_micros: i64,
}

impl BudgetGovernor {
    pub fn new(max_total_cost_usd_micros: i64) -> Self {
        Self { max_total_cost_usd_micros }
    }

    pub fn get_spent_cost(&self, conn: &Connection, problem_version_id: Uuid) -> Result<i64, String> {
        let mut stmt = conn.prepare(
            "SELECT SUM(
                CASE 
                    WHEN state = 'committed' THEN COALESCE(actual_cost_usd_micros, reserved_cost_usd_micros)
                    WHEN state = 'reserved' THEN reserved_cost_usd_micros
                    ELSE 0
                END
             ) FROM budget_ledger WHERE problem_version_id = ?1"
        ).map_err(|e| e.to_string())?;
        
        let sum: Option<i64> = stmt.query_row([problem_version_id.to_string()], |row| row.get(0))
            .map_err(|e| e.to_string())?;
            
        Ok(sum.unwrap_or(0))
    }

    pub fn reserve(
        &self,
        conn: &Connection,
        problem_version_id: Uuid,
        obligation_id: Option<Uuid>,
        call_kind: &str,
        reserved_input_tokens: i64,
        reserved_output_tokens: i64,
        reserved_cost_usd_micros: i64,
        reserved_wall_time_ms: i64,
    ) -> Result<Option<BudgetReservation>, String> {
        // Check if spent + reserved would exceed max
        let spent = self.get_spent_cost(conn, problem_version_id)?;
        if spent + reserved_cost_usd_micros > self.max_total_cost_usd_micros {
            return Ok(None); // Budget denied
        }

        let reservation_id = Uuid::new_v4().to_string();
        let id = Uuid::new_v4().to_string();
        let now = chrono::Utc::now().to_rfc3339();

        conn.execute(
            "INSERT INTO budget_ledger (
                id, problem_version_id, obligation_id, call_kind, reservation_id, state,
                reserved_input_tokens, reserved_output_tokens, actual_input_tokens, actual_output_tokens,
                reserved_cost_usd_micros, actual_cost_usd_micros, reserved_wall_time_ms, actual_wall_time_ms,
                created_at, updated_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, 'reserved', ?6, ?7, NULL, NULL, ?8, NULL, ?9, NULL, ?10, ?11)",
            rusqlite::params![
                id,
                problem_version_id.to_string(),
                obligation_id.map(|u| u.to_string()),
                call_kind,
                reservation_id,
                reserved_input_tokens,
                reserved_output_tokens,
                reserved_cost_usd_micros,
                reserved_wall_time_ms,
                now,
                now,
            ]
        ).map_err(|e| e.to_string())?;

        Ok(Some(BudgetReservation {
            reservation_id,
            reserved_cost_usd_micros,
        }))
    }

    pub fn commit(
        &self,
        conn: &Connection,
        reservation_id: &str,
        actual_input_tokens: i64,
        actual_output_tokens: i64,
        actual_cost_usd_micros: i64,
        actual_wall_time_ms: i64,
    ) -> Result<(), String> {
        let now = chrono::Utc::now().to_rfc3339();
        conn.execute(
            "UPDATE budget_ledger
             SET state = 'committed',
                 actual_input_tokens = ?1,
                 actual_output_tokens = ?2,
                 actual_cost_usd_micros = ?3,
                 actual_wall_time_ms = ?4,
                 updated_at = ?5
             WHERE reservation_id = ?6",
            rusqlite::params![
                actual_input_tokens,
                actual_output_tokens,
                actual_cost_usd_micros,
                actual_wall_time_ms,
                now,
                reservation_id,
            ]
        ).map_err(|e| e.to_string())?;
        Ok(())
    }

    pub fn release(&self, conn: &Connection, reservation_id: &str) -> Result<(), String> {
        let now = chrono::Utc::now().to_rfc3339();
        conn.execute(
            "UPDATE budget_ledger
             SET state = 'released',
                 updated_at = ?1
             WHERE reservation_id = ?2",
            rusqlite::params![now, reservation_id]
        ).map_err(|e| e.to_string())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::{initialize_db, insert_problem_version};
    use crate::models::{ProblemVersion, ProblemState, FidelityStatus};
    use chrono::Utc;

    #[test]
    fn test_budget_exhaustion_failing_test() {
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

        // Set budget limit to 100 micros
        let gov = BudgetGovernor::new(100);

        // Reserve 60 micros - should succeed
        let res1 = gov.reserve(&conn, problem_id, None, "prover_attempt", 100, 100, 60, 1000).unwrap();
        assert!(res1.is_some(), "First reservation should be accepted");

        // Reserve 50 micros - should exceed 100 (60 + 50 = 110) and be denied
        let res2 = gov.reserve(&conn, problem_id, None, "prover_attempt", 100, 100, 50, 1000).unwrap();
        assert!(res2.is_none(), "Second reservation should be denied because it exceeds the budget");
    }
}
