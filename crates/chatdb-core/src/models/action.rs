use serde::{Deserialize, Serialize};
use schemars::JsonSchema;
use super::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use super::reward::RewardComponent;

use chrono::{DateTime, Utc};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum TypedAction {
    Decompose { sub_lemmas: Vec<String> },
    Solve { proof_term: String },
    ExternalResponseRejected { reason: String, raw_response: String },
    GiveUp,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ActionRequest {
    pub id: Uuid,
    pub episode_id: Uuid,
    pub revision: i64,
    pub role: ActionRole,
    pub state_hash: String,
    pub status: String,
    pub expires_at: DateTime<Utc>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ActionAttempt {
    pub id: Uuid,
    pub action_request_id: Uuid,
    pub model_config_hash: Option<String>,
    pub status: AttemptStatus,
    pub action_json: Option<TypedAction>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ActionRole {
    Prover,
    Reviewer,
    Human,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum AttemptStatus {
    Pending,
    Claimed,
    Executing,
    Verified,
    Completed,
    Failed,
    Expired,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum StepDisposition {
    Accepted,
    StaleRevision,
    InvalidResponse,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct StepResult {
    pub disposition: StepDisposition,
    pub counts_as_environment_step: bool,
    pub reward: Option<Vec<RewardComponent>>,
    pub outcome: Option<EpisodeOutcome>,
    pub termination_reason: Option<TerminationReason>,
    pub truncation_reason: Option<TruncationReason>,
    pub diagnostics: Option<String>,
}

impl StepResult {
    /// Validates the constraints of the StepResult.
    pub fn validate(&self) -> Result<(), &'static str> {
        match (self.outcome, self.termination_reason, self.truncation_reason) {
            (Some(_), Some(_), Some(_)) => return Err("Cannot have both termination and truncation reasons"),
            (Some(_), None, None) => return Err("Terminal outcome must have a termination or truncation reason"),
            (None, Some(_), _) => return Err("Cannot have termination reason without outcome"),
            (None, _, Some(_)) => return Err("Cannot have truncation reason without outcome"),
            _ => {}
        }
        Ok(())
    }
}
