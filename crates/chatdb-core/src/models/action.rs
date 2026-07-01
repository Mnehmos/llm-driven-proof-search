use serde::{Deserialize, Serialize};
use super::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use super::reward::RewardComponent;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ActionRole {
    Prover,
    Reviewer,
    Human,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StepDisposition {
    Accepted,
    StaleRevision,
    InvalidResponse,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
