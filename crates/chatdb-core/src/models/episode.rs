use serde::{Deserialize, Serialize};
use schemars::JsonSchema;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EpisodeState {
    AwaitingExternalAction,
    ExecutingAction,
    Terminated,
    Truncated,
}

/// Matches the `episodes.outcome` CHECK constraint in `db::schema_v1` exactly —
/// these strings are written straight into that column.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum EpisodeOutcome {
    Certified,
    Refuted,
    GaveUp,
    Timeout,
    BudgetExhausted,
    ModelError,
    InfrastructureError,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum TerminationReason {
    RootProved,
    RootRefuted,
    ModelGaveUp,
    HumanCancelled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum TruncationReason {
    BudgetExhausted,
    Timeout,
    InvalidActionsExceeded,
    ConsecutiveErrorsExceeded,
}

impl ToString for EpisodeState {
    fn to_string(&self) -> String {
        serde_json::to_string(self).unwrap().trim_matches('"').to_string()
    }
}

impl TryFrom<&str> for EpisodeState {
    type Error = serde_json::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        serde_json::from_str(&format!("\"{}\"", value))
    }
}

impl ToString for EpisodeOutcome {
    fn to_string(&self) -> String {
        serde_json::to_string(self).unwrap().trim_matches('"').to_string()
    }
}

impl TryFrom<&str> for EpisodeOutcome {
    type Error = serde_json::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        serde_json::from_str(&format!("\"{}\"", value))
    }
}

impl ToString for TerminationReason {
    fn to_string(&self) -> String {
        serde_json::to_string(self).unwrap().trim_matches('"').to_string()
    }
}

impl TryFrom<&str> for TerminationReason {
    type Error = serde_json::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        serde_json::from_str(&format!("\"{}\"", value))
    }
}

impl ToString for TruncationReason {
    fn to_string(&self) -> String {
        serde_json::to_string(self).unwrap().trim_matches('"').to_string()
    }
}

impl TryFrom<&str> for TruncationReason {
    type Error = serde_json::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        serde_json::from_str(&format!("\"{}\"", value))
    }
}
