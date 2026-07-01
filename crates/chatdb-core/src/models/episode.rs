use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EpisodeState {
    AwaitingExternalAction,
    ExecutingAction,
    Terminated,
    Truncated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TerminationReason {
    ProofComplete,
    CounterexampleFound,
    ExplicitGiveUp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TruncationReason {
    WallClockTimeout,
    CpuTimeout,
    TokenBudgetExhausted,
    CostBudgetExhausted,
    TooManyInvalidResponses,
    InternalError,
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
