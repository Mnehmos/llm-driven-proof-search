use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

pub mod episode;
pub mod reward;
pub mod action;
pub mod dataset;
pub mod string_i128;


#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ProblemState {
    Created,
    Formalizing,
    FidelityReview,
    Drafting,
    Sketching,
    Proving,
    RootProvedCoveragePending,
    Complete,
    StalledNeedsHuman,
    BudgetExhausted,
    Cancelled,
    IntegrityBlocked,
    RootProvedCoverageUnconverged,
}

impl std::fmt::Display for ProblemState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ProblemState::Created => "CREATED",
            ProblemState::Formalizing => "FORMALIZING",
            ProblemState::FidelityReview => "FIDELITY_REVIEW",
            ProblemState::Drafting => "DRAFTING",
            ProblemState::Sketching => "SKETCHING",
            ProblemState::Proving => "PROVING",
            ProblemState::RootProvedCoveragePending => "ROOT_PROVED_COVERAGE_PENDING",
            ProblemState::Complete => "COMPLETE",
            ProblemState::StalledNeedsHuman => "STALLED_NEEDS_HUMAN",
            ProblemState::BudgetExhausted => "BUDGET_EXHAUSTED",
            ProblemState::Cancelled => "CANCELLED",
            ProblemState::IntegrityBlocked => "INTEGRITY_BLOCKED",
            ProblemState::RootProvedCoverageUnconverged => "ROOT_PROVED_COVERAGE_UNCONVERGED",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for ProblemState {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "CREATED" => Ok(ProblemState::Created),
            "FORMALIZING" => Ok(ProblemState::Formalizing),
            "FIDELITY_REVIEW" => Ok(ProblemState::FidelityReview),
            "DRAFTING" => Ok(ProblemState::Drafting),
            "SKETCHING" => Ok(ProblemState::Sketching),
            "PROVING" => Ok(ProblemState::Proving),
            "ROOT_PROVED_COVERAGE_PENDING" => Ok(ProblemState::RootProvedCoveragePending),
            "COMPLETE" => Ok(ProblemState::Complete),
            "STALLED_NEEDS_HUMAN" => Ok(ProblemState::StalledNeedsHuman),
            "BUDGET_EXHAUSTED" => Ok(ProblemState::BudgetExhausted),
            "CANCELLED" => Ok(ProblemState::Cancelled),
            "INTEGRITY_BLOCKED" => Ok(ProblemState::IntegrityBlocked),
            "ROOT_PROVED_COVERAGE_UNCONVERGED" => Ok(ProblemState::RootProvedCoverageUnconverged),
            other => Err(format!("Unknown ProblemState: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FidelityStatus {
    Pending,
    Approved,
    Revoked,
}

impl std::fmt::Display for FidelityStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            FidelityStatus::Pending => "pending",
            FidelityStatus::Approved => "approved",
            FidelityStatus::Revoked => "revoked",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for FidelityStatus {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "pending" => Ok(FidelityStatus::Pending),
            "approved" => Ok(FidelityStatus::Approved),
            "revoked" => Ok(FidelityStatus::Revoked),
            other => Err(format!("Unknown FidelityStatus: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ObligationKind {
    Root,
    Proof,
    Coverage,
    Counterexample,
}

impl std::fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ObligationKind::Root => "root",
            ObligationKind::Proof => "proof",
            ObligationKind::Coverage => "coverage",
            ObligationKind::Counterexample => "counterexample",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for ObligationKind {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "root" => Ok(ObligationKind::Root),
            "proof" => Ok(ObligationKind::Proof),
            "coverage" => Ok(ObligationKind::Coverage),
            "counterexample" => Ok(ObligationKind::Counterexample),
            other => Err(format!("Unknown ObligationKind: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationStatus {
    Open,
    InProgress,
    Proved,
    Refuted,
    Superseded,
    Abandoned,
    BlockedNeedsHuman,
}

impl std::fmt::Display for ObligationStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ObligationStatus::Open => "open",
            ObligationStatus::InProgress => "in_progress",
            ObligationStatus::Proved => "proved",
            ObligationStatus::Refuted => "refuted",
            ObligationStatus::Superseded => "superseded",
            ObligationStatus::Abandoned => "abandoned",
            ObligationStatus::BlockedNeedsHuman => "blocked_needs_human",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for ObligationStatus {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "open" => Ok(ObligationStatus::Open),
            "in_progress" => Ok(ObligationStatus::InProgress),
            "proved" => Ok(ObligationStatus::Proved),
            "refuted" => Ok(ObligationStatus::Refuted),
            "superseded" => Ok(ObligationStatus::Superseded),
            "abandoned" => Ok(ObligationStatus::Abandoned),
            "blocked_needs_human" => Ok(ObligationStatus::BlockedNeedsHuman),
            other => Err(format!("Unknown ObligationStatus: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationCreator {
    InitialSketch,
    Decomposition,
    Reviewer,
    Human,
}

impl std::fmt::Display for ObligationCreator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ObligationCreator::InitialSketch => "initial_sketch",
            ObligationCreator::Decomposition => "decomposition",
            ObligationCreator::Reviewer => "reviewer",
            ObligationCreator::Human => "human",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for ObligationCreator {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "initial_sketch" => Ok(ObligationCreator::InitialSketch),
            "decomposition" => Ok(ObligationCreator::Decomposition),
            "reviewer" => Ok(ObligationCreator::Reviewer),
            "human" => Ok(ObligationCreator::Human),
            other => Err(format!("Unknown ObligationCreator: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    Lemma,
    CaseBranch,
    Witness,
    Reduction,
}

impl std::fmt::Display for EdgeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            EdgeKind::Lemma => "lemma",
            EdgeKind::CaseBranch => "case_branch",
            EdgeKind::Witness => "witness",
            EdgeKind::Reduction => "reduction",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for EdgeKind {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "lemma" => Ok(EdgeKind::Lemma),
            "case_branch" => Ok(EdgeKind::CaseBranch),
            "witness" => Ok(EdgeKind::Witness),
            "reduction" => Ok(EdgeKind::Reduction),
            other => Err(format!("Unknown EdgeKind: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AttemptOutcome {
    KernelPass,
    KernelFail,
    PreflightReject,
    ModelInvalidOutput,
    InfrastructureError,
    BudgetDenied,
    Timeout,
    Cancelled,
}

impl std::fmt::Display for AttemptOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            AttemptOutcome::KernelPass => "kernel_pass",
            AttemptOutcome::KernelFail => "kernel_fail",
            AttemptOutcome::PreflightReject => "preflight_reject",
            AttemptOutcome::ModelInvalidOutput => "model_invalid_output",
            AttemptOutcome::InfrastructureError => "infrastructure_error",
            AttemptOutcome::BudgetDenied => "budget_denied",
            AttemptOutcome::Timeout => "timeout",
            AttemptOutcome::Cancelled => "cancelled",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for AttemptOutcome {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "kernel_pass" => Ok(AttemptOutcome::KernelPass),
            "kernel_fail" => Ok(AttemptOutcome::KernelFail),
            "preflight_reject" => Ok(AttemptOutcome::PreflightReject),
            "model_invalid_output" => Ok(AttemptOutcome::ModelInvalidOutput),
            "infrastructure_error" => Ok(AttemptOutcome::InfrastructureError),
            "budget_denied" => Ok(AttemptOutcome::BudgetDenied),
            "timeout" => Ok(AttemptOutcome::Timeout),
            "cancelled" => Ok(AttemptOutcome::Cancelled),
            other => Err(format!("Unknown AttemptOutcome: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Polarity {
    Positive,
    Negative,
}

impl std::fmt::Display for Polarity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Polarity::Positive => "positive",
            Polarity::Negative => "negative",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for Polarity {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "positive" => Ok(Polarity::Positive),
            "negative" => Ok(Polarity::Negative),
            other => Err(format!("Unknown Polarity: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProblemVersion {
    pub id: Uuid,
    pub source_problem_text: String,
    pub source_problem_hash: String,
    pub source_metadata_json: String,
    pub root_formal_statement: String,
    pub root_statement_hash: String,
    pub normalized_root_rendering: String,
    pub environment_hash: String,
    pub fidelity_status: FidelityStatus,
    pub fidelity_method: String,
    pub fidelity_approval_id: Option<Uuid>,
    pub root_obligation_id: Option<Uuid>,
    pub state: ProblemState,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Obligation {
    pub id: Uuid,
    pub problem_version_id: Uuid,
    pub kind: ObligationKind,
    pub theorem_name: String,
    pub lean_statement: String,
    pub statement_hash: String,
    pub natural_description: String,
    pub status: ObligationStatus,
    pub depth_from_root: i64,
    pub created_by: ObligationCreator,
    pub created_by_epoch_id: Option<Uuid>,
    pub superseded_by_id: Option<Uuid>,
    pub proved_lemma_id: Option<Uuid>,
    pub refutation_lemma_id: Option<Uuid>,
    pub failure_lesson: Option<String>,
    pub attempt_count: i64,
    pub created_at: DateTime<Utc>,
    pub closed_at: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObligationEdge {
    pub parent_obligation_id: Uuid,
    pub dependency_obligation_id: Uuid,
    pub edge_kind: EdgeKind,
    pub case_group: Option<String>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttemptDiagnostic {
    pub id: Uuid,
    pub obligation_id: Uuid,
    pub role: String,
    pub model_config_hash: Option<String>,
    pub prompt_hash: String,
    pub context_manifest_hash: String,
    pub candidate_source_artifact_hash: Option<String>,
    pub diagnostic_json: Option<String>,
    pub outcome: AttemptOutcome,
    pub input_tokens: i64,
    pub output_tokens: i64,
    pub cost_usd_micros: i64,
    pub wall_time_ms: i64,
    pub lean_cpu_time_ms: i64,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiedLemma {
    pub id: Uuid,
    pub obligation_id: Uuid,
    pub polarity: Polarity,
    pub theorem_name: String,
    pub statement_hash: String,
    pub proof_source_artifact_hash: String,
    pub compiled_artifact_hash: String,
    pub proof_term_hash: String,
    pub environment_hash: String,
    pub actual_dependency_ids_json: String,
    pub kernel_result_hash: String,
    pub verified_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LeanVerificationOutcome {
    KernelPass,
    KernelFail,
    Timeout,
    InfrastructureError,
}

impl std::fmt::Display for LeanVerificationOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            LeanVerificationOutcome::KernelPass => "kernel_pass",
            LeanVerificationOutcome::KernelFail => "kernel_fail",
            LeanVerificationOutcome::Timeout => "timeout",
            LeanVerificationOutcome::InfrastructureError => "infrastructure_error",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for LeanVerificationOutcome {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "kernel_pass" => Ok(LeanVerificationOutcome::KernelPass),
            "kernel_fail" => Ok(LeanVerificationOutcome::KernelFail),
            "timeout" => Ok(LeanVerificationOutcome::Timeout),
            "infrastructure_error" => Ok(LeanVerificationOutcome::InfrastructureError),
            other => Err(format!("Unknown LeanVerificationOutcome: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LeanDiagnosticCategory {
    ParseError,
    ElaborationError,
    TypeMismatch,
    UnsolvedGoals,
    TacticFailure,
    Timeout,
    ProhibitedConstruct,
    DependencyMismatch,
    InternalError,
}

impl std::fmt::Display for LeanDiagnosticCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            LeanDiagnosticCategory::ParseError => "parse_error",
            LeanDiagnosticCategory::ElaborationError => "elaboration_error",
            LeanDiagnosticCategory::TypeMismatch => "type_mismatch",
            LeanDiagnosticCategory::UnsolvedGoals => "unsolved_goals",
            LeanDiagnosticCategory::TacticFailure => "tactic_failure",
            LeanDiagnosticCategory::Timeout => "timeout",
            LeanDiagnosticCategory::ProhibitedConstruct => "prohibited_construct",
            LeanDiagnosticCategory::DependencyMismatch => "dependency_mismatch",
            LeanDiagnosticCategory::InternalError => "internal_error",
        };
        write!(f, "{}", s)
    }
}

impl TryFrom<&str> for LeanDiagnosticCategory {
    type Error = String;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "parse_error" => Ok(LeanDiagnosticCategory::ParseError),
            "elaboration_error" => Ok(LeanDiagnosticCategory::ElaborationError),
            "type_mismatch" => Ok(LeanDiagnosticCategory::TypeMismatch),
            "unsolved_goals" => Ok(LeanDiagnosticCategory::UnsolvedGoals),
            "tactic_failure" => Ok(LeanDiagnosticCategory::TacticFailure),
            "timeout" => Ok(LeanDiagnosticCategory::Timeout),
            "prohibited_construct" => Ok(LeanDiagnosticCategory::ProhibitedConstruct),
            "dependency_mismatch" => Ok(LeanDiagnosticCategory::DependencyMismatch),
            "internal_error" => Ok(LeanDiagnosticCategory::InternalError),
            other => Err(format!("Unknown LeanDiagnosticCategory: {}", other)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LeanDiagnostic {
    pub category: LeanDiagnosticCategory,
    pub primary_message: String,
    pub source_span: Option<String>,
    pub goal: Option<String>,
    pub local_context: Vec<String>,
    pub unsolved_goals: Vec<String>,
    pub used_dependencies: Vec<String>,
    pub error_code: Option<String>,
    pub canonical_goal_hash: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyUseReport {
    pub declared_direct_dependency_ids: Vec<Uuid>,
    pub actual_generated_dependency_ids: Vec<Uuid>,
    pub missing_required_dependency_ids: Vec<Uuid>,
    pub undeclared_generated_dependency_ids: Vec<Uuid>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LeanVerificationResult {
    pub outcome: LeanVerificationOutcome,
    pub attempt_id: Uuid,
    pub obligation_id: Uuid,
    pub theorem_name: String,
    pub expected_statement_hash: String,
    pub elaborated_statement_hash: Option<String>,
    pub environment_hash: String,
    pub proof_source_hash: String,
    pub compiled_artifact_hash: Option<String>,
    pub proof_term_hash: Option<String>,
    pub diagnostic: Option<LeanDiagnostic>,
    pub dependency_use_report: Option<DependencyUseReport>,
    pub wall_time_ms: u64,
    pub lean_cpu_time_ms: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_problem_state_serialization() {
        let state = ProblemState::RootProvedCoverageUnconverged;
        let serialized = serde_json::to_string(&state).unwrap();
        assert_eq!(serialized, "\"ROOT_PROVED_COVERAGE_UNCONVERGED\"");
        
        let deserialized: ProblemState = serde_json::from_str(&serialized).unwrap();
        assert_eq!(deserialized, ProblemState::RootProvedCoverageUnconverged);
    }

    #[test]
    fn test_obligation_status_serialization() {
        let status = ObligationStatus::BlockedNeedsHuman;
        let serialized = serde_json::to_string(&status).unwrap();
        assert_eq!(serialized, "\"blocked_needs_human\"");

        let deserialized: ObligationStatus = serde_json::from_str(&serialized).unwrap();
        assert_eq!(deserialized, ObligationStatus::BlockedNeedsHuman);
    }

    #[test]
    fn test_try_from_str() {
        assert_eq!(ProblemState::try_from("CREATED").unwrap(), ProblemState::Created);
        assert_eq!(FidelityStatus::try_from("approved").unwrap(), FidelityStatus::Approved);
        assert_eq!(ObligationKind::try_from("root").unwrap(), ObligationKind::Root);
        assert_eq!(ObligationStatus::try_from("proved").unwrap(), ObligationStatus::Proved);
        assert_eq!(ObligationCreator::try_from("reviewer").unwrap(), ObligationCreator::Reviewer);
        assert_eq!(EdgeKind::try_from("lemma").unwrap(), EdgeKind::Lemma);
        assert_eq!(AttemptOutcome::try_from("kernel_pass").unwrap(), AttemptOutcome::KernelPass);
        assert_eq!(Polarity::try_from("positive").unwrap(), Polarity::Positive);
    }
}
