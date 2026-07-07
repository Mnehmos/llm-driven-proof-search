use serde::{Deserialize, Serialize};
use schemars::JsonSchema;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum RewardComponentId {
    StepPenalty,
    KernelPass,
    KernelFail,
    InvalidResponse,
    /// Root obligation passed the Lean kernel. Awarded on every kernel-verified
    /// termination, whether or not fidelity is verified — the prover proved
    /// exactly the formal statement it was given; that's real work regardless of
    /// whether the statement matches the source problem.
    RootKernelVerified,
    /// Composite success: kernel-verified AND statement fidelity verified. Never
    /// awarded on a kernel_verified-but-not-certified outcome.
    TerminalSuccess,
    TerminalRefutation,
    TruncationPenalty,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct RewardComponent {
    pub id: RewardComponentId,
    #[schemars(with = "String")]
    #[serde(with = "crate::models::string_i128")]
    pub value_scaled: i128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewardPolicy {
    #[serde(with = "crate::models::string_i128")]
    pub scale_factor: i128,
    #[serde(with = "crate::models::string_i128")]
    pub step_penalty: i128,
    #[serde(with = "crate::models::string_i128")]
    pub kernel_pass: i128,
    #[serde(with = "crate::models::string_i128")]
    pub kernel_fail: i128,
    #[serde(with = "crate::models::string_i128")]
    pub invalid_response: i128,
    #[serde(with = "crate::models::string_i128")]
    pub root_kernel_verified: i128,
    #[serde(with = "crate::models::string_i128")]
    pub terminal_success: i128,
    #[serde(with = "crate::models::string_i128")]
    pub terminal_refutation: i128,
    #[serde(with = "crate::models::string_i128")]
    pub truncation_penalty: i128,
}

impl RewardPolicy {
    pub fn default_policy() -> Self {
        // Fixed point representation. E.g. scale_factor = 10_000
        let scale = 10_000;
        Self {
            scale_factor: scale,
            step_penalty: -100,            // -0.01
            kernel_pass: 5_000,            // +0.5
            kernel_fail: -1_000,           // -0.1
            invalid_response: -2_000,      // -0.2
            root_kernel_verified: 20_000,  // +2.0 — real work, independent of fidelity
            terminal_success: 100_000,     // +10.0
            terminal_refutation: 100_000,  // +10.0
            truncation_penalty: -50_000,   // -5.0
        }
    }
}
