use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RewardComponentId {
    StepPenalty,
    KernelPass,
    KernelFail,
    InvalidResponse,
    TerminalSuccess,
    TerminalRefutation,
    TruncationPenalty,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewardComponent {
    pub id: RewardComponentId,
    pub value_scaled: i128,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewardPolicy {
    pub scale_factor: i128,
    pub step_penalty: i128,
    pub kernel_pass: i128,
    pub kernel_fail: i128,
    pub invalid_response: i128,
    pub terminal_success: i128,
    pub terminal_refutation: i128,
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
            terminal_success: 100_000,     // +10.0
            terminal_refutation: 100_000,  // +10.0
            truncation_penalty: -50_000,   // -5.0
        }
    }
}
