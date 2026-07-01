use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SanitizedModelDescriptor {
    pub provider: String,
    pub model_name: String,
    pub sanitization_policy_version: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatasetManifest {
    pub name: String,
    pub description: String,
    pub created_at: String,
    pub sanitization_policy_version: String,
    pub removed_field_categories: Vec<String>,
    pub source_trajectory_root_hashes: Vec<String>,
    pub output_checksums: std::collections::HashMap<String, String>,
}
