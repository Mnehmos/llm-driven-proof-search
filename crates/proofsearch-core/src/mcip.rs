//! MCIP v1 conformance mapping (#230/#232/#233/#234/#235/#238).
//!
//! Maps this crate's derivative records onto the MathCorpus Interchange Protocol
//! v1 record schemas (`schema/mcip/v1/` in the corpus repo), so Proof Search can
//! emit MCIP-conformant evidence MathCorpus ingests without depending on either
//! repo's internal schema.
//!
//! Every MCIP record carries a common envelope (schema_version, record_type,
//! record_id, packet_id, environment_hash, created_at, trust_status,
//! export_eligibility, record_hash) where `record_hash` is the SHA-256 over the
//! record's canonical JSON (sorted keys, compact, UTF-8) with `record_hash`
//! itself removed — computed here by [`finalize`], matching
//! `tools/mathcorpus/mcip.record_hash`. Vocabulary differences (proof classes,
//! automation levels) are mapped explicitly. These records are child EVIDENCE,
//! never proof authority.

use crate::analyzer::ProofProfile;
use crate::dependency_manifest::DependencyManifest;
use crate::mutations::SyntheticNegative;
use crate::policy::RestrictionProfile;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// MCIP protocol version these mappings target.
pub const MCIP_VERSION: &str = "1.0.0";

/// Envelope inputs a caller supplies (identity + trust context) that this crate
/// cannot infer from a derivative record alone.
#[derive(Debug, Clone)]
pub struct Envelope {
    /// MathCorpus packet id, e.g. "algebra.add_comm.v1".
    pub packet_id: String,
    pub record_id: String,
    pub environment_hash: String,
    /// RFC3339 / ISO8601 with trailing Z.
    pub created_at: String,
    /// One of the MCIP trust_status enum values.
    pub trust_status: String,
    /// One of the MCIP export_eligibility enum values.
    pub export_eligibility: String,
}

fn canonical_json(map: &BTreeMap<String, Value>) -> String {
    // BTreeMap guarantees sorted keys; serde_json emits compact, UTF-8 (no ASCII
    // escaping) — matching the MCIP canonical rule.
    serde_json::to_string(map).unwrap_or_default()
}

fn sha256_hex(s: &str) -> String {
    let mut h = Sha256::new();
    h.update(s.as_bytes());
    format!("{:x}", h.finalize())
}

/// Attach the envelope, compute `record_hash` over the canonical record (minus
/// record_hash), and return the finished MCIP record.
fn finalize(record_type: &str, env: &Envelope, mut fields: BTreeMap<String, Value>) -> Value {
    fields.insert("schema_version".into(), json!(MCIP_VERSION));
    fields.insert("record_type".into(), json!(record_type));
    fields.insert("record_id".into(), json!(env.record_id));
    fields.insert("packet_id".into(), json!(env.packet_id));
    fields.insert("environment_hash".into(), json!(env.environment_hash));
    fields.insert("created_at".into(), json!(env.created_at));
    fields.insert("trust_status".into(), json!(env.trust_status));
    fields.insert("export_eligibility".into(), json!(env.export_eligibility));
    // record_hash over everything else, canonicalized.
    fields.remove("record_hash");
    let hash = sha256_hex(&canonical_json(&fields));
    fields.insert("record_hash".into(), json!(hash));
    Value::Object(fields.into_iter().collect())
}

/// Map an analyzer proof class to the MCIP `proof_class` vocabulary.
fn mcip_proof_class(analyzer_class: &str, is_module: bool) -> &'static str {
    if is_module {
        return "multi_lemma_composition";
    }
    match analyzer_class {
        "direct_application" => "theorem_lookup",
        "rewriting" => "normalization",
        "automation" | "calculation" => "arithmetic_automation",
        "induction" => "induction",
        "witness_construction" => "witness_construction",
        "case_analysis" | "contradiction" => "case_analysis",
        _ => "multi_lemma_composition",
    }
}

/// Map this crate's automation level to the MCIP `automation_level` vocabulary.
fn mcip_automation_level(level: &str) -> &'static str {
    match level {
        "none" => "none",
        "light" => "assisted",
        "moderate" => "semi_automated",
        "heavy" => "fully_automated",
        _ => "none",
    }
}

/// #232 -> MCIP `proof_profile`.
pub fn proof_profile_to_mcip(p: &ProofProfile, env: &Envelope, proof_variant_id: &str) -> Value {
    let is_module = p.observed.solve_kind == "verified_module";
    let primary = mcip_proof_class(&p.classification.primary_proof_class, is_module);
    let secondary: Vec<String> = p
        .classification
        .secondary_proof_class
        .as_deref()
        .map(|c| vec![mcip_proof_class(c, false).to_string()])
        .unwrap_or_default();

    let mut f = BTreeMap::new();
    f.insert("proof_variant_id".into(), json!(proof_variant_id));
    f.insert("primary_proof_class".into(), json!(primary));
    if !secondary.is_empty() {
        f.insert("secondary_proof_classes".into(), json!(secondary));
    }
    f.insert(
        "automation_level".into(),
        json!(mcip_automation_level(&p.classification.automation_level)),
    );
    f.insert("retrieval_depth".into(), json!(p.observed.retrieval_depth));
    f.insert("branch_count".into(), json!(p.observed.branch_case_count));
    f.insert(
        "dependency_composition_depth".into(),
        json!(p.observed.transitive_dependency_count),
    );
    f.insert(
        "uses_witness_invention".into(),
        json!(p.observed.constructs_witness),
    );
    f.insert("uses_induction".into(), json!(p.observed.uses_induction));
    f.insert(
        "uses_contradiction".into(),
        json!(p.observed.uses_contradiction),
    );
    f.insert(
        "uses_case_analysis".into(),
        json!(
            p.classification.primary_proof_class == "case_analysis"
                || p.classification.secondary_proof_class.as_deref() == Some("case_analysis")
        ),
    );
    finalize("proof_profile", env, f)
}

/// #233 -> MCIP `restriction_profile`. `null` allowlist means unrestricted.
pub fn restriction_profile_to_mcip(r: &RestrictionProfile, env: &Envelope, name: &str) -> Value {
    let mut f = BTreeMap::new();
    f.insert("name".into(), json!(name));
    f.insert(
        "forbidden_tactics".into(),
        json!(dedup_sorted(&r.forbidden_tactics)),
    );
    f.insert(
        "allowed_tactics".into(),
        if r.allowed_tactics.is_empty() {
            Value::Null
        } else {
            json!(dedup_sorted(&r.allowed_tactics))
        },
    );
    f.insert(
        "allowed_dependency_set".into(),
        if r.allowed_dependencies.is_empty() {
            Value::Null
        } else {
            json!(dedup_sorted(&r.allowed_dependencies))
        },
    );
    f.insert("max_tactic_count".into(), json!(r.max_tactic_steps));
    f.insert(
        "max_dependency_count".into(),
        json!(r.max_direct_dependencies),
    );
    f.insert(
        "requires_explicit_intermediate_claims".into(),
        json!(r.require_intermediate_claims),
    );
    finalize("restriction_profile", env, f)
}

/// #234 -> MCIP `dependency_manifest`. Instrumented categories map to arrays;
/// an uninstrumented category is OMITTED (schema fields are optional), never a
/// misleading empty array claiming a proven-empty set.
pub fn dependency_manifest_to_mcip(
    m: &DependencyManifest,
    env: &Envelope,
    proof_variant_id: Option<&str>,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert("proof_variant_id".into(), json!(proof_variant_id));
    if m.declared_dependencies.instrumented {
        f.insert(
            "declared_theorem_deps".into(),
            json!(dedup_sorted(&m.declared_dependencies.names)),
        );
    }
    if m.actual_used_verified_lemmas.instrumented {
        f.insert(
            "used_theorem_deps".into(),
            json!(dedup_sorted(&m.actual_used_verified_lemmas.names)),
        );
    }
    if m.approved_obligation_dependencies.instrumented {
        f.insert(
            "obligation_deps".into(),
            json!(dedup_sorted(&m.approved_obligation_dependencies.names)),
        );
    }
    if m.verified_module_item_edges.instrumented {
        f.insert(
            "verified_module_item_deps".into(),
            json!(dedup_sorted(&m.verified_module_item_edges.names)),
        );
    }
    if m.mathlib_declarations_referenced.instrumented {
        f.insert("tactic_tags".into(), json!(Vec::<String>::new()));
    }
    f.insert(
        "transitive_dependency_count".into(),
        json!(m.transitive_dependency_count),
    );
    f.insert(
        "transitive_dependency_depth".into(),
        json!(m.retrieval_depth),
    );
    if m.retrieved_candidates.instrumented {
        let names: Vec<String> = m
            .retrieved_candidates
            .candidates
            .iter()
            .map(|c| c.name.clone())
            .collect();
        f.insert("retrieval_candidates".into(), json!(dedup_sorted(&names)));
        let unused: Vec<String> = m
            .retrieved_but_unused
            .candidates
            .iter()
            .map(|c| c.name.clone())
            .collect();
        f.insert(
            "retrieved_unused_candidates".into(),
            json!(dedup_sorted(&unused)),
        );
    }
    finalize("dependency_manifest", env, f)
}

/// #235 -> MCIP `negative_example`. proof_authority is fixed to "none".
pub fn synthetic_negative_to_mcip(
    n: &SyntheticNegative,
    env: &Envelope,
    attempt_id: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert("attempt_id".into(), json!(attempt_id));
    f.insert("origin".into(), json!("controlled_mutation"));
    f.insert("diagnostic_category".into(), json!(n.expected_outcome));
    f.insert("candidate_source_ref".into(), Value::Null);
    f.insert("proof_authority".into(), json!("none"));
    f.insert("can_export_metadata".into(), json!(true));
    f.insert("can_export_proof_text".into(), json!(false));
    f.insert("can_export_diagnostics".into(), json!(true));
    f.insert("can_export_model_identity".into(), json!(false));
    finalize("negative_example", env, f)
}

/// Map an internal per-step outcome string to the MCIP `outcome` enum.
fn mcip_outcome(outcome: Option<&str>) -> &'static str {
    match outcome {
        Some("kernel_pass") | Some("kernel_verified") | Some("certified") => "kernel_verified",
        Some("kernel_fail") => "kernel_fail",
        Some("rejected") => "rejected",
        Some("timeout") => "timeout",
        Some("cancelled") => "cancelled",
        Some("error") | Some("infrastructure_error") | Some("model_error") => "error",
        _ => "unknown",
    }
}

/// #238 -> MCIP `rl_transition`. Every required-but-nullable field is emitted
/// explicitly; a null reward/terminal carries a `missing_field_reasons` entry
/// (never a silent zero), honoring #231.
pub fn rl_transition_to_mcip(
    t: &crate::orchestrator::dataset::RlTransition,
    env: &Envelope,
    formal_statement_sha256: &str,
) -> Value {
    let reward_available = t
        .info
        .get("reward_available")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);
    let terminal_available = t
        .info
        .get("terminal_fields_available")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);

    let mut missing = serde_json::Map::new();
    let reward: Value = if reward_available {
        json!(t.reward)
    } else {
        missing.insert(
            "reward".into(),
            json!("legacy episode predates reward persistence (llm-driven-proof-search#231)"),
        );
        Value::Null
    };
    let (terminated, truncated): (Value, Value) = if terminal_available {
        (json!(t.terminated), json!(t.truncated))
    } else {
        missing.insert(
            "terminated".into(),
            json!("legacy episode predates terminal-flag persistence (#231)"),
        );
        (Value::Null, Value::Null)
    };

    let state_ref = |s: &Value| json!({ "artifact_hash": Value::Null, "inline": s });

    let mut f = BTreeMap::new();
    f.insert(
        "formal_statement_sha256".into(),
        json!(formal_statement_sha256),
    );
    f.insert("episode_id".into(), json!(t.episode_id));
    f.insert(
        "problem_version_id".into(),
        json!(t
            .problem_version_id
            .clone()
            .unwrap_or_else(|| t.episode_id.clone())),
    );
    f.insert("step_index".into(), json!(t.step_index));
    f.insert("state".into(), state_ref(&t.state));
    f.insert("action".into(), t.action.clone());
    f.insert("reward".into(), reward);
    f.insert("next_state".into(), state_ref(&t.next_state));
    f.insert("terminated".into(), terminated);
    f.insert("truncated".into(), truncated);
    f.insert("termination_reason".into(), json!(t.termination_reason));
    f.insert("truncation_reason".into(), json!(t.truncation_reason));
    f.insert("outcome".into(), json!(mcip_outcome(t.outcome.as_deref())));
    f.insert("verifier_version".into(), Value::Null);
    f.insert("action_space_version".into(), Value::Null);
    f.insert("observation_space_version".into(), Value::Null);
    f.insert(
        "reward_policy_version".into(),
        t.info
            .get("reward_policy_version")
            .cloned()
            .unwrap_or(Value::Null),
    );
    f.insert("restriction_profile_id".into(), Value::Null);
    f.insert("restriction_profile_hash".into(), Value::Null);
    f.insert("model_config_hash".into(), Value::Null);
    f.insert("tokens".into(), Value::Null);
    f.insert("cost".into(), Value::Null);
    f.insert("wall_time_ms".into(), Value::Null);
    f.insert("lean_cpu_time_ms".into(), Value::Null);
    if !missing.is_empty() {
        f.insert("missing_field_reasons".into(), Value::Object(missing));
    }
    finalize("rl_transition", env, f)
}

fn dedup_sorted(v: &[String]) -> Vec<String> {
    let mut out: Vec<String> = v.to_vec();
    out.sort();
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer::{analyze_proof, DependencyInputs};
    use crate::dependency_manifest::{
        assemble_manifest, DependencySet, ManifestInputs, RetrievalRecord,
    };
    use crate::mutations::generate_mutations;

    fn env() -> Envelope {
        Envelope {
            packet_id: "algebra.add_comm.v1".into(),
            record_id: "rec-0001".into(),
            environment_hash: "lean4.32-mathlib-abc".into(),
            created_at: "2026-07-12T00:00:00Z".into(),
            trust_status: "kernel_verified".into(),
            export_eligibility: "restricted".into(),
        }
    }

    /// Emit one MCIP record of each mapped type to a directory the Python
    /// jsonschema validator (mcip_conformance.py) checks against the real
    /// schemas — the conformance evidence.
    #[test]
    fn emit_mcip_records_for_schema_validation() {
        let out =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/mcip_conformance");
        std::fs::create_dir_all(&out).unwrap();

        let profile = analyze_proof(
            "induction n with | zero => simp | succ k ih => nlinarith [ih]",
            "single_theorem",
            DependencyInputs {
                explicit: 1,
                transitive: 2,
                retrieval_depth: 1,
            },
        );
        let pp = proof_profile_to_mcip(&profile, &env(), "pv-1");
        assert_eq!(pp["record_type"], "proof_profile");
        assert!(pp["record_hash"].as_str().unwrap().len() == 64);
        std::fs::write(
            out.join("proof_profile.json"),
            serde_json::to_vec_pretty(&pp).unwrap(),
        )
        .unwrap();

        let rp = RestrictionProfile {
            forbidden_tactics: vec!["ring".into(), "nlinarith".into()],
            max_tactic_steps: Some(20),
            ..Default::default()
        };
        let rpm = restriction_profile_to_mcip(&rp, &env(), "no-ring-no-nlinarith");
        assert_eq!(rpm["record_type"], "restriction_profile");
        std::fs::write(
            out.join("restriction_profile.json"),
            serde_json::to_vec_pretty(&rpm).unwrap(),
        )
        .unwrap();

        let manifest = assemble_manifest(ManifestInputs {
            environment_hash: "env".into(),
            import_manifest: vec![],
            solve_kind: "single_theorem".into(),
            declared_dependencies: DependencySet::known(vec!["A".into()]),
            approved_obligation_dependencies: DependencySet::known(vec!["A".into()]),
            actual_used_verified_lemmas: DependencySet::known(vec!["A".into()]),
            mathlib_declarations_referenced: DependencySet::known(vec!["Nat.add_comm".into()]),
            verified_module_item_edges: DependencySet::unknown(),
            retrieved_candidates: RetrievalRecord::unknown(),
            direct_dependency_count: 1,
            transitive_dependency_count: 2,
            retrieval_depth: 1,
        });
        let dm = dependency_manifest_to_mcip(&manifest, &env(), Some("pv-1"));
        assert_eq!(dm["record_type"], "dependency_manifest");
        std::fs::write(
            out.join("dependency_manifest.json"),
            serde_json::to_vec_pretty(&dm).unwrap(),
        )
        .unwrap();

        let neg = &generate_mutations("exact Nat.add_comm a b")[0];
        let nm = synthetic_negative_to_mcip(neg, &env(), "attempt-1");
        assert_eq!(nm["record_type"], "negative_example");
        assert_eq!(nm["proof_authority"], "none");
        std::fs::write(
            out.join("negative_example.json"),
            serde_json::to_vec_pretty(&nm).unwrap(),
        )
        .unwrap();

        let transition = crate::orchestrator::dataset::RlTransition {
            schema_version: crate::orchestrator::dataset::RL_TRANSITION_SCHEMA_VERSION.into(),
            episode_id: "ep-1".into(),
            problem_version_id: Some("pv-1".into()),
            packet_id: None,
            step_index: 0,
            state: json!({ "state_hash": "s0", "observation": { "root_theorem_signature": "T" } }),
            action: json!({ "type": "solve", "proof_term": "x" }),
            reward: -0.01,
            next_state: json!({ "state_hash": "s1", "observation": { "unavailable": true } }),
            terminated: false,
            truncated: false,
            termination_reason: None,
            truncation_reason: None,
            outcome: Some("kernel_fail".into()),
            info: json!({ "reward_available": true, "terminal_fields_available": true, "reward_policy_version": "1.0" }),
            transition_hash: "abc".into(),
        };
        let tm = rl_transition_to_mcip(&transition, &env(), &"a".repeat(64));
        assert_eq!(tm["record_type"], "rl_transition");
        assert_eq!(tm["outcome"], "kernel_fail");
        std::fs::write(
            out.join("rl_transition.json"),
            serde_json::to_vec_pretty(&tm).unwrap(),
        )
        .unwrap();
    }

    #[test]
    fn record_hash_is_canonical_and_stable() {
        let rp = RestrictionProfile {
            forbidden_tactics: vec!["ring".into()],
            ..Default::default()
        };
        let a = restriction_profile_to_mcip(&rp, &env(), "n");
        let b = restriction_profile_to_mcip(&rp, &env(), "n");
        assert_eq!(a["record_hash"], b["record_hash"]);
        assert_eq!(a["record_hash"].as_str().unwrap().len(), 64);
    }
}
