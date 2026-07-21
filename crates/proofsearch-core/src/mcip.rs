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

fn mcip_attribution_status(s: crate::literature_lineage::AttributionStatus) -> &'static str {
    use crate::literature_lineage::AttributionStatus::*;
    match s {
        DirectlyUsed => "directly_used",
        LikelyInfluential => "likely_influential",
        BackgroundOnly => "background_only",
        IndependentlyRediscovered => "independent_rediscovery",
        Uncertain => "uncertain",
        NotUsed => "not_used",
    }
}

fn mcip_visibility(v: crate::literature_lineage::Visibility) -> &'static str {
    use crate::literature_lineage::Visibility::*;
    match v {
        ModelVisible => "model_visible",
        PostHocReviewOnly => "post_hoc",
    }
}

/// #236 -> MCIP `literature_source`.
pub fn literature_source_to_mcip(
    s: &crate::literature_lineage::SourceRecord,
    env: &Envelope,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert("title".into(), json!(s.title));
    if !s.authors.is_empty() {
        f.insert("authors".into(), json!(s.authors));
    }
    if let Some(y) = s.year {
        f.insert("publication_year".into(), json!(y));
    }
    if let Some(v) = &s.venue {
        f.insert("venue".into(), json!(v));
    }
    if let Some(u) = &s.doi_or_url {
        f.insert("external_ids".into(), json!({ "url": u }));
    }
    if let Some(h) = &s.source_hash {
        f.insert("source_sha256".into(), json!(h));
    }
    finalize("literature_source", env, f)
}

/// #236/#264 -> MCIP `idea_attribution`. `literature_source_id` is the catalog
/// record id of the paired `literature_source` (what MathCorpus links on), and
/// `source_sha256_pin` is that literature_source record's own `record_hash`
/// (the value MathCorpus's catalog-pin check validates — NOT the paper's
/// content hash, which lives in `literature_source.source_sha256`).
pub fn idea_attribution_to_mcip(
    s: &crate::literature_lineage::SourceRecord,
    env: &Envelope,
    formal_statement_sha256: &str,
    literature_source_id: &str,
    source_record_hash: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert(
        "formal_statement_sha256".into(),
        json!(formal_statement_sha256),
    );
    f.insert("literature_source_id".into(), json!(literature_source_id));
    f.insert("source_sha256_pin".into(), json!(source_record_hash));
    f.insert(
        "attribution_status".into(),
        json!(mcip_attribution_status(s.attribution)),
    );
    f.insert("visibility".into(), json!(mcip_visibility(s.visibility)));
    finalize("idea_attribution", env, f)
}

/// #264: a stable, Windows-safe catalog record id for a literature source,
/// matching MathCorpus's `literature_sources/` naming (`literature_source.<id>`).
/// The id is used as the catalog filename, so any character outside
/// `[A-Za-z0-9._-]` is replaced with `_`.
pub fn literature_source_record_id(source_id: &str) -> String {
    let safe: String = source_id
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
                c
            } else {
                '_'
            }
        })
        .collect();
    format!("literature_source.{}", safe)
}

/// #263: emit the paired `literature_source` + `idea_attribution` records for
/// every source of a stored lineage. `base` supplies the shared envelope
/// context (packet_id, environment_hash, created_at, trust_status,
/// export_eligibility); a distinct `record_id` is minted per emitted record
/// from `record_id_prefix` so the two records for source `i` are individually
/// addressable and hash-stable. `idea_attribution` binds to the obligation's
/// `formal_statement_sha256`, the same statement hash the bundle's
/// `packet_identity` carries.
///
/// Provenance EVIDENCE only: neither emitted record has a proof-status field,
/// and surfacing them changes no trust decision — exactly the boundary the
/// `literature_lineage` type and its #236 storage already enforce.
pub fn lineage_records(
    sources: &[crate::literature_lineage::SourceRecord],
    base: &Envelope,
    record_id_prefix: &str,
    formal_statement_sha256: &str,
) -> Vec<Value> {
    let mut out = Vec::with_capacity(sources.len() * 2);
    for (i, s) in sources.iter().enumerate() {
        // The literature_source goes to the shared catalog under a stable,
        // Windows-safe id derived from its source_id; the idea_attribution links
        // to THAT id and pins the literature_source record's own record_hash.
        let ls_record_id = literature_source_record_id(&s.source_id);
        let src_env = Envelope {
            record_id: ls_record_id.clone(),
            ..base.clone()
        };
        let ls = literature_source_to_mcip(s, &src_env);
        let ls_record_hash = ls
            .get("record_hash")
            .and_then(|v| v.as_str())
            .unwrap_or_default()
            .to_string();
        out.push(ls);
        let idea_env = Envelope {
            record_id: format!("{}.idea_attribution.{}", record_id_prefix, i),
            ..base.clone()
        };
        out.push(idea_attribution_to_mcip(
            s,
            &idea_env,
            formal_statement_sha256,
            &ls_record_id,
            &ls_record_hash,
        ));
    }
    out
}

/// #237 -> MCIP `contribution_statement`.
pub fn contribution_statement_to_mcip(
    r: &crate::publication_review::PublicationReview,
    env: &Envelope,
    author: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert(
        "contribution_class".into(),
        serde_json::to_value(r.contribution_type).unwrap_or(Value::Null),
    );
    if !r.known_prior_art.is_empty() {
        f.insert("known_prior_art_refs".into(), json!(r.known_prior_art));
    }
    f.insert("author".into(), json!(author));
    f.insert("ai_assistance_disclosure".into(),
        json!("AI-assisted proof search; correctness is kernel-verified. See the publication_review gate."));
    finalize("contribution_statement", env, f)
}

/// #237 -> MCIP `citation_review` (from the publication review's citation-lineage layer).
pub fn citation_review_to_mcip(
    r: &crate::publication_review::PublicationReview,
    env: &Envelope,
    reviewer_confidence: f64,
) -> Value {
    use crate::publication_review::LayerStatus;
    let layer = &r.layers.citation_lineage;
    let review_status = match layer.status {
        LayerStatus::Complete => "endorsed",
        LayerStatus::BlockedMissingAttribution => "disputed",
        _ => "needs_more_evidence",
    };
    let mut f = BTreeMap::new();
    f.insert(
        "reviewer".into(),
        json!(if layer.reviewer.is_empty() {
            "unassigned"
        } else {
            &layer.reviewer
        }),
    );
    f.insert("reviewer_confidence".into(), json!(reviewer_confidence));
    f.insert("review_status".into(), json!(review_status));
    f.insert(
        "reviewed_at".into(),
        json!(if layer.decided_at.is_empty() {
            &env.created_at
        } else {
            &layer.decided_at
        }),
    );
    if let Some(n) = &layer.notes {
        f.insert("notes".into(), json!(n));
    }
    finalize("citation_review", env, f)
}

/// #264: the MCIP `attempt_id` for a proof-search attempt UUID. One stable,
/// colon-free namespace shared by `attempt_record` record ids, the
/// `attempt_id` a `negative_example` references, and a `repair_trajectory`
/// step's `from_attempt_id` / `to_ref` — so every reference resolves against
/// the packet's own `attempts` after fold.
pub fn attempt_ref(attempt_uuid: &str) -> String {
    format!("ar.{}", attempt_uuid)
}

/// #264: MathCorpus's canonical repair-step hash — SHA-256 over the canonical
/// JSON of exactly `{step_index, from_attempt_id, repair_action,
/// diagnostic_category_addressed, to_ref}` (sorted keys, compact), matching
/// `mathcorpus.hashing.repair_step_hash`. Computed over the FINAL (namespaced)
/// ref values so a folded step's `step_hash` reproduces MathCorpus's recompute.
fn repair_step_hash_canonical(
    step_index: usize,
    from_attempt_id: &str,
    repair_action: &str,
    diagnostic_category_addressed: Option<&str>,
    to_ref: &str,
) -> String {
    let mut m = BTreeMap::new();
    m.insert("step_index".to_string(), json!(step_index));
    m.insert("from_attempt_id".to_string(), json!(from_attempt_id));
    m.insert("repair_action".to_string(), json!(repair_action));
    m.insert(
        "diagnostic_category_addressed".to_string(),
        match diagnostic_category_addressed {
            Some(s) => json!(s),
            None => Value::Null,
        },
    );
    m.insert("to_ref".to_string(), json!(to_ref));
    sha256_hex(&canonical_json(&m))
}

/// #264: emit the `proof_variant` record the packet folds as its proof variant.
/// A `repair_trajectory`'s `verified_proof` `terminal_ref` resolves to this
/// variant's id, and the `proof_profile` (whose `proof_variant_id` equals this
/// record's id) folds in attached to it.
pub fn proof_variant_to_mcip(
    env: &Envelope,
    formal_statement_sha256: &str,
    variant_style: &str,
    source: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert(
        "formal_statement_sha256".into(),
        json!(formal_statement_sha256),
    );
    f.insert("variant_style".into(), json!(variant_style));
    f.insert("proof_body_redacted".into(), json!(false));
    f.insert("source".into(), json!(source));
    f.insert("proof_profile_id".into(), json!(env.record_id));
    finalize("proof_variant", env, f)
}

/// #235/#264 -> MCIP `repair_trajectory`. `variant_id` is the id of the
/// `proof_variant` emitted for this obligation: a `verified_proof` terminus
/// resolves to it (MathCorpus requires the terminal_ref of a verified
/// trajectory to be a proof-variant id, not an attempt). Step `from_attempt_id`
/// / `to_ref` are namespaced into the shared `attempt_ref` space, and each
/// `step_hash` is recomputed over those final values via MathCorpus's canonical
/// convention so the fold's integrity check passes.
pub fn repair_chain_to_mcip(
    c: &crate::repair_chain::RepairChain,
    env: &Envelope,
    variant_id: &str,
) -> Value {
    let steps: Vec<Value> = c
        .steps
        .iter()
        .map(|s| {
            let from = attempt_ref(&s.from_attempt_id);
            let to = attempt_ref(&s.to_ref);
            let step_hash = repair_step_hash_canonical(
                s.step_index,
                &from,
                &s.repair_action,
                s.diagnostic_category_addressed.as_deref(),
                &to,
            );
            json!({
                "step_index": s.step_index,
                "from_attempt_id": from,
                "repair_action": s.repair_action,
                "diagnostic_category_addressed": s.diagnostic_category_addressed,
                "to_ref": to,
                "step_hash": step_hash,
            })
        })
        .collect();
    // A verified terminus points at the proof variant; a failure terminus points
    // at the (namespaced) terminal attempt.
    let terminal_ref = if c.terminal_outcome == "verified_proof" {
        variant_id.to_string()
    } else {
        attempt_ref(&c.terminal_ref)
    };
    let mut f = BTreeMap::new();
    f.insert("steps".into(), json!(steps));
    f.insert("terminal_outcome".into(), json!(c.terminal_outcome));
    f.insert("terminal_ref".into(), json!(terminal_ref));
    finalize("repair_trajectory", env, f)
}

/// One recorded attempt -> MCIP `attempt_record`.
pub fn attempt_record_to_mcip(
    a: &crate::repair_chain::AttemptSummary,
    env: &Envelope,
    episode_id: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert(
        "outcome".into(),
        json!(if a.failed { "failed" } else { "succeeded" }),
    );
    f.insert("episode_id".into(), json!(episode_id));
    f.insert("diagnostic_category".into(), json!(a.diagnostic_category));
    finalize("attempt_record", env, f)
}

/// The `packet_identity` record that binds a bundle to a packet + environment.
pub fn packet_identity_to_mcip(
    env: &Envelope,
    packet_version: &str,
    formal_statement_sha256: Option<&str>,
    lean_version: &str,
    mathlib_rev: &str,
    status: &str,
) -> Value {
    let mut f = BTreeMap::new();
    f.insert("packet_version".into(), json!(packet_version));
    f.insert(
        "formal_statement_sha256".into(),
        json!(formal_statement_sha256),
    );
    f.insert(
        "toolchain".into(),
        json!({ "lean_version": lean_version, "mathlib_rev": mathlib_rev }),
    );
    f.insert("status".into(), json!(status));
    finalize("packet_identity", env, f)
}

/// Wrap MCIP records in the `bundle.schema.json` transport envelope (#230).
/// The first record should be a `packet_identity` binding the bundle.
pub fn build_bundle(bundle_id: &str, created_at: &str, records: Vec<Value>) -> Value {
    json!({
        "mcip_version": MCIP_VERSION,
        "bundle_id": bundle_id,
        "created_at": created_at,
        "producer": "llm-driven-proof-search",
        "records": records,
    })
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

        // #230: a full transport bundle bound by a packet_identity record.
        let pid = packet_identity_to_mcip(
            &env(),
            "1.0.0",
            Some(&"b".repeat(64)),
            "leanprover/lean4:v4.32.0",
            "abc123",
            "kernel_verified",
        );
        assert_eq!(pid["record_type"], "packet_identity");

        let chain = crate::repair_chain::assemble_repair_chain(&[
            crate::repair_chain::AttemptSummary {
                attempt_id: "a1".into(),
                failed: true,
                diagnostic_category: Some("tactic_timeout".into()),
                repair_note: None,
            },
            crate::repair_chain::AttemptSummary {
                attempt_id: "a2".into(),
                failed: false,
                diagnostic_category: None,
                repair_note: None,
            },
        ])
        .unwrap();
        let variant_env = Envelope {
            record_id: "pv.o1.canonical".into(),
            ..env()
        };
        let pv = proof_variant_to_mcip(&variant_env, &"a".repeat(64), "canonical", "proof_search");
        assert_eq!(pv["record_type"], "proof_variant");
        std::fs::write(
            out.join("proof_variant.json"),
            serde_json::to_vec_pretty(&pv).unwrap(),
        )
        .unwrap();

        let rt = repair_chain_to_mcip(&chain, &env(), "pv.o1.canonical");
        assert_eq!(rt["record_type"], "repair_trajectory");
        // #264: a verified terminus resolves to the proof variant, refs are namespaced.
        assert_eq!(rt["terminal_ref"], "pv.o1.canonical");
        assert_eq!(rt["steps"][0]["from_attempt_id"], "ar.a1");
        assert_eq!(rt["steps"][0]["to_ref"], "ar.a2");
        std::fs::write(
            out.join("repair_trajectory.json"),
            serde_json::to_vec_pretty(&rt).unwrap(),
        )
        .unwrap();

        // #236 literature records + #237 contribution/citation records.
        use crate::literature_lineage as lit;
        let src = lit::SourceRecord {
            source_id: "src-1".into(),
            title: "On the irrationality of sqrt 2".into(),
            authors: vec!["Euclid".into()],
            year: Some(-300),
            venue: Some("Elements".into()),
            doi_or_url: Some("https://example.org/elements".into()),
            source_hash: Some("a".repeat(64)),
            retrieved_passages_artifact_ref: Some("sha256:passage".into()),
            visibility: lit::Visibility::PostHocReviewOnly,
            retrieval_timing: lit::RetrievalTiming::AfterProofDiscovery,
            attribution: lit::AttributionStatus::IndependentlyRediscovered,
            extracted_claims: vec![],
            reviewer_notes: None,
            confidence: "medium".into(),
        };
        let ls = literature_source_to_mcip(&src, &env());
        assert_eq!(ls["record_type"], "literature_source");
        std::fs::write(
            out.join("literature_source.json"),
            serde_json::to_vec_pretty(&ls).unwrap(),
        )
        .unwrap();
        let ia = idea_attribution_to_mcip(
            &src,
            &env(),
            &"b".repeat(64),
            "literature_source.src-1",
            &ls["record_hash"].as_str().unwrap().to_string(),
        );
        assert_eq!(ia["attribution_status"], "independent_rediscovery");
        assert_eq!(ia["literature_source_id"], "literature_source.src-1");
        assert_eq!(ia["source_sha256_pin"], ls["record_hash"]);
        std::fs::write(
            out.join("idea_attribution.json"),
            serde_json::to_vec_pretty(&ia).unwrap(),
        )
        .unwrap();

        use crate::publication_review as pr;
        let mut review = pr::PublicationReview {
            review_version: pr::PUBLICATION_REVIEW_VERSION.into(),
            episode_id: "ep".into(),
            contribution_type: pr::ContributionType::Reconstruction,
            layers: pr::ReviewLayers::default(),
            makes_strong_novelty_claim: false,
            novelty_uncertain: false,
            contribution_statement: "Formal reconstruction; not novel.".into(),
            known_prior_art: vec!["Prior Fano-flow literature".into()],
        };
        review.layers.citation_lineage = pr::ReviewDecision {
            status: pr::LayerStatus::Complete,
            reviewer: "maintainer".into(),
            decided_at: "2026-07-12T00:00:00Z".into(),
            bound_hashes: vec![],
            notes: None,
        };
        let cs = contribution_statement_to_mcip(&review, &env(), "Mnehmos");
        assert_eq!(cs["contribution_class"], "reconstruction");
        std::fs::write(
            out.join("contribution_statement.json"),
            serde_json::to_vec_pretty(&cs).unwrap(),
        )
        .unwrap();
        let cr = citation_review_to_mcip(&review, &env(), 0.8);
        assert_eq!(cr["review_status"], "endorsed");
        std::fs::write(
            out.join("citation_review.json"),
            serde_json::to_vec_pretty(&cr).unwrap(),
        )
        .unwrap();

        let ar = attempt_record_to_mcip(
            &crate::repair_chain::AttemptSummary {
                attempt_id: "a1".into(),
                failed: true,
                diagnostic_category: Some("tactic_timeout".into()),
                repair_note: None,
            },
            &env(),
            "ep",
        );
        assert_eq!(ar["record_type"], "attempt_record");
        assert_eq!(ar["outcome"], "failed");
        std::fs::write(
            out.join("attempt_record.json"),
            serde_json::to_vec_pretty(&ar).unwrap(),
        )
        .unwrap();

        let bundle = build_bundle(
            "bundle-0001",
            "2026-07-12T00:00:00Z",
            vec![pid, pv, pp, rpm, dm, nm, tm, rt, ls, ia, cs, cr, ar],
        );
        assert_eq!(bundle["records"].as_array().unwrap().len(), 13);
        std::fs::write(
            out.join("bundle.json"),
            serde_json::to_vec_pretty(&bundle).unwrap(),
        )
        .unwrap();
    }

    /// #263: `lineage_records` emits a paired literature_source +
    /// idea_attribution per source, each individually addressable, hash-stable,
    /// and bound to the obligation's formal-statement hash — carrying no
    /// proof-status field.
    #[test]
    fn lineage_records_pairs_source_and_attribution_per_source() {
        use crate::literature_lineage as lit;
        let mk = |id: &str, attribution| lit::SourceRecord {
            source_id: id.into(),
            title: format!("Paper {}", id),
            authors: vec!["A. Author".into()],
            year: Some(2026),
            venue: None,
            doi_or_url: Some(format!("https://example.org/{}", id)),
            source_hash: Some("c".repeat(64)),
            retrieved_passages_artifact_ref: None,
            visibility: lit::Visibility::ModelVisible,
            retrieval_timing: lit::RetrievalTiming::BeforeProofDiscovery,
            attribution,
            extracted_claims: vec![],
            reviewer_notes: None,
            confidence: "high".into(),
        };
        let sources = vec![
            mk("s0", lit::AttributionStatus::DirectlyUsed),
            mk("s1", lit::AttributionStatus::LikelyInfluential),
        ];
        let stmt_sha = "d".repeat(64);
        let recs = lineage_records(&sources, &env(), "obl-1.lin-1", &stmt_sha);

        // Two sources -> four records, alternating source/attribution.
        assert_eq!(recs.len(), 4);
        assert_eq!(recs[0]["record_type"], "literature_source");
        assert_eq!(recs[1]["record_type"], "idea_attribution");
        assert_eq!(recs[2]["record_type"], "literature_source");
        assert_eq!(recs[3]["record_type"], "idea_attribution");

        // #264: the literature_source carries a stable, Windows-safe catalog id
        // (colon-free), and the idea_attribution links to THAT id and pins the
        // literature_source record's own record_hash (not the paper content hash).
        assert_eq!(recs[0]["record_id"], "literature_source.s0");
        assert_eq!(recs[1]["record_id"], "obl-1.lin-1.idea_attribution.0");
        assert!(!recs[0]["record_id"].as_str().unwrap().contains(':'));
        assert!(!recs[1]["record_id"].as_str().unwrap().contains(':'));
        assert_eq!(recs[1]["formal_statement_sha256"], stmt_sha);
        assert_eq!(recs[1]["literature_source_id"], "literature_source.s0");
        assert_eq!(recs[1]["source_sha256_pin"], recs[0]["record_hash"]);
        assert_eq!(recs[1]["attribution_status"], "directly_used");
        assert_eq!(recs[3]["literature_source_id"], "literature_source.s1");
        assert_eq!(recs[3]["source_sha256_pin"], recs[2]["record_hash"]);

        // Every record is hash-pinned, and NONE carries a proof-status field —
        // provenance evidence, never proof authority.
        for r in &recs {
            assert_eq!(r["record_hash"].as_str().unwrap().len(), 64);
            assert!(r.get("outcome").is_none());
            assert!(r.get("proof_authority").is_none());
            assert!(r.get("kernel_verified").is_none());
        }

        // Empty input yields no records (bundle unchanged when no lineage).
        assert!(lineage_records(&[], &env(), "p", &stmt_sha).is_empty());
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
