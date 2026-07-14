//! Issue #236: literature lineage as a first-class, hash-pinned artifact.
//!
//! A verified proof establishes correctness but says nothing about novelty or
//! attribution. This module models the intellectual provenance of an
//! AI-assisted proof: what was searched, what sources were retrieved, what
//! ideas/claims came from them, which proof steps map to which source claims,
//! and — crucially — whether a source was shown to the MODEL or only found in
//! POST-HOC review.
//!
//! Trust boundary: a `LiteratureLineage` is EVIDENCE, never authority. It has no
//! proof-status field by construction, so it can never mark anything proved.
//! Unknown/disputed provenance is a first-class value (`Uncertain`), never
//! guessed. Records are hash-pinned; the storage layer appends them (append-only
//! ledger), and this type carries a stable `lineage_hash` for replay/export.

use serde::{Deserialize, Serialize};

pub const LITERATURE_LINEAGE_VERSION: &str = "1.0";

/// How a source relates to the final proof. `Uncertain` and `NotUsed` are
/// explicit — provenance is never guessed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AttributionStatus {
    DirectlyUsed,
    LikelyInfluential,
    BackgroundOnly,
    IndependentlyRediscovered,
    Uncertain,
    NotUsed,
}

/// Whether the source was shown to the model during the run, or surfaced only in
/// post-hoc human review — the two must never be conflated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Visibility {
    ModelVisible,
    PostHocReviewOnly,
}

/// When the source was retrieved relative to proof discovery.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RetrievalTiming {
    BeforeProofDiscovery,
    AfterProofDiscovery,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ClaimKind {
    Theorem,
    Definition,
    Construction,
    ProofStrategy,
}

/// A claim extracted from a source, hash-pinned.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtractedClaim {
    pub claim_id: String,
    pub kind: ClaimKind,
    pub text: String,
    pub claim_hash: String,
}

/// A literature search event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SearchQuery {
    pub query: String,
    /// RFC3339 timestamp (supplied by the caller — deterministic input).
    pub searched_at: String,
}

/// One source and everything known about how it relates to the proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRecord {
    pub source_id: String,
    pub title: String,
    #[serde(default)]
    pub authors: Vec<String>,
    #[serde(default)]
    pub year: Option<i64>,
    #[serde(default)]
    pub venue: Option<String>,
    #[serde(default)]
    pub doi_or_url: Option<String>,
    /// Source content hash where available; None = unknown, never fabricated.
    #[serde(default)]
    pub source_hash: Option<String>,
    /// Governed artifact reference to retrieved passages/statements (never raw text inline).
    #[serde(default)]
    pub retrieved_passages_artifact_ref: Option<String>,
    pub visibility: Visibility,
    pub retrieval_timing: RetrievalTiming,
    pub attribution: AttributionStatus,
    #[serde(default)]
    pub extracted_claims: Vec<ExtractedClaim>,
    #[serde(default)]
    pub reviewer_notes: Option<String>,
    /// low | medium | high | unknown.
    pub confidence: String,
}

/// A link from a final proof step or dependency to a source claim it draws on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdeaToSourceLink {
    /// A proof step id / dependency name in the final artifact.
    pub proof_element: String,
    pub source_id: String,
    pub claim_id: String,
    pub attribution: AttributionStatus,
}

/// The full lineage record. EVIDENCE only — no proof-status field exists.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LiteratureLineage {
    pub lineage_version: String,
    pub episode_id: String,
    /// Pins the record to the exact environment it was gathered under.
    pub environment_hash: String,
    #[serde(default)]
    pub problem_version_id: Option<String>,
    #[serde(default)]
    pub obligation_id: Option<String>,
    pub search_queries: Vec<SearchQuery>,
    pub sources: Vec<SourceRecord>,
    pub idea_to_source_map: Vec<IdeaToSourceLink>,
    /// Canonical hash over everything above — replay/export compares this.
    pub lineage_hash: String,
}

impl LiteratureLineage {
    pub fn new(
        episode_id: &str,
        environment_hash: &str,
        problem_version_id: Option<String>,
        obligation_id: Option<String>,
        search_queries: Vec<SearchQuery>,
        sources: Vec<SourceRecord>,
        idea_to_source_map: Vec<IdeaToSourceLink>,
    ) -> Self {
        let mut record = LiteratureLineage {
            lineage_version: LITERATURE_LINEAGE_VERSION.to_string(),
            episode_id: episode_id.to_string(),
            environment_hash: environment_hash.to_string(),
            problem_version_id,
            obligation_id,
            search_queries,
            sources,
            idea_to_source_map,
            lineage_hash: String::new(),
        };
        record.lineage_hash = crate::hashing::canonical_hash(&record).unwrap_or_default();
        record
    }

    /// The machine-readable idea-to-source map final artifacts can emit.
    pub fn idea_to_source_map_json(&self) -> serde_json::Value {
        serde_json::to_value(&self.idea_to_source_map).unwrap_or(serde_json::Value::Null)
    }

    /// True iff every source is genuinely model-visible (nothing post-hoc).
    /// Lets an export distinguish what the model actually saw.
    pub fn all_model_visible(&self) -> bool {
        self.sources
            .iter()
            .all(|s| s.visibility == Visibility::ModelVisible)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claim(id: &str, kind: ClaimKind, text: &str) -> ExtractedClaim {
        ExtractedClaim {
            claim_id: id.to_string(),
            kind,
            text: text.to_string(),
            claim_hash: crate::hashing::canonical_hash(&text).unwrap_or_default(),
        }
    }

    fn source(
        id: &str,
        vis: Visibility,
        timing: RetrievalTiming,
        attr: AttributionStatus,
        claims: Vec<ExtractedClaim>,
    ) -> SourceRecord {
        SourceRecord {
            source_id: id.to_string(),
            title: format!("Source {id}"),
            authors: vec!["A. Author".to_string()],
            year: Some(2020),
            venue: Some("J. Math".to_string()),
            doi_or_url: Some(format!("https://doi.org/10.0/{id}")),
            source_hash: Some(crate::hashing::canonical_hash(&id).unwrap_or_default()),
            retrieved_passages_artifact_ref: Some(format!("sha256:artifact-{id}")),
            visibility: vis,
            retrieval_timing: timing,
            attribution: attr,
            extracted_claims: claims,
            reviewer_notes: None,
            confidence: "medium".to_string(),
        }
    }

    #[test]
    fn known_theorem_lookup_directly_used_and_model_visible() {
        let c = claim("c1", ClaimKind::Theorem, "sqrt 2 is irrational");
        let s = source(
            "s1",
            Visibility::ModelVisible,
            RetrievalTiming::BeforeProofDiscovery,
            AttributionStatus::DirectlyUsed,
            vec![c],
        );
        let l = LiteratureLineage::new(
            "ep",
            "env",
            None,
            None,
            vec![SearchQuery {
                query: "irrationality of sqrt 2".into(),
                searched_at: "2026-07-12T00:00:00Z".into(),
            }],
            vec![s],
            vec![],
        );
        assert!(l.all_model_visible());
        assert_eq!(l.sources[0].attribution, AttributionStatus::DirectlyUsed);
        assert!(!l.lineage_hash.is_empty());
    }

    #[test]
    fn reused_proof_strategy_links_a_step_to_a_source_claim() {
        let c = claim(
            "strat",
            ClaimKind::ProofStrategy,
            "descent via minimal counterexample",
        );
        let s = source(
            "s2",
            Visibility::ModelVisible,
            RetrievalTiming::BeforeProofDiscovery,
            AttributionStatus::LikelyInfluential,
            vec![c],
        );
        let link = IdeaToSourceLink {
            proof_element: "step:descent".into(),
            source_id: "s2".into(),
            claim_id: "strat".into(),
            attribution: AttributionStatus::LikelyInfluential,
        };
        let l = LiteratureLineage::new("ep", "env", None, None, vec![], vec![s], vec![link]);
        let map = l.idea_to_source_map_json();
        assert_eq!(map[0]["proof_element"], "step:descent");
        assert_eq!(map[0]["source_id"], "s2");
    }

    #[test]
    fn post_hoc_prior_art_is_distinguished_from_model_visible() {
        let s = source(
            "s3",
            Visibility::PostHocReviewOnly,
            RetrievalTiming::AfterProofDiscovery,
            AttributionStatus::IndependentlyRediscovered,
            vec![],
        );
        let l = LiteratureLineage::new("ep", "env", None, None, vec![], vec![s], vec![]);
        assert!(
            !l.all_model_visible(),
            "post-hoc source must not count as model-visible"
        );
        assert_eq!(
            l.sources[0].retrieval_timing,
            RetrievalTiming::AfterProofDiscovery
        );
        assert_eq!(
            l.sources[0].attribution,
            AttributionStatus::IndependentlyRediscovered
        );
    }

    #[test]
    fn uncertain_influence_is_explicit_not_guessed() {
        let s = source(
            "s4",
            Visibility::ModelVisible,
            RetrievalTiming::Unknown,
            AttributionStatus::Uncertain,
            vec![],
        );
        let l = LiteratureLineage::new("ep", "env", None, None, vec![], vec![s], vec![]);
        assert_eq!(l.sources[0].attribution, AttributionStatus::Uncertain);
        assert_eq!(l.sources[0].retrieval_timing, RetrievalTiming::Unknown);
    }

    #[test]
    fn record_has_no_proof_authority_and_hash_is_deterministic() {
        let build = || {
            let s = source(
                "s5",
                Visibility::ModelVisible,
                RetrievalTiming::BeforeProofDiscovery,
                AttributionStatus::BackgroundOnly,
                vec![],
            );
            LiteratureLineage::new("ep", "env", None, None, vec![], vec![s], vec![])
        };
        let a = build();
        let b = build();
        assert_eq!(a.lineage_hash, b.lineage_hash);
        // Structural guarantee: serialized record carries no proof/verified/status field.
        let json = serde_json::to_string(&a).unwrap();
        assert!(
            !json.contains("\"proved\"")
                && !json.contains("\"verified\"")
                && !json.contains("\"kernel")
        );
    }
}
