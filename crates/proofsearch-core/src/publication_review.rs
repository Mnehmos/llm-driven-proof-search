//! Issue #237: publication gate — citation + novelty review before an
//! open-problem claim is called publication-ready.
//!
//! Kernel verification proves a formal statement checks; it says nothing about
//! novelty, attribution, or honest description. This module models the review
//! workflow that gates PUBLIC claims, and — critically — keeps proof correctness
//! and publication readiness on SEPARATE axes: a kernel-verified proof stays
//! verified no matter what the citation/novelty review concludes. Novelty
//! uncertainty blocks a strong novelty *claim*, never the proof. The gate is
//! deterministic: given the layer states + contribution type, it computes one
//! publication status, and a kernel-verified result can NEVER become
//! `publication_ready` without a completed citation-lineage review.

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub const PUBLICATION_REVIEW_VERSION: &str = "1.0";

/// What kind of contribution the output claims to be — these are NOT
/// interchangeable and must be stated explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ContributionType {
    NewProof,
    IndependentRediscovery,
    Formalization,
    Verification,
    Reconstruction,
    Adaptation,
    LiteratureDerivedSynthesis,
}

/// Per-layer review state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum LayerStatus {
    NotStarted,
    InProgress,
    Complete,
    /// Blocked because attribution is missing (citation-lineage layer).
    BlockedMissingAttribution,
}

/// The overall publication status (the state machine the gate computes).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PublicationStatus {
    NotStarted,
    Incomplete,
    SourcesIdentified,
    LineageMapped,
    HumanReviewRequired,
    ReviewedWithCaveats,
    PublicationReady,
    BlockedMissingAttribution,
    BlockedNoveltyUncertain,
}

/// A signed/attributed, timestamped, hash-bound review decision for one layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReviewDecision {
    pub status: LayerStatus,
    /// Reviewer identity (free text — attribution, not authentication).
    pub reviewer: String,
    /// RFC3339 timestamp.
    pub decided_at: String,
    /// Proof/source hashes this decision is bound to.
    #[serde(default)]
    pub bound_hashes: Vec<String>,
    #[serde(default)]
    pub notes: Option<String>,
}

impl ReviewDecision {
    pub fn not_started() -> Self {
        ReviewDecision {
            status: LayerStatus::NotStarted,
            reviewer: String::new(),
            decided_at: String::new(),
            bound_hashes: Vec::new(),
            notes: None,
        }
    }
}

/// The six review layers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReviewLayers {
    /// Layer 1: the pinned kernel / certificate verification result.
    pub kernel_or_certificate: ReviewDecision,
    pub statement_fidelity: ReviewDecision,
    pub literature_completeness: ReviewDecision,
    pub citation_lineage: ReviewDecision,
    pub novelty_claim: ReviewDecision,
    pub exposition_disclosure: ReviewDecision,
}

impl Default for ReviewLayers {
    fn default() -> Self {
        ReviewLayers {
            kernel_or_certificate: ReviewDecision::not_started(),
            statement_fidelity: ReviewDecision::not_started(),
            literature_completeness: ReviewDecision::not_started(),
            citation_lineage: ReviewDecision::not_started(),
            novelty_claim: ReviewDecision::not_started(),
            exposition_disclosure: ReviewDecision::not_started(),
        }
    }
}

/// A full publication review. Carries the required contribution statement and
/// known-prior-art section for public export.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicationReview {
    pub review_version: String,
    pub episode_id: String,
    pub contribution_type: ContributionType,
    pub layers: ReviewLayers,
    /// True when the run makes a strong novelty claim (new_proof / stronger
    /// bound / novel method) that novelty-uncertainty must block.
    #[serde(default)]
    pub makes_strong_novelty_claim: bool,
    /// True when novelty could not be established — blocks the claim, not the proof.
    #[serde(default)]
    pub novelty_uncertain: bool,
    /// Required for public export.
    pub contribution_statement: String,
    #[serde(default)]
    pub known_prior_art: Vec<String>,
}

impl PublicationReview {
    /// Is the proof itself kernel-verified? INDEPENDENT of publication status —
    /// review outcomes never change this.
    pub fn kernel_verified(&self) -> bool {
        self.layers.kernel_or_certificate.status == LayerStatus::Complete
    }

    /// Deterministically compute the publication status from the review state.
    /// A kernel-verified result can never be `publication_ready` without a
    /// completed citation-lineage review.
    pub fn publication_status(&self) -> PublicationStatus {
        let l = &self.layers;

        // Nothing publishes until the proof actually verifies.
        if !self.kernel_verified() {
            return match l.kernel_or_certificate.status {
                LayerStatus::NotStarted => PublicationStatus::NotStarted,
                _ => PublicationStatus::Incomplete,
            };
        }

        // Hard blocks (the proof stays verified regardless).
        if l.citation_lineage.status == LayerStatus::BlockedMissingAttribution {
            return PublicationStatus::BlockedMissingAttribution;
        }
        if self.makes_strong_novelty_claim && self.novelty_uncertain {
            return PublicationStatus::BlockedNoveltyUncertain;
        }

        let done = |d: &ReviewDecision| d.status == LayerStatus::Complete;
        let all_review_layers_done = done(&l.statement_fidelity)
            && done(&l.literature_completeness)
            && done(&l.citation_lineage)
            && done(&l.novelty_claim)
            && done(&l.exposition_disclosure);

        // THE gate: publication_ready requires citation-lineage complete (and
        // every other layer). Enforced structurally here.
        if all_review_layers_done {
            return PublicationStatus::PublicationReady;
        }
        if done(&l.exposition_disclosure) && done(&l.citation_lineage) {
            // Everything material done but a caveat remains elsewhere.
            return PublicationStatus::ReviewedWithCaveats;
        }
        if done(&l.citation_lineage) {
            return PublicationStatus::HumanReviewRequired;
        }
        if l.citation_lineage.status == LayerStatus::InProgress {
            return PublicationStatus::LineageMapped;
        }
        if done(&l.literature_completeness)
            || l.literature_completeness.status == LayerStatus::InProgress
        {
            return PublicationStatus::SourcesIdentified;
        }
        PublicationStatus::Incomplete
    }

    /// The public export contribution block (contribution statement + prior art).
    /// Only meaningful once the gate allows publication or caveated release.
    pub fn public_contribution_block(&self) -> serde_json::Value {
        serde_json::json!({
            "contribution_type": self.contribution_type,
            "contribution_statement": self.contribution_statement,
            "known_prior_art": self.known_prior_art,
            "publication_status": self.publication_status(),
            "kernel_verified": self.kernel_verified(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete(reviewer: &str) -> ReviewDecision {
        ReviewDecision {
            status: LayerStatus::Complete,
            reviewer: reviewer.to_string(),
            decided_at: "2026-07-12T00:00:00Z".to_string(),
            bound_hashes: vec!["sha256:proof".to_string()],
            notes: None,
        }
    }

    fn base_review(contribution: ContributionType) -> PublicationReview {
        PublicationReview {
            review_version: PUBLICATION_REVIEW_VERSION.to_string(),
            episode_id: "ep".to_string(),
            contribution_type: contribution,
            layers: ReviewLayers::default(),
            makes_strong_novelty_claim: false,
            novelty_uncertain: false,
            contribution_statement: "A formal reconstruction.".to_string(),
            known_prior_art: vec![],
        }
    }

    #[test]
    fn kernel_verified_but_no_citation_review_is_not_publication_ready() {
        let mut r = base_review(ContributionType::NewProof);
        r.layers.kernel_or_certificate = complete("kernel");
        r.layers.statement_fidelity = complete("rev");
        // citation_lineage NOT done.
        assert!(r.kernel_verified());
        assert_ne!(r.publication_status(), PublicationStatus::PublicationReady);
    }

    #[test]
    fn all_layers_complete_is_publication_ready() {
        let mut r = base_review(ContributionType::Formalization);
        r.layers.kernel_or_certificate = complete("kernel");
        r.layers.statement_fidelity = complete("rev");
        r.layers.literature_completeness = complete("rev");
        r.layers.citation_lineage = complete("rev");
        r.layers.novelty_claim = complete("rev");
        r.layers.exposition_disclosure = complete("rev");
        assert_eq!(r.publication_status(), PublicationStatus::PublicationReady);
    }

    #[test]
    fn novelty_uncertainty_blocks_the_claim_not_the_proof() {
        let mut r = base_review(ContributionType::NewProof);
        r.layers.kernel_or_certificate = complete("kernel");
        r.makes_strong_novelty_claim = true;
        r.novelty_uncertain = true;
        assert_eq!(
            r.publication_status(),
            PublicationStatus::BlockedNoveltyUncertain
        );
        // The proof is STILL kernel-verified — correctness is a separate axis.
        assert!(r.kernel_verified());
    }

    #[test]
    fn missing_attribution_blocks_publication_not_kernel_truth() {
        let mut r = base_review(ContributionType::LiteratureDerivedSynthesis);
        r.layers.kernel_or_certificate = complete("kernel");
        r.layers.citation_lineage = ReviewDecision {
            status: LayerStatus::BlockedMissingAttribution,
            reviewer: "rev".into(),
            decided_at: "2026-07-12T00:00:00Z".into(),
            bound_hashes: vec![],
            notes: Some("source of the key lemma unattributed".into()),
        };
        assert_eq!(
            r.publication_status(),
            PublicationStatus::BlockedMissingAttribution
        );
        assert!(r.kernel_verified());
    }

    #[test]
    fn revoking_a_citation_review_updates_status_but_not_kernel_truth() {
        let mut r = base_review(ContributionType::Reconstruction);
        for layer in [
            &mut r.layers.kernel_or_certificate,
            &mut r.layers.statement_fidelity,
            &mut r.layers.literature_completeness,
            &mut r.layers.citation_lineage,
            &mut r.layers.novelty_claim,
            &mut r.layers.exposition_disclosure,
        ] {
            *layer = complete("rev");
        }
        assert_eq!(r.publication_status(), PublicationStatus::PublicationReady);
        // Revoke the citation-lineage review.
        r.layers.citation_lineage = ReviewDecision::not_started();
        assert_ne!(r.publication_status(), PublicationStatus::PublicationReady);
        assert!(
            r.kernel_verified(),
            "revocation must not alter kernel truth"
        );
    }

    #[test]
    fn cdc_reconstruction_with_acknowledged_prior_fano_flow_literature() {
        // The CDC fixture: a formal RECONSTRUCTION (not a new proof), with prior
        // Fano-flow literature acknowledged — no strong novelty claim, all layers
        // reviewed => publication-ready with an honest contribution statement.
        let mut r = base_review(ContributionType::Reconstruction);
        r.contribution_statement =
            "Formal Lean reconstruction of the CDC capstone; correctness is kernel-verified. Not a novel result."
                .to_string();
        r.known_prior_art =
            vec!["Prior Fano-flow / nowhere-zero-flow literature (acknowledged)".to_string()];
        for layer in [
            &mut r.layers.kernel_or_certificate,
            &mut r.layers.statement_fidelity,
            &mut r.layers.literature_completeness,
            &mut r.layers.citation_lineage,
            &mut r.layers.novelty_claim,
            &mut r.layers.exposition_disclosure,
        ] {
            *layer = complete("maintainer");
        }
        assert_eq!(r.contribution_type, ContributionType::Reconstruction);
        assert_eq!(r.publication_status(), PublicationStatus::PublicationReady);
        let block = r.public_contribution_block();
        assert_eq!(block["contribution_type"], "reconstruction");
        assert!(block["known_prior_art"]
            .as_array()
            .unwrap()
            .iter()
            .any(|p| p.as_str().unwrap().contains("Fano-flow")));
        assert_eq!(block["kernel_verified"], true);
    }
}
