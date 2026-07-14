//! Issue #233: immutable, versioned tactic/dependency restriction profiles.
//!
//! A benchmark or curriculum can demand a proof avoid `ring`/`nlinarith`, stay
//! under a step budget, use only certain lemmas, etc. Prompt-only requests are
//! not reliable training labels, so this is a DETERMINISTIC contract: a
//! `RestrictionProfile` (hash-pinned, version-stamped) is checked against a
//! submitted proof — reusing the #232 analyzer's observed facts — and produces
//! structured `PolicyViolation`s. A non-empty result is a POLICY rejection,
//! deliberately distinct from a Lean kernel failure: the proof may be perfectly
//! valid and still violate the contract. The same check applies to
//! single-theorem and module submissions.

use crate::analyzer::{self, DependencyInputs};
use serde::{Deserialize, Serialize};

/// Bump on any change to the profile field set or check semantics.
pub const RESTRICTION_PROFILE_VERSION: &str = "1.0";

/// Tactics that are close variants of one another — forbidding the base name
/// also forbids the variants, so a restriction can't be trivially evaded by an
/// alias/macro (`ring` -> `ring_nf`, `simp` -> `simp_all`/`simpa`/`dsimp`, ...).
fn alias_expand(tactic: &str) -> &'static [&'static str] {
    match tactic {
        "ring" | "ring_nf" => &["ring", "ring_nf"],
        "simp" | "simp_all" | "simpa" | "dsimp" => &["simp", "simp_all", "simpa", "dsimp"],
        "decide" | "native_decide" => &["decide", "native_decide"],
        "norm_num" | "norm_cast" | "push_cast" => &["norm_num", "norm_cast", "push_cast"],
        "omega" => &["omega"],
        "nlinarith" => &["nlinarith"],
        "linarith" => &["linarith"],
        _ => &[],
    }
}

fn automation_rank(level: &str) -> u8 {
    match level {
        "none" => 0,
        "light" => 1,
        "moderate" => 2,
        "heavy" => 3,
        _ => 0,
    }
}

/// An immutable, versioned restriction contract. Empty/None fields impose no
/// restriction, so the zero value is a legacy "unrestricted" profile.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct RestrictionProfile {
    #[serde(default)]
    pub forbidden_tactics: Vec<String>,
    /// Allowlist; when non-empty, any tactic outside it is a violation.
    #[serde(default)]
    pub allowed_tactics: Vec<String>,
    /// Allowlist of dependency/theorem names; empty = unrestricted.
    #[serde(default)]
    pub allowed_dependencies: Vec<String>,
    #[serde(default)]
    pub forbidden_dependencies: Vec<String>,
    #[serde(default)]
    pub max_tactic_steps: Option<usize>,
    #[serde(default)]
    pub max_direct_dependencies: Option<usize>,
    /// none | light | moderate | heavy — observed automation must not exceed it.
    #[serde(default)]
    pub automation_ceiling: Option<String>,
    /// e.g. "flat_tactic_sequence" | "raw_lean_block".
    #[serde(default)]
    pub required_proof_format: Option<String>,
    /// If true, the proof must contain explicit intermediate claims (`have`/`suffices`/`calc`).
    #[serde(default)]
    pub require_intermediate_claims: bool,
    /// Allowlist of import-manifest entries; empty = unrestricted.
    #[serde(default)]
    pub allowed_imports: Vec<String>,
}

impl RestrictionProfile {
    /// True when no restriction is imposed (legacy/unrestricted episode).
    pub fn is_unrestricted(&self) -> bool {
        self == &RestrictionProfile::default()
    }

    /// Canonical, stable hash for episode pinning + replay. Version-stamped so a
    /// change in semantics changes the pin.
    pub fn profile_hash(&self) -> String {
        let stamped = serde_json::json!({
            "restriction_profile_version": RESTRICTION_PROFILE_VERSION,
            "profile": self,
        });
        crate::hashing::canonical_hash(&stamped).unwrap_or_default()
    }
}

/// A single, structured restriction violation. A POLICY rejection, never a
/// kernel verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "rule", rename_all = "snake_case")]
pub enum PolicyViolation {
    ForbiddenTactic { tactic: String, matched: String },
    TacticNotAllowed { tactic: String },
    ForbiddenDependency { dependency: String },
    DependencyNotAllowed { dependency: String },
    TooManyTacticSteps { used: usize, max: usize },
    TooManyDirectDependencies { used: usize, max: usize },
    AutomationCeilingExceeded { observed: String, ceiling: String },
    WrongProofFormat { required: String, actual: String },
    MissingIntermediateClaims,
    ImportNotAllowed { import: String },
}

/// Everything the deterministic check needs about a submission.
pub struct SubmissionFacts<'a> {
    pub proof_source: &'a str,
    pub solve_kind: &'a str,
    /// Dependency/theorem names the submission relies on (from the graph).
    pub dependency_names: &'a [String],
    pub explicit_dependency_count: usize,
    pub import_manifest: &'a [String],
    pub actual_proof_format: Option<&'a str>,
}

/// Deterministically check a submission against a restriction profile. An empty
/// result is a pass; a non-empty result is a structured POLICY rejection.
/// Identical for single-theorem and module submissions.
pub fn check_restrictions(
    profile: &RestrictionProfile,
    facts: &SubmissionFacts,
) -> Vec<PolicyViolation> {
    let mut violations = Vec::new();
    if profile.is_unrestricted() {
        return violations;
    }

    let analysis = analyzer::analyze_proof(
        facts.proof_source,
        facts.solve_kind,
        DependencyInputs {
            explicit: facts.explicit_dependency_count,
            transitive: 0,
            retrieval_depth: 0,
        },
    );
    let observed_tactics = &analysis.observed.tactics_referenced;

    // Forbidden tactics (alias-aware).
    for forbidden in &profile.forbidden_tactics {
        let aliases = alias_expand(forbidden);
        for observed in observed_tactics {
            let hit = observed == forbidden || aliases.contains(&observed.as_str());
            if hit {
                violations.push(PolicyViolation::ForbiddenTactic {
                    tactic: forbidden.clone(),
                    matched: observed.clone(),
                });
            }
        }
    }

    // Allowlist: every observed tactic must be listed.
    if !profile.allowed_tactics.is_empty() {
        for observed in observed_tactics {
            if !profile.allowed_tactics.iter().any(|a| a == observed) {
                violations.push(PolicyViolation::TacticNotAllowed {
                    tactic: observed.clone(),
                });
            }
        }
    }

    // Dependencies: forbidden set + allowlist.
    for dep in facts.dependency_names {
        if profile.forbidden_dependencies.iter().any(|f| f == dep) {
            violations.push(PolicyViolation::ForbiddenDependency {
                dependency: dep.clone(),
            });
        }
        if !profile.allowed_dependencies.is_empty()
            && !profile.allowed_dependencies.iter().any(|a| a == dep)
        {
            violations.push(PolicyViolation::DependencyNotAllowed {
                dependency: dep.clone(),
            });
        }
    }

    if let Some(max) = profile.max_tactic_steps {
        if analysis.observed.tactic_count > max {
            violations.push(PolicyViolation::TooManyTacticSteps {
                used: analysis.observed.tactic_count,
                max,
            });
        }
    }

    if let Some(max) = profile.max_direct_dependencies {
        if facts.explicit_dependency_count > max {
            violations.push(PolicyViolation::TooManyDirectDependencies {
                used: facts.explicit_dependency_count,
                max,
            });
        }
    }

    if let Some(ceiling) = &profile.automation_ceiling {
        let observed = &analysis.classification.automation_level;
        if automation_rank(observed) > automation_rank(ceiling) {
            violations.push(PolicyViolation::AutomationCeilingExceeded {
                observed: observed.clone(),
                ceiling: ceiling.clone(),
            });
        }
    }

    if let Some(required) = &profile.required_proof_format {
        let actual = facts.actual_proof_format.unwrap_or("");
        if actual != required {
            violations.push(PolicyViolation::WrongProofFormat {
                required: required.clone(),
                actual: actual.to_string(),
            });
        }
    }

    if profile.require_intermediate_claims && !analysis.observed.has_intermediate_claims {
        violations.push(PolicyViolation::MissingIntermediateClaims);
    }

    if !profile.allowed_imports.is_empty() {
        for import in facts.import_manifest {
            if !profile.allowed_imports.iter().any(|a| a == import) {
                violations.push(PolicyViolation::ImportNotAllowed {
                    import: import.clone(),
                });
            }
        }
    }

    violations
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts<'a>(src: &'a str, deps: &'a [String], imports: &'a [String]) -> SubmissionFacts<'a> {
        SubmissionFacts {
            proof_source: src,
            solve_kind: "single_theorem",
            dependency_names: deps,
            explicit_dependency_count: deps.len(),
            import_manifest: imports,
            actual_proof_format: Some("flat_tactic_sequence"),
        }
    }

    #[test]
    fn unrestricted_profile_passes_everything() {
        let p = RestrictionProfile::default();
        assert!(p.is_unrestricted());
        let v = check_restrictions(&p, &facts("nlinarith [sq_nonneg a]; ring", &[], &[]));
        assert!(v.is_empty());
    }

    #[test]
    fn forbidden_tactic_is_caught_including_alias() {
        let p = RestrictionProfile {
            forbidden_tactics: vec!["ring".into()],
            ..Default::default()
        };
        // Direct hit.
        let v = check_restrictions(&p, &facts("ring", &[], &[]));
        assert!(matches!(
            v.as_slice(),
            [PolicyViolation::ForbiddenTactic { .. }]
        ));
        // Alias `ring_nf` is also caught even though `ring_nf` != `ring`.
        let v2 = check_restrictions(&p, &facts("ring_nf", &[], &[]));
        assert!(v2.iter().any(|x| matches!(x, PolicyViolation::ForbiddenTactic { matched, .. } if matched == "ring_nf")));
    }

    #[test]
    fn allowlist_rejects_unlisted_tactic() {
        let p = RestrictionProfile {
            allowed_tactics: vec!["exact".into(), "apply".into()],
            ..Default::default()
        };
        let v = check_restrictions(&p, &facts("exact h", &[], &[]));
        assert!(v.is_empty(), "listed tactic passes: {v:?}");
        let v2 = check_restrictions(&p, &facts("simp", &[], &[]));
        assert!(v2.iter().any(
            |x| matches!(x, PolicyViolation::TacticNotAllowed { tactic } if tactic == "simp")
        ));
    }

    #[test]
    fn forbidden_and_unlisted_dependencies() {
        let forbidden = RestrictionProfile {
            forbidden_dependencies: vec!["Mathlib.evil".into()],
            ..Default::default()
        };
        let deps = vec!["Mathlib.evil".to_string(), "Nat.add_comm".to_string()];
        let v = check_restrictions(&forbidden, &facts("exact foo", &deps, &[]));
        assert!(v.iter().any(|x| matches!(x, PolicyViolation::ForbiddenDependency { dependency } if dependency == "Mathlib.evil")));

        let allow = RestrictionProfile {
            allowed_dependencies: vec!["Nat.add_comm".into()],
            ..Default::default()
        };
        let v2 = check_restrictions(&allow, &facts("exact foo", &deps, &[]));
        assert!(v2.iter().any(|x| matches!(x, PolicyViolation::DependencyNotAllowed { dependency } if dependency == "Mathlib.evil")));
    }

    #[test]
    fn step_and_dependency_budgets() {
        let p = RestrictionProfile {
            max_tactic_steps: Some(1),
            max_direct_dependencies: Some(0),
            ..Default::default()
        };
        let deps = vec!["a".to_string()];
        let v = check_restrictions(&p, &facts("intro h; simp; ring", &deps, &[]));
        assert!(v
            .iter()
            .any(|x| matches!(x, PolicyViolation::TooManyTacticSteps { .. })));
        assert!(v.iter().any(|x| matches!(
            x,
            PolicyViolation::TooManyDirectDependencies { used: 1, max: 0 }
        )));
    }

    #[test]
    fn automation_ceiling_and_required_claims_and_format() {
        let p = RestrictionProfile {
            automation_ceiling: Some("light".into()),
            require_intermediate_claims: true,
            required_proof_format: Some("raw_lean_block".into()),
            ..Default::default()
        };
        // nlinarith is heavy > light; no `have`; format is flat not raw.
        let v = check_restrictions(&p, &facts("nlinarith", &[], &[]));
        assert!(v
            .iter()
            .any(|x| matches!(x, PolicyViolation::AutomationCeilingExceeded { .. })));
        assert!(v
            .iter()
            .any(|x| matches!(x, PolicyViolation::MissingIntermediateClaims)));
        assert!(v
            .iter()
            .any(|x| matches!(x, PolicyViolation::WrongProofFormat { .. })));
    }

    #[test]
    fn restricted_imports() {
        let p = RestrictionProfile {
            allowed_imports: vec!["Mathlib.Tactic.Ring".into()],
            ..Default::default()
        };
        let imports = vec![
            "Mathlib.Tactic.Ring".to_string(),
            "Mathlib.Analysis.Whatever".to_string(),
        ];
        let v = check_restrictions(&p, &facts("ring", &[], &imports));
        assert!(v.iter().any(|x| matches!(x, PolicyViolation::ImportNotAllowed { import } if import == "Mathlib.Analysis.Whatever")));
    }

    #[test]
    fn same_enforcement_for_module_submissions() {
        let p = RestrictionProfile {
            forbidden_tactics: vec!["simp".into()],
            ..Default::default()
        };
        let module = SubmissionFacts {
            proof_source: "theorem a : True := by simp\ntheorem root : True := a",
            solve_kind: "verified_module",
            dependency_names: &[],
            explicit_dependency_count: 1,
            import_manifest: &[],
            actual_proof_format: Some("flat_tactic_sequence"),
        };
        let v = check_restrictions(&p, &module);
        assert!(
            v.iter()
                .any(|x| matches!(x, PolicyViolation::ForbiddenTactic { .. })),
            "module uses the SAME layer: {v:?}"
        );
    }

    #[test]
    fn profile_hash_is_stable_and_version_stamped() {
        let p = RestrictionProfile {
            forbidden_tactics: vec!["ring".into()],
            ..Default::default()
        };
        assert_eq!(p.profile_hash(), p.profile_hash());
        assert!(!p.profile_hash().is_empty());
        // A different profile hashes differently.
        let q = RestrictionProfile {
            forbidden_tactics: vec!["simp".into()],
            ..Default::default()
        };
        assert_ne!(p.profile_hash(), q.profile_hash());
    }
}
