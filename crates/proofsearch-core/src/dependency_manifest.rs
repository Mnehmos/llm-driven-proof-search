//! Issue #234: a verifier-backed dependency & retrieval manifest.
//!
//! Proof Search already stores obligation edges and verified lemma IDs, but not
//! one complete, corpus-ready record that keeps DECLARED, APPROVED, actually
//! USED, Mathlib-referenced, and module-item dependencies distinct — plus
//! retrieved candidates and their unused remainder. This module builds that
//! manifest deterministically from persisted state (reusing the #224 graph and
//! the #232 analyzer), hash-pins it for replay comparison, and — critically —
//! represents uninstrumented categories as UNKNOWN, never as an empty proven
//! set (an empty list would falsely claim "nothing was used/retrieved").

use crate::analyzer;
use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Bump on any change to the manifest field set or derivation.
pub const DEPENDENCY_MANIFEST_VERSION: &str = "1.0";

/// A set of dependency/declaration names with an explicit instrumentation flag.
/// `instrumented: false` means the category was NOT captured — distinct from an
/// instrumented-but-empty set.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DependencySet {
    pub instrumented: bool,
    pub names: Vec<String>,
}

impl DependencySet {
    pub fn known(mut names: Vec<String>) -> Self {
        names.sort();
        names.dedup();
        DependencySet {
            instrumented: true,
            names,
        }
    }
    pub fn unknown() -> Self {
        DependencySet {
            instrumented: false,
            names: Vec::new(),
        }
    }
}

/// One retrieved candidate and its score (retrieval instrumentation, #234).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RetrievedCandidate {
    pub name: String,
    pub score: f64,
    pub used: bool,
}

/// Retrieval record — `instrumented: false` when no retrieval was tracked for
/// this proof (the common case today), never an empty "retrieved nothing".
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RetrievalRecord {
    pub instrumented: bool,
    pub candidates: Vec<RetrievedCandidate>,
}

impl RetrievalRecord {
    pub fn unknown() -> Self {
        RetrievalRecord {
            instrumented: false,
            candidates: Vec::new(),
        }
    }
}

/// A verifier-backed dependency manifest for one accepted solve.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DependencyManifest {
    pub manifest_version: String,
    /// Bound to the exact environment + import manifest the names resolve under.
    pub environment_hash: String,
    pub import_manifest: Vec<String>,
    pub solve_kind: String,
    /// Distinct categories — never conflated.
    pub declared_dependencies: DependencySet,
    pub approved_obligation_dependencies: DependencySet,
    pub actual_used_verified_lemmas: DependencySet,
    pub mathlib_declarations_referenced: DependencySet,
    /// Verified module item declaration edges (module solves only).
    pub verified_module_item_edges: DependencySet,
    pub retrieved_candidates: RetrievalRecord,
    /// Retrieved but not used (derivable only when retrieval is instrumented).
    pub retrieved_but_unused: RetrievalRecord,
    pub direct_dependency_count: usize,
    pub transitive_dependency_count: usize,
    pub retrieval_depth: usize,
    /// Canonical hash over everything above — replay regenerates + compares.
    pub manifest_hash: String,
}

/// Pure inputs for `assemble_manifest`, so the aggregation is unit-testable
/// without a database.
pub struct ManifestInputs {
    pub environment_hash: String,
    pub import_manifest: Vec<String>,
    pub solve_kind: String,
    pub declared_dependencies: DependencySet,
    pub approved_obligation_dependencies: DependencySet,
    pub actual_used_verified_lemmas: DependencySet,
    pub mathlib_declarations_referenced: DependencySet,
    pub verified_module_item_edges: DependencySet,
    pub retrieved_candidates: RetrievalRecord,
    pub direct_dependency_count: usize,
    pub transitive_dependency_count: usize,
    pub retrieval_depth: usize,
}

/// Assemble a deterministic manifest from already-gathered inputs. Derives
/// `retrieved_but_unused` from the retrieval record (unknown if retrieval is
/// uninstrumented) and hashes the whole thing.
pub fn assemble_manifest(inputs: ManifestInputs) -> DependencyManifest {
    let retrieved_but_unused = if inputs.retrieved_candidates.instrumented {
        RetrievalRecord {
            instrumented: true,
            candidates: inputs
                .retrieved_candidates
                .candidates
                .iter()
                .filter(|c| !c.used)
                .cloned()
                .collect(),
        }
    } else {
        RetrievalRecord::unknown()
    };

    let mut manifest = DependencyManifest {
        manifest_version: DEPENDENCY_MANIFEST_VERSION.to_string(),
        environment_hash: inputs.environment_hash,
        import_manifest: inputs.import_manifest,
        solve_kind: inputs.solve_kind,
        declared_dependencies: inputs.declared_dependencies,
        approved_obligation_dependencies: inputs.approved_obligation_dependencies,
        actual_used_verified_lemmas: inputs.actual_used_verified_lemmas,
        mathlib_declarations_referenced: inputs.mathlib_declarations_referenced,
        verified_module_item_edges: inputs.verified_module_item_edges,
        retrieved_candidates: inputs.retrieved_candidates,
        retrieved_but_unused,
        direct_dependency_count: inputs.direct_dependency_count,
        transitive_dependency_count: inputs.transitive_dependency_count,
        retrieval_depth: inputs.retrieval_depth,
        manifest_hash: String::new(),
    };
    manifest.manifest_hash = crate::hashing::canonical_hash(&manifest).unwrap_or_default();
    manifest
}

/// Build the manifest for an accepted obligation solve from persisted state.
/// `declared` is the client-declared/approved dependency id list (unknown when
/// not supplied). Retrieval is `unknown` until a retrieval stage is instrumented.
pub fn build_dependency_manifest(
    conn: &Connection,
    episode_id: Uuid,
    obligation_id: Uuid,
    proof_source: &str,
    environment_hash: &str,
    import_manifest: &[String],
    declared: Option<Vec<String>>,
) -> Result<DependencyManifest, String> {
    // Approved obligation dependencies: the recorded edges.
    let approved_ids: Vec<String> = {
        let mut stmt = conn
            .prepare("SELECT dependency_obligation_id FROM episode_obligation_edges WHERE parent_obligation_id = ?1")
            .map_err(|e| e.to_string())?;
        let rows = stmt
            .query_map([obligation_id.to_string()], |r| r.get::<_, String>(0))
            .map_err(|e| e.to_string())?;
        let mut v = Vec::new();
        for r in rows {
            v.push(r.map_err(|e| e.to_string())?);
        }
        v
    };
    let mut approved_names = Vec::new();
    let mut used_lemmas = Vec::new();
    for dep_id in &approved_ids {
        if let Some(name) = conn
            .query_row(
                "SELECT theorem_name FROM episode_obligations WHERE id = ?1",
                [dep_id],
                |r| r.get::<_, String>(0),
            )
            .optional()
            .map_err(|e| e.to_string())?
        {
            approved_names.push(name);
        }
        if let Some(lemma) = conn
            .query_row(
                "SELECT theorem_name FROM episode_verified_lemmas WHERE obligation_id = ?1 AND polarity = 'positive'",
                [dep_id],
                |r| r.get::<_, String>(0),
            )
            .optional()
            .map_err(|e| e.to_string())?
        {
            used_lemmas.push(lemma);
        }
    }

    // Mathlib declarations referenced: dotted names the analyzer observed.
    let analysis = analyzer::analyze_proof(
        proof_source,
        "single_theorem",
        analyzer::DependencyInputs::default(),
    );
    let mathlib_refs = analysis.observed.declarations_referenced.clone();

    // Verified module item edges (module solves only).
    let module_items: Option<String> = conn
        .query_row(
            "SELECT declaration_manifest_hash FROM episode_verified_modules WHERE root_obligation_id = ?1 ORDER BY verified_at DESC LIMIT 1",
            [obligation_id.to_string()],
            |r| r.get::<_, String>(0),
        )
        .optional()
        .map_err(|e| e.to_string())?;
    let (solve_kind, module_edges) = match module_items {
        Some(hash) => (
            "verified_module".to_string(),
            DependencySet::known(vec![format!("declaration_manifest:{hash}")]),
        ),
        None => ("single_theorem".to_string(), DependencySet::unknown()),
    };

    let direct = approved_ids.len();

    // NOTE: transitive count/depth default to the direct count here; the module
    // tool's order_closure (#224) computes the true transitive closure and the
    // caller can pass it through once wired at the solve site. Never inflated.
    // episode_id is reserved for episode-scoped retrieval instrumentation (#234
    // follow-up) — retrieval is `unknown` until a retrieval stage is tracked.
    let _ = episode_id;

    Ok(assemble_manifest(ManifestInputs {
        environment_hash: environment_hash.to_string(),
        import_manifest: import_manifest.to_vec(),
        solve_kind,
        declared_dependencies: declared
            .map(DependencySet::known)
            .unwrap_or_else(DependencySet::unknown),
        approved_obligation_dependencies: DependencySet::known(approved_names),
        actual_used_verified_lemmas: DependencySet::known(used_lemmas),
        mathlib_declarations_referenced: DependencySet::known(mathlib_refs),
        verified_module_item_edges: module_edges,
        retrieved_candidates: RetrievalRecord::unknown(),
        direct_dependency_count: direct,
        transitive_dependency_count: direct,
        retrieval_depth: 0,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(names: &[&str]) -> DependencySet {
        DependencySet::known(names.iter().map(|s| s.to_string()).collect())
    }

    #[test]
    fn categories_stay_distinct_and_hash_is_deterministic() {
        let inputs = || ManifestInputs {
            environment_hash: "env".into(),
            import_manifest: vec!["Mathlib.Tactic.Ring".into()],
            solve_kind: "single_theorem".into(),
            declared_dependencies: set(&["A", "B", "C"]),
            approved_obligation_dependencies: set(&["A", "B"]),
            actual_used_verified_lemmas: set(&["A"]),
            mathlib_declarations_referenced: set(&["Nat.add_comm"]),
            verified_module_item_edges: DependencySet::unknown(),
            retrieved_candidates: RetrievalRecord::unknown(),
            direct_dependency_count: 2,
            transitive_dependency_count: 3,
            retrieval_depth: 1,
        };
        let m1 = assemble_manifest(inputs());
        let m2 = assemble_manifest(inputs());
        assert_eq!(m1.manifest_hash, m2.manifest_hash);
        assert!(!m1.manifest_hash.is_empty());
        // Declared, approved, and used are NOT conflated.
        assert_eq!(m1.declared_dependencies.names, vec!["A", "B", "C"]);
        assert_eq!(m1.approved_obligation_dependencies.names, vec!["A", "B"]);
        assert_eq!(m1.actual_used_verified_lemmas.names, vec!["A"]);
        assert_eq!(
            m1.mathlib_declarations_referenced.names,
            vec!["Nat.add_comm"]
        );
    }

    #[test]
    fn uninstrumented_categories_are_unknown_not_empty_proven_sets() {
        let m = assemble_manifest(ManifestInputs {
            environment_hash: "env".into(),
            import_manifest: vec![],
            solve_kind: "single_theorem".into(),
            declared_dependencies: DependencySet::unknown(),
            approved_obligation_dependencies: set(&[]),
            actual_used_verified_lemmas: set(&[]),
            mathlib_declarations_referenced: set(&[]),
            verified_module_item_edges: DependencySet::unknown(),
            retrieved_candidates: RetrievalRecord::unknown(),
            direct_dependency_count: 0,
            transitive_dependency_count: 0,
            retrieval_depth: 0,
        });
        // Declared/retrieval: NOT instrumented (unknown), distinct from the
        // genuinely-empty-but-instrumented approved/used sets.
        assert!(!m.declared_dependencies.instrumented);
        assert!(!m.retrieved_candidates.instrumented);
        assert!(!m.retrieved_but_unused.instrumented);
        assert!(m.approved_obligation_dependencies.instrumented);
        assert!(m.approved_obligation_dependencies.names.is_empty());
    }

    #[test]
    fn retrieved_but_unused_is_derived_when_retrieval_is_instrumented() {
        let retrieval = RetrievalRecord {
            instrumented: true,
            candidates: vec![
                RetrievedCandidate {
                    name: "used_one".into(),
                    score: 0.9,
                    used: true,
                },
                RetrievedCandidate {
                    name: "wasted_one".into(),
                    score: 0.4,
                    used: false,
                },
            ],
        };
        let m = assemble_manifest(ManifestInputs {
            environment_hash: "env".into(),
            import_manifest: vec![],
            solve_kind: "single_theorem".into(),
            declared_dependencies: DependencySet::unknown(),
            approved_obligation_dependencies: set(&[]),
            actual_used_verified_lemmas: set(&["used_one"]),
            mathlib_declarations_referenced: set(&[]),
            verified_module_item_edges: DependencySet::unknown(),
            retrieved_candidates: retrieval,
            direct_dependency_count: 0,
            transitive_dependency_count: 0,
            retrieval_depth: 0,
        });
        assert!(m.retrieved_but_unused.instrumented);
        assert_eq!(m.retrieved_but_unused.candidates.len(), 1);
        assert_eq!(m.retrieved_but_unused.candidates[0].name, "wasted_one");
    }
}
