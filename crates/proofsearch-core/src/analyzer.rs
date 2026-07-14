//! Issue #232: a deterministic post-verification proof-profile analyzer.
//!
//! Given a *verified* proof/module source (the kernel already accepted it), this
//! derives a versioned `ProofProfile` for MathCorpus enrichment and internal
//! evaluation — tactics used, proof class, automation level, structural
//! indicators, and dependency counts. It is PURE and derivative: it reads
//! recorded source text, never runs Lean, and its classification can never
//! affect kernel acceptance. Directly observed facts (`ObservedFacts`, read off
//! the source) are kept strictly separate from heuristic classification
//! (`HeuristicClassification`), and a manual `annotations` layer sits on top —
//! it can add notes but can never overwrite machine-derived evidence.
//!
//! Determinism: the same source + solve kind + dependency inputs always produce
//! the same profile (`profile_hash` over observed+classification, excluding
//! human annotations). Regenerable at any time from persisted artifacts.

use serde::{Deserialize, Serialize};

/// Bump on any change to the derivation rules or field set. Recorded on every
/// profile so a consumer knows which analyzer produced it.
pub const ANALYZER_VERSION: &str = "1.0";

/// Tactic tokens the analyzer recognizes. Presence is an OBSERVED fact.
const KNOWN_TACTICS: &[&str] = &[
    "exact",
    "apply",
    "refine",
    "rfl",
    "assumption",
    "trivial",
    "exact?",
    "apply?",
    "simp",
    "simp_all",
    "simpa",
    "dsimp",
    "norm_num",
    "norm_cast",
    "push_cast",
    "ring",
    "ring_nf",
    "linarith",
    "nlinarith",
    "polyrith",
    "positivity",
    "gcongr",
    "omega",
    "decide",
    "native_decide",
    "field_simp",
    "aesop",
    "tauto",
    "induction",
    "cases",
    "rcases",
    "obtain",
    "rintro",
    "match",
    "constructor",
    "use",
    "exists",
    "refine'",
    "exact_mod_cast",
    "rw",
    "rewrite",
    "subst",
    "conv",
    "calc",
    "show",
    "change",
    "intro",
    "intros",
    "by_contra",
    "absurd",
    "exfalso",
    "contradiction",
    "have",
    "suffices",
    "let",
    "set",
    "generalize",
    "left",
    "right",
    "split",
    "ext",
    "funext",
    "congr",
    "convert",
    "unfold",
    "delta",
    "rotate_left",
    "rotate_right",
    "swap",
];

/// Automation-heavy tactics — their presence raises `automation_level`.
const HEAVY_AUTOMATION: &[&str] = &["nlinarith", "polyrith", "decide", "native_decide", "aesop"];
const MODERATE_AUTOMATION: &[&str] = &[
    "ring",
    "ring_nf",
    "linarith",
    "simp",
    "simp_all",
    "omega",
    "field_simp",
    "positivity",
    "tauto",
];
const LIGHT_AUTOMATION: &[&str] = &[
    "norm_num",
    "norm_cast",
    "push_cast",
    "rfl",
    "trivial",
    "assumption",
    "dsimp",
];

/// Facts read directly off the verified source — not heuristics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservedFacts {
    /// Recognized tactic tokens present, sorted + deduped.
    pub tactics_referenced: Vec<String>,
    /// Dotted identifiers used (e.g. `Nat.add_comm`), sorted + deduped — a
    /// heuristic view of referenced declarations, flagged as such.
    pub declarations_referenced: Vec<String>,
    /// Occurrences of recognized tactic tokens (a proxy for step count).
    pub tactic_count: usize,
    pub proof_length_bytes: usize,
    /// Focus bullets `·`, `case` labels, and `<;>` combinators.
    pub branch_case_count: usize,
    /// Supplied by the caller from the verified dependency graph (#224).
    pub explicit_dependency_count: usize,
    pub transitive_dependency_count: usize,
    /// Longest dependency chain depth, if the caller computed it.
    pub retrieval_depth: usize,
    pub uses_induction: bool,
    pub uses_contradiction: bool,
    pub constructs_witness: bool,
    pub uses_rewriting: bool,
    pub has_intermediate_claims: bool,
    /// "single_theorem" or "verified_module".
    pub solve_kind: String,
}

/// Heuristic labels DERIVED from the observed facts — explicitly not truth.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeuristicClassification {
    pub primary_proof_class: String,
    pub secondary_proof_class: Option<String>,
    /// none | light | moderate | heavy.
    pub automation_level: String,
    pub note: String,
}

/// A human annotation. Layered on top; never overwrites machine evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileAnnotation {
    pub author: String,
    pub note: String,
}

/// A versioned, deterministic profile of a verified proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofProfile {
    pub analyzer_version: String,
    pub observed: ObservedFacts,
    pub classification: HeuristicClassification,
    /// Manual annotations — additive only.
    pub annotations: Vec<ProfileAnnotation>,
    /// Canonical hash over analyzer_version + observed + classification (NOT
    /// annotations): same source + inputs => same hash.
    pub profile_hash: String,
}

impl ProofProfile {
    /// Add a human annotation WITHOUT touching machine-derived evidence.
    /// Returns the (unchanged) `profile_hash` to make the invariant explicit —
    /// annotations never change the machine hash.
    pub fn annotate(&mut self, author: &str, note: &str) -> String {
        self.annotations.push(ProfileAnnotation {
            author: author.to_string(),
            note: note.to_string(),
        });
        self.profile_hash.clone()
    }
}

/// Dependency inputs the caller supplies from the verified graph (#224).
#[derive(Debug, Clone, Copy, Default)]
pub struct DependencyInputs {
    pub explicit: usize,
    pub transitive: usize,
    pub retrieval_depth: usize,
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '\'' || c == '?'
}

/// Tokenize into identifier-like tokens (keeping dotted names and the trailing
/// `?` of `exact?`/`simp?`).
fn tokens(source: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in source.chars() {
        if is_ident_char(c) {
            cur.push(c);
        } else if !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Derive a deterministic `ProofProfile` from verified proof source.
pub fn analyze_proof(source: &str, solve_kind: &str, deps: DependencyInputs) -> ProofProfile {
    let toks = tokens(source);
    let known: std::collections::HashSet<&str> = KNOWN_TACTICS.iter().copied().collect();

    // Observed: recognized tactic tokens (sorted/deduped) + raw occurrence count.
    let mut present: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut tactic_count = 0usize;
    for t in &toks {
        if known.contains(t.as_str()) {
            present.insert(t.clone());
            tactic_count += 1;
        }
    }
    let tactics_referenced: Vec<String> = present.iter().cloned().collect();

    // Referenced declarations: dotted identifiers (heuristic), sorted/deduped.
    let mut decls: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for t in &toks {
        if t.contains('.') && t.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) {
            decls.insert(t.clone());
        }
    }
    let declarations_referenced: Vec<String> = decls.iter().cloned().collect();

    let has = |name: &str| present.contains(name);
    let uses_induction = has("induction");
    let uses_contradiction =
        has("by_contra") || has("absurd") || has("exfalso") || has("contradiction");
    let constructs_witness =
        has("use") || has("exists") || has("constructor") || source.contains('⟨') || has("refine");
    let uses_rewriting = has("rw")
        || has("rewrite")
        || has("simp")
        || has("simp_all")
        || has("subst")
        || has("conv");
    let has_intermediate_claims =
        has("have") || has("suffices") || has("calc") || has("set") || has("let");

    // Branch/case structure: focus bullets, `case` labels, `<;>` combinators.
    let branch_case_count = source.matches('·').count()
        + source.matches("<;>").count()
        + toks.iter().filter(|t| t.as_str() == "case").count()
        + if has("cases") || has("rcases") || has("obtain") {
            1
        } else {
            0
        };

    let observed = ObservedFacts {
        tactics_referenced,
        declarations_referenced,
        tactic_count,
        proof_length_bytes: source.len(),
        branch_case_count,
        explicit_dependency_count: deps.explicit,
        transitive_dependency_count: deps.transitive,
        retrieval_depth: deps.retrieval_depth,
        uses_induction,
        uses_contradiction,
        constructs_witness,
        uses_rewriting,
        has_intermediate_claims,
        solve_kind: solve_kind.to_string(),
    };

    let classification = classify(&observed, &present);

    let hashable = serde_json::json!({
        "analyzer_version": ANALYZER_VERSION,
        "observed": &observed,
        "classification": &classification,
    });
    let profile_hash = crate::hashing::canonical_hash(&hashable).unwrap_or_default();

    ProofProfile {
        analyzer_version: ANALYZER_VERSION.to_string(),
        observed,
        classification,
        annotations: Vec::new(),
        profile_hash,
    }
}

fn classify(
    obs: &ObservedFacts,
    present: &std::collections::BTreeSet<String>,
) -> HeuristicClassification {
    let has = |name: &str| present.contains(name);

    // Ordered candidate classes; the first two that apply become primary/secondary.
    let mut classes: Vec<&str> = Vec::new();
    if obs.uses_induction {
        classes.push("induction");
    }
    if obs.uses_contradiction {
        classes.push("contradiction");
    }
    if has("cases") || has("rcases") || has("obtain") {
        classes.push("case_analysis");
    }
    if obs.constructs_witness {
        classes.push("witness_construction");
    }
    if has("calc") {
        classes.push("calculation");
    }
    let automation_present = HEAVY_AUTOMATION
        .iter()
        .chain(MODERATE_AUTOMATION)
        .any(|t| has(t));
    if automation_present {
        classes.push("automation");
    }
    if has("rw") || has("rewrite") || has("simp_all") || has("subst") {
        classes.push("rewriting");
    }
    if has("exact") || has("apply") || has("refine") {
        classes.push("direct_application");
    }
    if classes.is_empty() {
        classes.push("other");
    }

    let automation_level = if HEAVY_AUTOMATION.iter().any(|t| has(t)) {
        "heavy"
    } else if MODERATE_AUTOMATION.iter().any(|t| has(t)) {
        "moderate"
    } else if LIGHT_AUTOMATION.iter().any(|t| has(t)) {
        "light"
    } else {
        "none"
    };

    HeuristicClassification {
        primary_proof_class: classes[0].to_string(),
        secondary_proof_class: classes.get(1).map(|s| s.to_string()),
        automation_level: automation_level.to_string(),
        note: "heuristic classification derived from observed tactic tokens; NOT kernel truth and never affects acceptance".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn profile(src: &str) -> ProofProfile {
        analyze_proof(src, "single_theorem", DependencyInputs::default())
    }

    #[test]
    fn direct_theorem_application() {
        let p = profile("exact Nat.add_comm a b");
        assert!(p.observed.tactics_referenced.contains(&"exact".to_string()));
        assert_eq!(p.classification.primary_proof_class, "direct_application");
        assert_eq!(p.classification.automation_level, "none");
        assert!(p
            .observed
            .declarations_referenced
            .contains(&"Nat.add_comm".to_string()));
    }

    #[test]
    fn simp_is_moderate_automation() {
        let p = profile("simp [foo, bar]");
        assert_eq!(p.classification.primary_proof_class, "automation");
        assert_eq!(p.classification.automation_level, "moderate");
        assert!(p.observed.uses_rewriting);
    }

    #[test]
    fn ring_and_linarith_are_automation() {
        assert_eq!(profile("ring").classification.automation_level, "moderate");
        assert_eq!(
            profile("linarith [h1, h2]").classification.automation_level,
            "moderate"
        );
    }

    #[test]
    fn nlinarith_with_witness_is_heavy() {
        let p = profile("nlinarith [sq_nonneg (a - b), mul_pos ha hb]");
        assert_eq!(p.classification.automation_level, "heavy");
        assert!(p
            .observed
            .tactics_referenced
            .contains(&"nlinarith".to_string()));
    }

    #[test]
    fn induction_is_detected_and_primary() {
        let p = profile("induction n with\n  | zero => rfl\n  | succ k ih => simp [ih]");
        assert!(p.observed.uses_induction);
        assert_eq!(p.classification.primary_proof_class, "induction");
    }

    #[test]
    fn cases_is_case_analysis() {
        let p = profile("cases h with\n  | inl ha => exact ha\n  | inr hb => exact hb");
        assert_eq!(p.classification.primary_proof_class, "case_analysis");
        assert!(p.observed.branch_case_count >= 1);
    }

    #[test]
    fn contradiction_and_intermediate_claims() {
        let p = profile("by_contra h\n  have h2 : False := absurd rfl h\n  exact h2");
        assert!(p.observed.uses_contradiction);
        assert!(p.observed.has_intermediate_claims);
        assert_eq!(p.classification.primary_proof_class, "contradiction");
    }

    #[test]
    fn multi_lemma_module_solve_kind_and_deps() {
        let p = analyze_proof(
            "theorem a : True := trivial\ntheorem root : True := a",
            "verified_module",
            DependencyInputs {
                explicit: 3,
                transitive: 6,
                retrieval_depth: 2,
            },
        );
        assert_eq!(p.observed.solve_kind, "verified_module");
        assert_eq!(p.observed.explicit_dependency_count, 3);
        assert_eq!(p.observed.transitive_dependency_count, 6);
        assert_eq!(p.observed.retrieval_depth, 2);
    }

    #[test]
    fn same_source_and_inputs_produce_identical_profile() {
        let src = "induction n with | zero => simp | succ k ih => nlinarith [ih]";
        let a = analyze_proof(
            src,
            "single_theorem",
            DependencyInputs {
                explicit: 1,
                transitive: 2,
                retrieval_depth: 1,
            },
        );
        let b = analyze_proof(
            src,
            "single_theorem",
            DependencyInputs {
                explicit: 1,
                transitive: 2,
                retrieval_depth: 1,
            },
        );
        assert_eq!(a.profile_hash, b.profile_hash);
        assert_eq!(a, b);
    }

    #[test]
    fn annotation_never_overwrites_machine_evidence() {
        let mut p = profile("ring");
        let before = p.clone();
        let hash = p.annotate("reviewer-1", "looks like a routine algebra identity");
        // Machine-derived evidence + hash unchanged; only annotations grew.
        assert_eq!(hash, before.profile_hash);
        assert_eq!(p.profile_hash, before.profile_hash);
        assert_eq!(p.observed, before.observed);
        assert_eq!(p.classification, before.classification);
        assert_eq!(p.annotations.len(), 1);
    }
}
