//! Issue #240: deterministic, versioned root-vs-cascade classification of an
//! ordered Lean diagnostic list.
//!
//! The verifier can retain several ordered diagnostics; the most *prominent* one
//! is frequently a downstream cascade (e.g. `No goals to be solved` on a tactic
//! that runs after an earlier tactic already closed the goal), not the causal
//! source error. An external policy that treats the prominent diagnostic as the
//! next observation can chase the cascade symptom into repeated, useless
//! repairs while the real obstruction stays hidden.
//!
//! This module computes a compact `DiagnosticSummary` that names the most
//! likely *root* diagnostic and classifies the rest, WITHOUT discarding or
//! rewriting the full ordered list. It is advisory presentation only — a
//! best-effort first pass, deterministic and versioned; it never claims perfect
//! causality and never changes the kernel result.

use crate::models::{LeanDiagnostic, LeanDiagnosticCategory};
use serde::Serialize;

/// Bump when the classification heuristics or output shape change, so a consumer
/// can tell which selection policy produced a summary.
pub const DIAGNOSTIC_SUMMARY_VERSION: &str = "1.0";

/// The class assigned to a single diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticClass {
    RootCandidate,
    CascadeCandidate,
    IndependentError,
    UnsolvedGoal,
    PostGoalTactic,
    UnknownIdentifierFromPriorFailure,
    Unknown,
}

impl DiagnosticClass {
    /// A cascade class is a likely *downstream symptom* — never selected as the
    /// primary root when a non-cascade candidate exists.
    fn is_cascade(self) -> bool {
        matches!(
            self,
            DiagnosticClass::CascadeCandidate
                | DiagnosticClass::PostGoalTactic
                | DiagnosticClass::UnknownIdentifierFromPriorFailure
        )
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DiagnosticCandidate {
    pub diagnostic_index: usize,
    pub classification: DiagnosticClass,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct DiagnosticSummary {
    pub version: String,
    /// Index into the ordered diagnostic list of the selected likely-root
    /// diagnostic, or None when the list is empty.
    pub primary_index: Option<usize>,
    /// Which selection rule chose `primary_index`.
    pub selection_reason: String,
    /// Diagnostics the verifier saw (may exceed `retained_diagnostics` when the
    /// verifier truncated under its diagnostic cap).
    pub total_diagnostics: usize,
    /// Diagnostics actually retained (and classified here).
    pub retained_diagnostics: usize,
    pub cascade_count: usize,
    pub has_additional_diagnostics: bool,
    pub candidates: Vec<DiagnosticCandidate>,
}

fn message_has(d: &LeanDiagnostic, needle: &str) -> bool {
    d.primary_message.to_lowercase().contains(needle)
}

fn has_context(d: &LeanDiagnostic) -> bool {
    d.goal.is_some() || !d.local_context.is_empty() || !d.unsolved_goals.is_empty()
}

/// Classify one diagnostic given the full ordered list (some classes depend on
/// what came before it).
fn classify_one(i: usize, diags: &[LeanDiagnostic]) -> (DiagnosticClass, String) {
    let d = &diags[i];
    let earlier = &diags[..i];
    let earlier_has =
        |cats: &[LeanDiagnosticCategory]| earlier.iter().any(|e| cats.contains(&e.category));

    // Strong cascade: a cleanup tactic reporting "No goals to be solved" after an
    // earlier tactic already closed the goal.
    if message_has(d, "no goals") {
        return (DiagnosticClass::PostGoalTactic, "post_goal_tactic".into());
    }

    match d.category {
        LeanDiagnosticCategory::UnknownDeclaration => {
            // An unknown identifier is a cascade when an earlier source-level
            // failure (parse/elaboration/type) could have suppressed the
            // declaration that would have introduced it; otherwise it is a real,
            // independent name-resolution failure.
            if earlier_has(&[
                LeanDiagnosticCategory::ParseError,
                LeanDiagnosticCategory::ElaborationError,
                LeanDiagnosticCategory::TypeMismatch,
            ]) {
                (
                    DiagnosticClass::UnknownIdentifierFromPriorFailure,
                    "unknown_identifier_after_prior_source_failure".into(),
                )
            } else {
                (
                    DiagnosticClass::IndependentError,
                    "unknown_identifier_no_prior_failure".into(),
                )
            }
        }
        LeanDiagnosticCategory::ParseError => {
            // The first parse error is the root; a later parse error is usually a
            // cascade of the first (the parser never recovered cleanly).
            if earlier_has(&[LeanDiagnosticCategory::ParseError]) {
                (
                    DiagnosticClass::CascadeCandidate,
                    "parse_error_after_earlier_parse_error".into(),
                )
            } else {
                (DiagnosticClass::RootCandidate, "parser_error".into())
            }
        }
        LeanDiagnosticCategory::ElaborationError | LeanDiagnosticCategory::TypeMismatch => {
            // A source-level elaboration/type error is a strong root; if a parse
            // error preceded it, the elaboration is downstream of the syntax.
            if earlier_has(&[LeanDiagnosticCategory::ParseError]) {
                (
                    DiagnosticClass::CascadeCandidate,
                    "elaboration_after_parse_error".into(),
                )
            } else if d.source_span.is_some() {
                (
                    DiagnosticClass::RootCandidate,
                    "concrete_source_failure_with_span".into(),
                )
            } else {
                (
                    DiagnosticClass::RootCandidate,
                    "elaboration_or_type_error".into(),
                )
            }
        }
        LeanDiagnosticCategory::TacticFailure => {
            if has_context(d) {
                (
                    DiagnosticClass::RootCandidate,
                    "tactic_failure_with_concrete_context".into(),
                )
            } else {
                (
                    DiagnosticClass::Unknown,
                    "tactic_failure_without_context".into(),
                )
            }
        }
        LeanDiagnosticCategory::UnsolvedGoals => {
            (DiagnosticClass::UnsolvedGoal, "unsolved_goals".into())
        }
        LeanDiagnosticCategory::ProhibitedConstruct => (
            DiagnosticClass::IndependentError,
            "prohibited_construct".into(),
        ),
        LeanDiagnosticCategory::DependencyMismatch => (
            DiagnosticClass::IndependentError,
            "dependency_mismatch".into(),
        ),
        LeanDiagnosticCategory::Timeout | LeanDiagnosticCategory::InternalError => (
            DiagnosticClass::IndependentError,
            "infrastructure_or_timeout".into(),
        ),
    }
}

/// Classify an ordered diagnostic list and select the most likely root.
/// `total_diagnostics` is the verifier's own count (>= `diags.len()` when the
/// verifier truncated under its diagnostic cap).
pub fn classify_diagnostics(
    diags: &[LeanDiagnostic],
    total_diagnostics: usize,
) -> DiagnosticSummary {
    let candidates: Vec<DiagnosticCandidate> = diags
        .iter()
        .enumerate()
        .map(|(i, _)| {
            let (classification, reason) = classify_one(i, diags);
            DiagnosticCandidate {
                diagnostic_index: i,
                classification,
                reason,
            }
        })
        .collect();

    let cascade_count = candidates
        .iter()
        .filter(|c| c.classification.is_cascade())
        .count();
    let is_cascade = |i: usize| candidates[i].classification.is_cascade();

    // Selection order (issue #240): earliest non-cascade parser/elaboration/type
    // error; then earliest non-cascade tactic failure with concrete context;
    // then earliest non-cascade diagnostic; then earliest diagnostic; else the
    // legacy first-diagnostic fallback (which is None only for an empty list).
    let find = |pred: &dyn Fn(usize) -> bool| (0..diags.len()).find(|&i| pred(i));

    let (primary_index, selection_reason) = if let Some(i) = find(&|i| {
        !is_cascade(i)
            && matches!(
                diags[i].category,
                LeanDiagnosticCategory::ParseError
                    | LeanDiagnosticCategory::ElaborationError
                    | LeanDiagnosticCategory::TypeMismatch
            )
    }) {
        (Some(i), "earliest_non_cascade_parser_or_elaboration_error")
    } else if let Some(i) = find(&|i| {
        !is_cascade(i)
            && diags[i].category == LeanDiagnosticCategory::TacticFailure
            && has_context(&diags[i])
    }) {
        (Some(i), "earliest_non_cascade_tactic_failure_with_context")
    } else if let Some(i) = find(&|i| !is_cascade(i)) {
        (Some(i), "earliest_non_cascade_diagnostic")
    } else if !diags.is_empty() {
        (Some(0), "earliest_diagnostic_all_cascade_fallback")
    } else {
        (None, "no_diagnostics")
    };

    DiagnosticSummary {
        version: DIAGNOSTIC_SUMMARY_VERSION.to_string(),
        primary_index,
        selection_reason: selection_reason.to_string(),
        total_diagnostics: total_diagnostics.max(diags.len()),
        retained_diagnostics: diags.len(),
        cascade_count,
        has_additional_diagnostics: total_diagnostics > diags.len() || diags.len() > 1,
        candidates,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn diag(cat: LeanDiagnosticCategory, msg: &str) -> LeanDiagnostic {
        LeanDiagnostic {
            category: cat,
            primary_message: msg.to_string(),
            source_span: None,
            goal: None,
            local_context: vec![],
            unsolved_goals: vec![],
            used_dependencies: vec![],
            error_code: None,
            canonical_goal_hash: None,
        }
    }

    /// The motivating incident: a `No goals to be solved` cascade masks an
    /// earlier real elaboration failure. The summary must select the elaboration
    /// error as root and mark the "No goals" as a post-goal cascade.
    #[test]
    fn selects_root_over_no_goals_cascade() {
        let mut elab = diag(
            LeanDiagnosticCategory::ElaborationError,
            "type expected, got Foo",
        );
        elab.source_span = Some("12:3".into());
        let diags = vec![
            elab,
            diag(
                LeanDiagnosticCategory::TacticFailure,
                "No goals to be solved",
            ),
        ];
        let s = classify_diagnostics(&diags, 2);
        assert_eq!(s.primary_index, Some(0));
        assert_eq!(
            s.selection_reason,
            "earliest_non_cascade_parser_or_elaboration_error"
        );
        assert_eq!(
            s.candidates[0].classification,
            DiagnosticClass::RootCandidate
        );
        assert_eq!(
            s.candidates[1].classification,
            DiagnosticClass::PostGoalTactic
        );
        assert_eq!(s.cascade_count, 1);
        assert!(s.has_additional_diagnostics);
    }

    /// An unknown identifier following an earlier source failure is a cascade,
    /// not the root; the parse error is the root even though it is first.
    #[test]
    fn unknown_identifier_after_source_failure_is_cascade() {
        let diags = vec![
            diag(LeanDiagnosticCategory::ParseError, "unexpected token"),
            diag(
                LeanDiagnosticCategory::UnknownDeclaration,
                "unknown identifier 'helper'",
            ),
        ];
        let s = classify_diagnostics(&diags, 2);
        assert_eq!(s.primary_index, Some(0));
        assert_eq!(
            s.candidates[1].classification,
            DiagnosticClass::UnknownIdentifierFromPriorFailure
        );
    }

    /// A standalone unknown identifier (no prior failure) is a real independent
    /// error, and — absent any parser/elaboration root — is selected.
    #[test]
    fn standalone_unknown_identifier_is_independent_and_selected() {
        let diags = vec![diag(
            LeanDiagnosticCategory::UnknownDeclaration,
            "unknown identifier 'Nat.foo'",
        )];
        let s = classify_diagnostics(&diags, 1);
        assert_eq!(
            s.candidates[0].classification,
            DiagnosticClass::IndependentError
        );
        assert_eq!(s.primary_index, Some(0));
        assert_eq!(s.selection_reason, "earliest_non_cascade_diagnostic");
    }

    /// A tactic failure carrying a concrete goal/context is preferred over a
    /// later unsolved-goals symptom.
    #[test]
    fn tactic_failure_with_context_preferred() {
        let mut tac = diag(LeanDiagnosticCategory::TacticFailure, "linarith failed");
        tac.goal = Some("a < b".into());
        tac.local_context = vec!["h : a ≤ b".into()];
        let diags = vec![
            diag(LeanDiagnosticCategory::UnsolvedGoals, "unsolved goals"),
            tac,
        ];
        let s = classify_diagnostics(&diags, 2);
        assert_eq!(s.primary_index, Some(1));
        assert_eq!(
            s.selection_reason,
            "earliest_non_cascade_tactic_failure_with_context"
        );
    }

    #[test]
    fn empty_list_has_no_primary() {
        let s = classify_diagnostics(&[], 0);
        assert_eq!(s.primary_index, None);
        assert_eq!(s.selection_reason, "no_diagnostics");
        assert_eq!(s.cascade_count, 0);
        assert!(!s.has_additional_diagnostics);
    }

    #[test]
    fn version_is_stamped() {
        let s = classify_diagnostics(&[diag(LeanDiagnosticCategory::ParseError, "x")], 1);
        assert_eq!(s.version, DIAGNOSTIC_SUMMARY_VERSION);
    }
}
