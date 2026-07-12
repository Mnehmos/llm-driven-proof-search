//! Issue #235: controlled mutation generator for synthetic negative examples.
//!
//! MathCorpus needs realistic *labeled* failures. Given a VERIFIED proof, this
//! deterministically produces synthetic negatives — each stamped
//! `provenance = "synthetic_mutation"` so it can NEVER be conflated with an
//! organic (real attempt) failure — carrying the mutation kind, an EXPECTED
//! verifier outcome, and a content hash. A mutation is a proposal: its expected
//! outcome should be confirmed by the real verifier before use (the expected
//! label is honest about being expected, not observed).
//!
//! Only mutations that actually apply to a given source are emitted, and the
//! same source always yields the same set (deterministic, replayable).

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Bump on any change to the mutation catalog or transforms.
pub const MUTATION_GENERATOR_VERSION: &str = "1.0";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MutationKind {
    WrongTheoremName,
    WrongCoefficient,
    FlippedRewriteDirection,
    MissingHypothesis,
    MalformedSyntax,
    IncompleteGoal,
}

impl MutationKind {
    /// The verifier outcome this mutation is DESIGNED to induce (expected, to be
    /// confirmed by a real run — never asserted as observed).
    pub fn expected_outcome(self) -> &'static str {
        match self {
            MutationKind::WrongTheoremName => "unknown_identifier",
            MutationKind::WrongCoefficient => "kernel_fail",
            MutationKind::FlippedRewriteDirection => "kernel_fail",
            MutationKind::MissingHypothesis => "kernel_fail",
            MutationKind::MalformedSyntax => "parse_error",
            MutationKind::IncompleteGoal => "unsolved_goals",
        }
    }
}

/// One labeled synthetic negative. `provenance` is fixed to synthetic so it is
/// never mistaken for an organic failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyntheticNegative {
    pub generator_version: String,
    /// Always "synthetic_mutation" — the organic/synthetic firewall.
    pub provenance: String,
    pub kind: MutationKind,
    pub description: String,
    pub mutated_source: String,
    /// Expected (not yet observed) verifier outcome.
    pub expected_outcome: String,
    /// SHA-256 of the ORIGINAL verified source.
    pub source_hash: String,
    /// SHA-256 of the mutated source.
    pub mutation_hash: String,
}

fn sha(s: &str) -> String {
    let mut h = Sha256::new();
    h.update(s.as_bytes());
    format!("{:x}", h.finalize())
}

fn make(
    kind: MutationKind,
    description: &str,
    original: &str,
    mutated: String,
) -> SyntheticNegative {
    SyntheticNegative {
        generator_version: MUTATION_GENERATOR_VERSION.to_string(),
        provenance: "synthetic_mutation".to_string(),
        kind,
        description: description.to_string(),
        expected_outcome: kind.expected_outcome().to_string(),
        source_hash: sha(original),
        mutation_hash: sha(&mutated),
        mutated_source: mutated,
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '\''
}

/// First dotted identifier (e.g. `Nat.add_comm`) as a (start,end) byte range.
fn first_dotted_ident(src: &str) -> Option<(usize, usize)> {
    let bytes = src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            let mut has_dot = false;
            while i < bytes.len() && is_ident_char(bytes[i] as char) {
                if bytes[i] == b'.' {
                    has_dot = true;
                }
                i += 1;
            }
            if has_dot && i - start > 1 {
                return Some((start, i));
            }
        } else {
            i += 1;
        }
    }
    None
}

/// First standalone integer literal as a (start,end) byte range.
fn first_number(src: &str) -> Option<(usize, usize)> {
    let bytes = src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_digit() {
            let prev_ident = i > 0 && is_ident_char(bytes[i - 1] as char);
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            // Skip digits that are part of an identifier (e.g. `h1`).
            if !prev_ident {
                return Some((start, i));
            }
        } else {
            i += 1;
        }
    }
    None
}

/// Deterministically generate the synthetic negatives that apply to `source`.
pub fn generate_mutations(source: &str) -> Vec<SyntheticNegative> {
    let mut out = Vec::new();

    // Wrong theorem name: rename the first referenced dotted lemma to a bogus one.
    if let Some((s, e)) = first_dotted_ident(source) {
        let mut m = String::with_capacity(source.len() + 16);
        m.push_str(&source[..s]);
        m.push_str("Nonexistent.bogus_lemma_zzz");
        m.push_str(&source[e..]);
        out.push(make(
            MutationKind::WrongTheoremName,
            &format!(
                "renamed referenced declaration `{}` to a nonexistent one",
                &source[s..e]
            ),
            source,
            m,
        ));
    }

    // Wrong coefficient: bump the first integer literal by one.
    if let Some((s, e)) = first_number(source) {
        if let Ok(n) = source[s..e].parse::<u64>() {
            let mut m = String::with_capacity(source.len() + 2);
            m.push_str(&source[..s]);
            m.push_str(&(n.wrapping_add(1)).to_string());
            m.push_str(&source[e..]);
            out.push(make(
                MutationKind::WrongCoefficient,
                &format!("changed literal `{}` to `{}`", n, n + 1),
                source,
                m,
            ));
        }
    }

    // Flipped rewrite direction: `rw [X` -> `rw [← X` (or remove an existing ←).
    if let Some(pos) = source.find("rw [") {
        let after = pos + "rw [".len();
        let mutated = if source[after..].trim_start().starts_with('←') {
            // Remove the first ← after `rw [`.
            let arrow = source[after..].find('←').unwrap() + after;
            let mut m = source.to_string();
            m.replace_range(arrow..arrow + '←'.len_utf8(), "");
            m
        } else {
            let mut m = String::with_capacity(source.len() + 4);
            m.push_str(&source[..after]);
            m.push_str("← ");
            m.push_str(&source[after..]);
            m
        };
        out.push(make(
            MutationKind::FlippedRewriteDirection,
            "flipped the direction of the first `rw` lemma",
            source,
            mutated,
        ));
    }

    // Missing hypothesis: drop the first `have ... := ...` line.
    if let Some(line_start) = source
        .lines()
        .position(|l| l.trim_start().starts_with("have "))
    {
        let kept: Vec<&str> = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i != line_start)
            .map(|(_, l)| l)
            .collect();
        out.push(make(
            MutationKind::MissingHypothesis,
            "removed the first intermediate `have` claim its later steps depend on",
            source,
            kept.join("\n"),
        ));
    }

    // Malformed syntax: unbalance the first bracket.
    if let Some(pos) = source.find('[') {
        let mut m = source.to_string();
        m.insert(pos, '[');
        out.push(make(
            MutationKind::MalformedSyntax,
            "introduced an unbalanced `[` (parse error)",
            source,
            m,
        ));
    }

    // Incomplete goal: drop the last non-empty line (leaves goals unsolved).
    let mut lines: Vec<&str> = source.lines().collect();
    if let Some(last_nonempty) = lines.iter().rposition(|l| !l.trim().is_empty()) {
        if last_nonempty < lines.len() || !lines.is_empty() {
            lines.remove(last_nonempty);
            let mutated = lines.join("\n");
            if mutated != source {
                out.push(make(
                    MutationKind::IncompleteGoal,
                    "removed the final tactic, leaving the goal unsolved",
                    source,
                    mutated,
                ));
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const PROOF: &str = "have h2 : a = b := Nat.add_comm a b\n  rw [h2]\n  exact congrArg f 2";

    fn kinds(neg: &[SyntheticNegative]) -> Vec<MutationKind> {
        neg.iter().map(|n| n.kind).collect()
    }

    #[test]
    fn every_negative_is_synthetic_labeled_with_expected_outcome_and_hashes() {
        let neg = generate_mutations(PROOF);
        assert!(!neg.is_empty());
        for n in &neg {
            assert_eq!(n.provenance, "synthetic_mutation", "never organic");
            assert!(!n.expected_outcome.is_empty());
            assert_eq!(n.source_hash, sha(PROOF));
            assert_eq!(n.mutation_hash, sha(&n.mutated_source));
            assert_ne!(n.mutated_source, PROOF, "a mutation must change the source");
        }
    }

    #[test]
    fn generation_is_deterministic() {
        assert_eq!(generate_mutations(PROOF), generate_mutations(PROOF));
    }

    #[test]
    fn applicable_mutation_kinds_are_emitted() {
        let k = kinds(&generate_mutations(PROOF));
        assert!(k.contains(&MutationKind::WrongTheoremName)); // Nat.add_comm
        assert!(k.contains(&MutationKind::WrongCoefficient)); // 2
        assert!(k.contains(&MutationKind::FlippedRewriteDirection)); // rw [h2]
        assert!(k.contains(&MutationKind::MissingHypothesis)); // have h2
        assert!(k.contains(&MutationKind::MalformedSyntax)); // [
        assert!(k.contains(&MutationKind::IncompleteGoal));
    }

    #[test]
    fn wrong_theorem_name_targets_a_dotted_reference() {
        let n = generate_mutations(PROOF)
            .into_iter()
            .find(|n| n.kind == MutationKind::WrongTheoremName)
            .unwrap();
        assert!(n.mutated_source.contains("Nonexistent.bogus_lemma_zzz"));
        assert!(!n.mutated_source.contains("Nat.add_comm"));
        assert_eq!(n.expected_outcome, "unknown_identifier");
    }

    #[test]
    fn coefficient_mutation_bumps_the_literal() {
        let n = generate_mutations(PROOF)
            .into_iter()
            .find(|n| n.kind == MutationKind::WrongCoefficient)
            .unwrap();
        assert!(n.mutated_source.contains("congrArg f 3"));
    }

    #[test]
    fn a_proof_with_no_mutable_sites_yields_a_subset_not_a_panic() {
        // Only an incomplete-goal / malformed site is unavailable here.
        let neg = generate_mutations("rfl");
        // "rfl" has no dotted ident, number, rw, have, or `[` — incomplete-goal
        // removal would empty it, so no mutation applies. Must not panic.
        assert!(neg.is_empty() || neg.iter().all(|n| n.mutated_source != "rfl"));
    }
}
