//! Parsing helpers for PutnamBench's Lean 4 problem source files (issue #29).
//!
//! Shared by the `import_putnambench` example (batch registration into
//! `benchmark_problems`) and, eventually, the pass@k runner (issue #31),
//! which needs the same `has_solution_abbrev` classification to decide
//! whether a problem needs `SubmitModule` (the abbrev's real body plus the
//! theorem's proof) or a bare `Solve` (the theorem alone already type-checks
//! against something concrete).

#[derive(Debug)]
pub struct ParsedProblem {
    pub name: String,
    pub root_formal_statement: String,
    /// True if the file defines an `abbrev`/`noncomputable abbrev`/`def`
    /// (roughly half of PutnamBench's problems ask the prover to state an
    /// answer via a `_solution`-style declaration, not just supply a bare
    /// proof) before its `theorem` declaration. Those problems need
    /// `SubmitModule` — the abbrev's real body must be supplied alongside
    /// the theorem's proof — not a bare `Solve`, since the theorem
    /// statement's own dependency (the abbrev) is still an unresolved
    /// `sorry` on its own.
    pub has_solution_abbrev: bool,
}

/// Finds the start of a line-initial occurrence of `needle` (not merely a
/// substring match anywhere, e.g. inside a docstring sentence) within
/// `haystack`, searching from the start.
fn find_line_start(haystack: &str, needle: &str) -> Option<usize> {
    if haystack.starts_with(needle) {
        return Some(0);
    }
    let pat = format!("\n{}", needle);
    haystack.find(&pat).map(|i| i + 1)
}

/// Strips Lean line comments (`-- ...`) and block/doc comments (`/- ... -/`,
/// `/-- ... -/`) from `text`. Line-based, not a full Lean lexer — sufficient
/// for PutnamBench's own consistent style (no comment delimiters embedded
/// inside string literals in these files).
///
/// This exists for a real contamination reason, not just tidiness: roughly
/// half of PutnamBench's problems follow an `abbrev X_solution := sorry`
/// then `-- <the actual closed-form answer>` convention — the correct
/// answer, spelled out as a source comment, immediately after the
/// placeholder the prover is supposed to fill in. PutnamBench's own
/// extractor (`lean4/scripts/extract_to_json.py`) captures this comment
/// verbatim into `lean4_statement` since its regex has no notion of Lean
/// comment syntax. Registering that text unmodified into
/// `benchmark_problems.root_formal_statement` would hand any prover reading
/// it the answer key for free — the exact opposite of what a benchmark
/// import should do. Block/doc comments (the natural-language problem
/// description) are stripped too, so `root_formal_statement` stays purely
/// formal Lean declarations, matching its name.
fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut in_block_comment = false;
    for line in text.lines() {
        let trimmed = line.trim_start();
        if in_block_comment {
            if let Some(end) = trimmed.find("-/") {
                in_block_comment = false;
                let rest = trimmed[end + 2..].trim_start();
                if !rest.is_empty() && !rest.starts_with("--") {
                    out.push_str(rest);
                    out.push('\n');
                }
            }
            continue;
        }
        if trimmed.starts_with("--") {
            continue;
        }
        if let Some(block_start) = trimmed.find("/-") {
            if let Some(end) = trimmed[block_start + 2..].find("-/") {
                // Single-line block comment: keep whatever's before/after it.
                let before = trimmed[..block_start].trim_end();
                let after = trimmed[block_start + 2 + end + 2..].trim_start();
                if !before.is_empty() { out.push_str(before); out.push('\n'); }
                if !after.is_empty() && !after.starts_with("--") { out.push_str(after); out.push('\n'); }
            } else {
                in_block_comment = true;
                let before = trimmed[..block_start].trim_end();
                if !before.is_empty() { out.push_str(before); out.push('\n'); }
            }
            continue;
        }
        out.push_str(trimmed);
        out.push('\n');
    }
    out.trim_end().to_string()
}

/// Parses one PutnamBench `lean4/src/*.lean` file's text. Mirrors
/// PutnamBench's own `lean4/scripts/extract_to_json.py` regex
/// (`(abbrev...)*theorem NAME ... sorry`): every file is `import Mathlib`,
/// an optional `open ...` line, an optional docstring, an optional
/// `abbrev`/`noncomputable abbrev`/`def`/`noncomputable def` declaration,
/// and exactly one `theorem NAME ... := sorry` (confirmed against the full
/// 672-file corpus at commit a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39: zero
/// files have more than one `theorem` declaration, and only one file
/// — `putnam_1987_a1.lean` — has `sorry` inline on the theorem's own last
/// line rather than on its own line; both shapes are handled here since the
/// check is a trimmed suffix match, not a whole-line match).
pub fn parse_problem_file(text: &str) -> Result<ParsedProblem, String> {
    let theorem_start = find_line_start(text, "theorem ")
        .or_else(|| find_line_start(text, "noncomputable theorem "))
        .or_else(|| find_line_start(text, "protected theorem "))
        .ok_or_else(|| "no line-initial 'theorem ' declaration found".to_string())?;

    let after_kw = text[theorem_start..].splitn(2, "theorem ").nth(1)
        .ok_or_else(|| "malformed theorem line".to_string())?;
    // Split on any character that can't be part of a Lean identifier, not
    // just whitespace — a real file (putnam_1993_b5.lean) writes
    // "theorem putnam_1993_b5:" with no space before the colon, which a
    // bare `split_whitespace()` would include in the extracted name.
    let name = after_kw.trim_start()
        .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '{' || c == '[')
        .next()
        .filter(|s| !s.is_empty())
        .ok_or_else(|| "could not extract theorem name".to_string())?
        .to_string();

    let theorem_block = text[theorem_start..].trim_end();
    if !theorem_block.ends_with("sorry") {
        return Err(format!("theorem block for '{}' does not end in 'sorry' — not an unsolved PutnamBench placeholder", name));
    }

    let abbrev_start = find_line_start(&text[..theorem_start], "abbrev ")
        .or_else(|| find_line_start(&text[..theorem_start], "noncomputable abbrev "))
        .or_else(|| find_line_start(&text[..theorem_start], "def "))
        .or_else(|| find_line_start(&text[..theorem_start], "noncomputable def "));

    let raw = match abbrev_start {
        Some(a) => format!("{}\n{}", text[a..theorem_start].trim_end(), theorem_block),
        None => theorem_block.to_string(),
    };
    let root_formal_statement = strip_comments(&raw);

    Ok(ParsedProblem { name, root_formal_statement, has_solution_abbrev: abbrev_start.is_some() })
}

#[derive(Debug, PartialEq)]
pub struct AbbrevFields {
    pub name: String,
    pub type_signature: String,
}

#[derive(Debug, PartialEq)]
pub struct PiForm {
    /// A single, self-contained Lean type expression — suitable for
    /// `problem_create`'s `root_formal_statement` or `SubmitModule`'s
    /// `root_theorem.statement`, both of which splice this directly after a
    /// colon (`theorem X : {this} := ...`) with no external binders.
    pub root_theorem_statement: String,
    pub solution_abbrev: Option<AbbrevFields>,
}

/// Converts a `theorem NAME (a : A) (b : B) : C` signature (everything AFTER
/// "theorem NAME", i.e. starting at the first binder or the colon) into a
/// single self-contained type expression `∀ (a : A) (b : B), C` — Lean 4's
/// own desugaring of named-binder declaration syntax into a Pi type. Uses
/// bracket-depth tracking (not a naive first-colon split) since binders
/// themselves contain colons (`(S : Set (ℝ × ℝ))`) and can nest brackets
/// arbitrarily deep.
pub fn binders_to_pi_type(signature: &str) -> Result<String, String> {
    let mut depth: i32 = 0;
    let mut split_at: Option<usize> = None;
    for (idx, ch) in signature.char_indices() {
        match ch {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => depth -= 1,
            ':' if depth == 0 && !signature[idx + 1..].starts_with('=') => {
                split_at = Some(idx);
                break;
            }
            _ => {}
        }
    }
    let split_at = split_at.ok_or_else(|| "no top-level ':' found separating binders from return type".to_string())?;
    let binders = signature[..split_at].trim();
    let return_type = signature[split_at + 1..].trim();
    if binders.is_empty() {
        Ok(return_type.to_string())
    } else {
        Ok(format!("∀ {}, {}", binders, return_type))
    }
}

fn parse_abbrev_fields(abbrev_text: &str) -> Result<AbbrevFields, String> {
    let rest = abbrev_text.trim_start().trim_start_matches("noncomputable ").trim_start();
    let rest = rest.strip_prefix("abbrev ").or_else(|| rest.strip_prefix("def "))
        .ok_or_else(|| format!("expected an 'abbrev'/'def' declaration, got: {:?}", abbrev_text))?;
    let colon_idx = rest.find(':').ok_or_else(|| format!("no ':' found in abbrev declaration: {:?}", abbrev_text))?;
    let name = rest[..colon_idx].trim().to_string();
    let after_colon = &rest[colon_idx + 1..];
    let assign_idx = after_colon.find(":=").ok_or_else(|| format!("no ':=' found in abbrev declaration: {:?}", abbrev_text))?;
    let type_signature = after_colon[..assign_idx].trim().to_string();
    Ok(AbbrevFields { name, type_signature })
}

/// Converts a `benchmark_problems.root_formal_statement` (the abbrev-if-
/// present-plus-theorem text `parse_problem_file` registers, already comment-
/// stripped) into the `PiForm` a runner needs to actually construct a
/// `problem_create`/`SubmitModule` call: a bare Pi-type for the theorem
/// (never the named-binder declaration syntax ChatDB's model can't accept as
/// a single type expression), plus the solution abbrev's name/type if one
/// is present.
pub fn to_pi_form(root_formal_statement: &str, theorem_name: &str) -> Result<PiForm, String> {
    let marker = format!("theorem {}", theorem_name);
    let theorem_idx = root_formal_statement.find(&marker)
        .ok_or_else(|| format!("could not find {:?} in root_formal_statement", marker))?;
    let abbrev_part = root_formal_statement[..theorem_idx].trim();
    let theorem_part = &root_formal_statement[theorem_idx + marker.len()..];

    let sig_end = theorem_part.rfind(":=")
        .ok_or_else(|| "no ':=' found in theorem block".to_string())?;
    let signature = theorem_part[..sig_end].trim();
    let root_theorem_statement = binders_to_pi_type(signature)?;

    let solution_abbrev = if abbrev_part.is_empty() {
        None
    } else {
        Some(parse_abbrev_fields(abbrev_part)?)
    };

    Ok(PiForm { root_theorem_statement, solution_abbrev })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parses_plain_proof_problem_no_abbrev() {
        // Real shape of putnam_1962_a1.lean.
        let text = "import Mathlib\n\nopen MeasureTheory\n\n/--\nGiven five points...\n-/\ntheorem putnam_1962_a1\n(S : Set (ℝ × ℝ))\n: True :=\nsorry\n";
        let p = parse_problem_file(text).unwrap();
        assert_eq!(p.name, "putnam_1962_a1");
        assert!(!p.has_solution_abbrev);
        assert!(p.root_formal_statement.starts_with("theorem putnam_1962_a1"));
        assert!(p.root_formal_statement.ends_with("sorry"));
        assert!(!p.root_formal_statement.contains("import Mathlib"), "docstring/import preamble must not leak into the statement");
    }

    #[test]
    fn test_extracts_name_correctly_when_no_space_before_colon() {
        // Real, verbatim shape of putnam_1993_b5.lean — no space between the
        // theorem name and the following colon. A naive split_whitespace()
        // would extract "putnam_1993_b5:" (colon included), silently
        // corrupting theorem_name (the importer separately registers the
        // file stem as upstream_problem_id, so this diverges from it).
        let text = "import Mathlib\n\ntheorem putnam_1993_b5:\n∀ n : ℕ, n = n :=\nsorry\n";
        let p = parse_problem_file(text).unwrap();
        assert_eq!(p.name, "putnam_1993_b5");
    }

    #[test]
    fn test_parses_solution_abbrev_problem() {
        // Real shape of putnam_1962_a5.lean.
        let text = "import Mathlib\n\nabbrev putnam_1962_a5_solution : ℕ → ℕ := sorry\n-- fun n : ℕ => n * (n + 1) * 2^(n - 2)\n/--\nEvaluate in closed form.\n-/\ntheorem putnam_1962_a5\n: ∀ n ≥ 2, putnam_1962_a5_solution n = 0 :=\nsorry\n";
        let p = parse_problem_file(text).unwrap();
        assert_eq!(p.name, "putnam_1962_a5");
        assert!(p.has_solution_abbrev);
        assert!(p.root_formal_statement.starts_with("abbrev putnam_1962_a5_solution"));
        assert!(p.root_formal_statement.contains("theorem putnam_1962_a5"));
    }

    #[test]
    fn test_strips_answer_key_comment_and_docstring_from_solution_abbrev_problems() {
        // Real, security-relevant behavior: PutnamBench's own convention for
        // roughly half its problems is `abbrev X_solution := sorry` followed
        // immediately by `-- <the actual closed-form answer>` as a source
        // comment — PutnamBench's own extract_to_json.py captures this
        // verbatim. If ChatDB's importer did the same, it would hand any
        // prover reading `root_formal_statement` the answer key for free.
        // Both the spoiler comment and the natural-language docstring must
        // be stripped, leaving only the formal abbrev + theorem signatures.
        let text = "import Mathlib\n\nabbrev putnam_1962_a5_solution : ℕ → ℕ := sorry\n-- fun n : ℕ => n * (n + 1) * 2^(n - 2)\n/--\nEvaluate in closed form \\[ \\sum_{k=1}^n {n \\choose k} k^2. \\]\n-/\ntheorem putnam_1962_a5\n: ∀ n ≥ 2, putnam_1962_a5_solution n = ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k^2 :=\nsorry\n";
        let p = parse_problem_file(text).unwrap();
        assert!(!p.root_formal_statement.contains("n * (n + 1) * 2^(n - 2)"), "the answer-key comment must never appear in the registered statement: {}", p.root_formal_statement);
        assert!(!p.root_formal_statement.contains("Evaluate in closed form"), "the natural-language docstring must not leak into the formal statement: {}", p.root_formal_statement);
        assert!(p.root_formal_statement.contains("abbrev putnam_1962_a5_solution : ℕ → ℕ := sorry"));
        assert!(p.root_formal_statement.contains("theorem putnam_1962_a5"));
    }

    #[test]
    fn test_handles_sorry_inline_on_theorem_last_line() {
        // Real edge case: putnam_1987_a1.lean has ":= sorry" on the same
        // line as the statement, not "sorry" on its own trailing line.
        let text = "import Mathlib\n\ntheorem putnam_1987_a1\n(A B C D : Set ℕ)\n: A ∩ B = C ∩ D := sorry";
        let p = parse_problem_file(text).unwrap();
        assert_eq!(p.name, "putnam_1987_a1");
        assert!(p.root_formal_statement.ends_with(":= sorry"));
    }

    #[test]
    fn test_rejects_file_without_theorem() {
        let text = "import Mathlib\n\ndef helper : ℕ := 0\n";
        assert!(parse_problem_file(text).is_err());
    }

    #[test]
    fn test_rejects_already_solved_file_not_ending_in_sorry() {
        // A file whose sorry has already been replaced with a real proof is
        // not something this importer should register as an open benchmark
        // problem (registering it would silently treat a solved proof as
        // unsolved, or worse, embed a real proof body as if it were a bare
        // statement).
        let text = "import Mathlib\n\ntheorem putnam_done\n: True :=\nby trivial\n";
        let err = parse_problem_file(text).unwrap_err();
        assert!(err.contains("sorry"));
    }

    #[test]
    fn test_docstring_mentioning_theorem_keyword_does_not_confuse_the_parser() {
        // A docstring sentence containing the literal word "theorem" must
        // not be mistaken for a line-initial 'theorem ' declaration.
        let text = "import Mathlib\n\n/--\nProve this theorem is true.\n-/\ntheorem putnam_x\n: True :=\nsorry\n";
        let p = parse_problem_file(text).unwrap();
        assert_eq!(p.name, "putnam_x");
    }

    #[test]
    fn test_binders_to_pi_type_no_binders() {
        assert_eq!(binders_to_pi_type(": True").unwrap(), "True");
    }

    #[test]
    fn test_binders_to_pi_type_simple_binders() {
        // Real shape of putnam_1962_a1's signature (name already stripped).
        let sig = "\n(S : Set (ℝ × ℝ))\n(hS : S.ncard = 5)\n(hnoncol : ∀ s ⊆ S, s.ncard = 3 → ¬Collinear ℝ s)\n: ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \\ {t})";
        let pi = binders_to_pi_type(sig).unwrap();
        assert!(pi.starts_with("∀ (S : Set (ℝ × ℝ))"), "{}", pi);
        assert!(pi.contains(", ∃ T ⊆ S"), "the return type must follow a comma after all binders: {}", pi);
        // A colon nested inside a binder's own type (e.g. "Set (ℝ × ℝ)" has no
        // colon, but "hS : S.ncard = 5" and "hnoncol : ..." each have their
        // own colon) must never be mistaken for the top-level separator.
        assert!(!pi.contains(", ∀ s ⊆ S"), "must not split at a colon nested inside a later binder: {}", pi);
    }

    #[test]
    fn test_binders_to_pi_type_deeply_nested_binder_types() {
        // Real shape of putnam_1963_a3's signature — binder types are
        // themselves multi-argument function types with their own nested
        // parens, and the LAST binder's type contains a colon-free arrow
        // chain right before the top-level separator.
        let sig = "\n    (P : ℕ → (ℝ → ℝ) → (ℝ → ℝ))\n    (hP : P 0 = id ∧ ∀ i y, P (i + 1) y = P i (fun x ↦ x * deriv y x - i * y x))\n    (n : ℕ)\n    (hn : 0 < n)\n    (f y : ℝ → ℝ)\n    (hf : ContinuousOn f (Ici 1))\n    (hy : ContDiffOn ℝ n y (Ici 1))\n    (hy1 : ContDiffAt ℝ n y 1) :\n    (∀ i < n, deriv^[i] y 1 = 0) ∧ (Ici 1).EqOn (P n y) f ↔\n    ∀ x ≥ 1, y x = ∫ t in (1 : ℝ)..x, putnam_1963_a3_solution f n x t";
        let pi = binders_to_pi_type(sig).unwrap();
        assert!(pi.starts_with("∀ (P : ℕ → (ℝ → ℝ) → (ℝ → ℝ))"), "{}", pi);
        assert!(pi.contains("(hy1 : ContDiffAt ℝ n y 1)"), "the last binder must be included: {}", pi);
        assert!(pi.trim_end().ends_with("putnam_1963_a3_solution f n x t"), "the return type must be preserved intact: {}", pi);
    }

    #[test]
    fn test_to_pi_form_plain_proof_problem() {
        let root_formal_statement = "theorem putnam_1962_a1\n(S : Set (ℝ × ℝ))\n(hS : S.ncard = 5)\n: ∃ T ⊆ S, T.ncard = 4 :=\nsorry";
        let form = to_pi_form(root_formal_statement, "putnam_1962_a1").unwrap();
        assert!(form.solution_abbrev.is_none());
        assert!(form.root_theorem_statement.starts_with("∀ (S : Set (ℝ × ℝ))"), "{}", form.root_theorem_statement);
        assert!(form.root_theorem_statement.contains("(hS : S.ncard = 5)"), "{}", form.root_theorem_statement);
        assert!(form.root_theorem_statement.ends_with("∃ T ⊆ S, T.ncard = 4"), "{}", form.root_theorem_statement);
        assert!(!form.root_theorem_statement.contains("sorry"), "the proof placeholder must not leak into the statement: {}", form.root_theorem_statement);
    }

    #[test]
    fn test_to_pi_form_solution_abbrev_problem() {
        let root_formal_statement = "abbrev putnam_1962_a5_solution : ℕ → ℕ := sorry\ntheorem putnam_1962_a5\n: ∀ n ≥ 2, putnam_1962_a5_solution n = 0 :=\nsorry";
        let form = to_pi_form(root_formal_statement, "putnam_1962_a5").unwrap();
        let abbrev = form.solution_abbrev.unwrap();
        assert_eq!(abbrev.name, "putnam_1962_a5_solution");
        assert_eq!(abbrev.type_signature, "ℕ → ℕ");
        assert_eq!(form.root_theorem_statement, "∀ n ≥ 2, putnam_1962_a5_solution n = 0");
    }

    #[test]
    fn test_to_pi_form_noncomputable_abbrev() {
        let root_formal_statement = "noncomputable abbrev putnam_1963_a3_solution : (ℝ → ℝ) → ℕ → ℝ → ℝ → ℝ := sorry\ntheorem putnam_1963_a3\n(n : ℕ)\n: True :=\nsorry";
        let form = to_pi_form(root_formal_statement, "putnam_1963_a3").unwrap();
        let abbrev = form.solution_abbrev.unwrap();
        assert_eq!(abbrev.name, "putnam_1963_a3_solution");
        assert_eq!(abbrev.type_signature, "(ℝ → ℝ) → ℕ → ℝ → ℝ → ℝ");
    }
}
